import LeanCloud.Proofs.BackendMap
import LeanCloud.Proofs.CompletionCode

/-! The interpreter's loads and saves commute with backend
maps. This transfers their crash proofs without replacing their implementation. -/

namespace LeanCloud.Proofs.BackendMap
open Lean ReplayInterpreter.Internal ReplayRecovery
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

omit [LawfulMonad m] [LawfulMonad n] in
theorem decode_map (f : BackendMap m n) (codec : Codec α) (value : Json) :
    (f.except CloudError).map (decode codec value) = decode codec value := by
  unfold decode
  cases codec.decode value with
  | ok decoded => exact (f.except CloudError).map_pure _
  | error error => exact f.map_throw _

theorem decodeGroup_map (f : BackendMap m n) (codec : Codec α) (count : Nat) (value : Json) :
    (f.except CloudError).map (decodeGroup codec count value) = decodeGroup codec count value := by
  unfold decodeGroup
  rw [(f.except CloudError).map_bind, decode_map]
  congr 1
  funext values
  by_cases different : (values.size != count) = true <;>
    simp only [different, Bool.false_eq_true, ↓reduceIte, ExceptT.bind_throw,
      f.map_throw, (f.except CloudError).map_pure]

end LeanCloud.Proofs.BackendMap

namespace LeanCloud.Proofs.DbMap
open Lean ReplayInterpreter.Internal ReplayRecovery
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
variable {backend : Db σ m} {mapped : Db τ n}

theorem load_map (f : DbMap backend mapped) (location : Location) :
    f.worker.map (load backend location) = load mapped location := by
  unfold load
  rw [f.worker.map_bind, f.actions.map_lift, f.get]
  congr 1
  funext stored
  cases stored with
  | none => exact f.worker.map_pure _
  | some value =>
    simp only []
    cases fromJson? (α := Result) value with
    | ok result => exact f.worker.map_pure _
    | error message => exact f.actions.map_throw _

theorem save_map (f : DbMap backend mapped) (location : Location) (record : Result) :
    f.worker.map (save backend location record) = save mapped location record := by
  unfold save
  rw [f.worker.map_bind, f.actions.map_lift, f.put]
  congr 1
  funext accepted
  cases accepted with
  | false => exact f.actions.map_throw _
  | true => exact f.worker.map_pure _

private theorem readParent_map (f : DbMap backend mapped) (parent : Location) :
    f.worker.map (readParent backend parent) = readParent mapped parent := by
  unfold readParent
  rw [f.worker.map_bind, load_map]
  congr 1
  funext latest
  cases latest with
  | none => exact f.actions.map_throw _
  | some latest => cases latest <;> exact f.worker.map_pure _

private theorem publishParent_map (f : DbMap backend mapped)
    (parent : Location) (slots : Array (Option Exit)) (updated : Result) :
    f.worker.map (publishParent backend parent slots updated) =
      publishParent mapped parent slots updated := by
  cases updated <;>
    simp only [publishParent, f.worker.map_bind, save_map, readParent_map]

private theorem notifyParent_map (f : DbMap backend mapped)
    (parent : Location) (index : Nat) (outcome : Exit) :
    f.worker.map (notifyParent backend parent index outcome) =
      notifyParent mapped parent index outcome := by
  unfold notifyParent
  rw [f.worker.map_bind, load_map]
  congr 1
  funext group
  cases group with
  | none => exact f.actions.map_throw _
  | some group =>
    cases group with
    | completed _ => exact f.worker.map_pure _
    | suspended children =>
      cases recorded : Result.recordChild (.suspended children) index outcome <;>
        simp only [recorded, pure_bind, ExceptT.bind_throw, f.actions.map_throw, publishParent_map]

private theorem recordResult_map (f : DbMap backend mapped) (location : Location) (outcome : Exit) :
    f.worker.map (recordResult backend location outcome) = recordResult mapped location outcome := by
  unfold recordResult
  rw [f.worker.map_bind, load_map]
  congr 1
  funext record
  cases record with
  | none => exact save_map f location (.completed outcome)
  | some record =>
    cases record with
    | suspended _ => exact f.actions.map_throw _
    | completed recorded =>
      by_cases changed : (recorded != outcome) = true <;>
        simp only [changed, Bool.false_eq_true, ↓reduceIte, f.actions.map_throw, f.worker.map_pure]

theorem finish_map (f : DbMap backend mapped) (location : Location) (outcome : Exit) :
    f.worker.map (finish backend location outcome) = finish mapped location outcome := by
  simp only [finish_eq, f.worker.map_bind, recordResult_map]
  congr 1
  funext _
  cases location.parent? with
  | none => exact f.worker.map_pure _
  | some pair => exact notifyParent_map f pair.1 pair.2 outcome

end LeanCloud.Proofs.DbMap
