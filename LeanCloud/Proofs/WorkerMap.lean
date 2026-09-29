import LeanCloud.Proofs.ProgramMap
import LeanCloud.Proofs.InterpreterMap

/-! Backend naturality of the actual fuel-based replay worker on pure programs.
This covers errors and malformed views as well as successful reconstruction. -/

namespace LeanCloud.Proofs.DbMap
open Lean LeanEff ReplayInterpreter.Internal BackendMap
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

theorem walk_map (mapper : BackendMap m n) {backend : Db σ m} {mapped : Db τ n} (f : DbMap backend mapped)
    (blobs : BlobStorage σ m) (mappedBlobs : BlobStorage τ n) (fuel : Nat)
    (source : Cloud m Json) (supported : PureProgram source) (current target : Location) :
    f.worker.map (walk backend blobs fuel source current target) =
      walk mapped mappedBlobs fuel (mapper.program source) current target := by
  induction fuel generalizing source current with
  | zero => exact f.actions.map_throw _
  | succ fuel ih =>
    cases source with
    | pure value =>
      simp only [walk, program]
      by_cases same : (current == target) = true <;>
        simp only [same, Bool.false_eq_true, ↓reduceIte, finish_map, f.actions.map_throw]
    | impure request rest =>
      cases request with
      | sequential codec operation => exact False.elim supported.1
      | choice codec count branches => exact False.elim supported.1
      | delay =>
        simpa only [walk, program, BackendMap.control, continuation_apply] using
          ih (ArrsF.apply rest ()) (supported.2.apply ()) current
      | fail error =>
        simp only [walk, program, BackendMap.control]
        by_cases same : (current == target) = true <;>
          simp only [same, Bool.false_eq_true, ↓reduceIte, finish_map, f.actions.map_throw]
      | parallel codec count branches =>
        simp only [walk, program, BackendMap.control]
        rw [f.worker.map_bind, load_map]
        congr 1
        funext existing
        by_cases fresh : ((current == target) && existing.isNone) = true
        · simp only [fresh, ↓reduceIte, f.worker.map_bind, save_map, f.worker.map_pure]
        · simp only [fresh, Bool.false_eq_true, ↓reduceIte]
          cases existing with
          | none => exact f.actions.map_throw _
          | some record =>
            cases record with
            | completed outcome =>
              cases outcome with
              | success value =>
                rw [f.worker.map_bind, f.actions.decodeGroup_map]
                congr 1
                funext values
                by_cases same : (current == target) = true
                · simp only [same, ↓reduceIte, f.worker.map_pure]
                · simp only [same, Bool.false_eq_true, ↓reduceIte]
                  simpa only [continuation_apply] using
                    ih (ArrsF.apply rest values) (supported.2.apply values) current.next
              | failure error | cancelled error =>
                by_cases same : (current == target) = true <;>
                  simp only [same, Bool.false_eq_true, ↓reduceIte, finish_map, f.actions.map_throw]
            | suspended children =>
              by_cases different : (children.size != count) = true
              · simp only [different, ↓reduceIte, ExceptT.bind_throw, f.actions.map_throw]
              · simp only [different, Bool.false_eq_true, ↓reduceIte]
                by_cases same : (current == target) = true
                · simp only [same, ↓reduceIte, f.worker.map_pure]
                · simp only [same, Bool.false_eq_true, ↓reduceIte]
                  by_cases outside : (!current.entersChild target) = true
                  · simp only [outside, ↓reduceIte, ExceptT.bind_throw, f.actions.map_throw]
                  · simp only [outside, Bool.false_eq_true, ↓reduceIte]
                    by_cases inside : target[current.size]!.1 < count
                    · simp only [inside, ↓reduceDIte]
                      simpa only [program_map] using
                        ih (codec.encode <$> branches ⟨_, inside⟩)
                          ((supported.1.2 ⟨_, inside⟩).map codec.encode) (current.child target[current.size]!.1)
                    · simp only [inside, ↓reduceDIte, f.actions.map_throw]

theorem step_map (mapper : BackendMap m n) {backend : Db σ m} {mapped : Db τ n} (f : DbMap backend mapped)
    (blobs : BlobStorage σ m) (mappedBlobs : BlobStorage τ n) (fuel : Nat)
    (source : Cloud m Json) (supported : PureProgram source) (location : Location) :
    f.worker.map (step backend blobs fuel source location) =
      step mapped mappedBlobs fuel (mapper.program source) location := by
  unfold step
  by_cases invalid : (location.isEmpty || location[0]!.1 != 0) = true
  · simp only [invalid, ↓reduceIte, ExceptT.bind_throw, f.actions.map_throw]
  · simp only [invalid, Bool.false_eq_true, ↓reduceIte]
    cases location.parent? with
    | none => exact walk_map mapper f blobs mappedBlobs fuel source supported _ _
    | some parent =>
      obtain ⟨parent, index⟩ := parent
      rw [f.worker.map_bind, load_map]
      congr 1
      funext record
      cases record with
      | none => exact walk_map mapper f blobs mappedBlobs fuel source supported _ _
      | some record =>
        cases record with
        | completed _ => exact f.worker.map_pure _
        | suspended _ => exact walk_map mapper f blobs mappedBlobs fuel source supported _ _

end LeanCloud.Proofs.DbMap
