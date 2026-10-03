import LeanCloud.Proofs.SimulationComposition
import LeanCloud.Proofs.PureBind
import LeanCloud.Proofs.PureContinuation
import LeanCloud.Proofs.CompletionCode

/-! One structural argument for properties of replay actions. Instantiations
relate the leased backend or restrict the primitive operations a step can use.
No interpreter implementation or monad-law instance is introduced. -/

namespace LeanCloud.Proofs
open Lean LeanEff Simulation

universe u
variable {m : Type → Type u} [Monad m] [PureBindLaw m]

private abbrev Action (σ : Type) (m : Type → Type u) [Monad m] (α : Type) := ExceptT CloudError (StateT σ m) α

structure ReplayRelation (db : Db σ m) (mapped : Db τ m) where
  relates : {α : Type} → Action σ m α → Action τ m α → Prop
  pure : ∀ {α} (value : α), relates (Pure.pure value) (Pure.pure value)
  throw : ∀ {α} (error : CloudError), relates (throw error : Action σ m α) (throw error)
  bind : ∀ {α β} {first : Action σ m α} {second : Action τ m α}, relates first second →
    ∀ {left : α → Action σ m β} {right : α → Action τ m β},
      (∀ value, relates (left value) (right value)) → relates (first >>= left) (second >>= right)
  get : ∀ key, relates (liftM (db.get key)) (liftM (mapped.get key))
  put : ∀ key value, relates (liftM (db.put key value)) (liftM (mapped.put key value))

namespace ReplayRelation
open ReplayInterpreter.Internal ReplayRecovery

private theorem pure_bind (value : α) (next : α → Action σ m β) :
    (Pure.pure value >>= next) = next value := PureBindLaw.pure_bind value next

private theorem throw_bind (error : CloudError) (next : α → Action σ m β) :
    ((MonadExcept.throw error : Action σ m α) >>= next) = MonadExcept.throw error := by
  change (Pure.pure (Except.error error) >>= ExceptT.bindCont next) = _
  rw [PureBindLaw.pure_bind]
  rfl


omit [PureBindLaw m] in
theorem load {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (location : Location) :
    relation.relates (ReplayInterpreter.Internal.load db location)
      (ReplayInterpreter.Internal.load mapped location) := by
  unfold ReplayInterpreter.Internal.load
  apply relation.bind (relation.get location.key)
  intro stored
  cases stored with
  | none => exact relation.pure _
  | some value =>
    simp only []
    cases fromJson? (α := Result) value with
    | ok result => exact relation.pure _
    | error message => simpa only [throw_bind] using relation.throw _

omit [PureBindLaw m] in
theorem save {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (location : Location) (record : Result) :
    relation.relates (ReplayInterpreter.Internal.save db location record)
      (ReplayInterpreter.Internal.save mapped location record) := by
  unfold ReplayInterpreter.Internal.save
  apply relation.bind (relation.put location.key (toJson record))
  intro accepted
  cases accepted with
  | false => simpa using relation.throw _
  | true => exact relation.pure _

omit [PureBindLaw m] in
private theorem decode {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (codec : Codec α) (value : Json) :
    relation.relates (ReplayInterpreter.Internal.decode (m := StateT σ m) codec value)
      (ReplayInterpreter.Internal.decode (m := StateT τ m) codec value) := by
  unfold ReplayInterpreter.Internal.decode
  cases codec.decode value with
  | ok value => exact relation.pure _
  | error error => simpa only [throw_bind] using relation.throw _

private theorem decodeGroup {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (codec : Codec α) (count : Nat) (value : Json) :
    relation.relates (ReplayInterpreter.Internal.decodeGroup (m := StateT σ m) codec count value)
      (ReplayInterpreter.Internal.decodeGroup (m := StateT τ m) codec count value) := by
  unfold ReplayInterpreter.Internal.decodeGroup
  apply relation.bind (decode relation _ _)
  intro values
  by_cases different : (values.size != count) = true <;>
    simp only [different, Bool.false_eq_true, ↓reduceIte]
  · simpa only [throw_bind] using relation.throw _
  · exact relation.pure _

omit [PureBindLaw m] in
private theorem readParent {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (parent : Location) :
    relation.relates (ReplayRecovery.readParent db parent)
      (ReplayRecovery.readParent mapped parent) := by
  unfold ReplayRecovery.readParent
  apply relation.bind (load relation parent)
  intro latest
  cases latest with
  | none => simpa only [throw_bind] using relation.throw _
  | some result => exact relation.pure _

omit [PureBindLaw m] in
private theorem publishParent {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (parent : Location)
    (slots : Array (Option Exit)) (updated : Result) :
    relation.relates (ReplayRecovery.publishParent db parent slots updated)
      (ReplayRecovery.publishParent mapped parent slots updated) := by
  unfold ReplayRecovery.publishParent
  apply relation.bind (save relation parent (.suspended slots))
  intro _
  cases updated with
  | suspended _ => exact readParent relation parent
  | completed result =>
    exact relation.bind (save relation parent (.completed result)) (fun _ => readParent relation parent)

private theorem notifyParent {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (parent : Location) (index : Nat) (outcome : Exit) :
    relation.relates (ReplayRecovery.notifyParent db parent index outcome)
      (ReplayRecovery.notifyParent mapped parent index outcome) := by
  unfold ReplayRecovery.notifyParent
  apply relation.bind (load relation parent)
  intro group
  cases group with
  | none => simpa only [throw_bind] using relation.throw _
  | some record =>
    cases record with
    | completed _ => exact relation.pure _
    | suspended slots =>
      cases recorded : Result.recordChild (.suspended slots) index outcome with
      | error error => simp only [recorded]; simpa only [throw_bind] using relation.throw _
      | ok updated =>
        simp only [recorded, pure_bind]
        exact publishParent relation parent _ updated

theorem finish {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (location : Location) (outcome : Exit) :
    relation.relates (ReplayInterpreter.Internal.finish db location outcome)
      (ReplayInterpreter.Internal.finish mapped location outcome) := by
  have rest : relation.relates
      (match location.parent? with
      | none => Pure.pure (.done outcome)
      | some (parent, index) => ReplayRecovery.notifyParent db parent index outcome)
      (match location.parent? with
      | none => Pure.pure (.done outcome)
      | some (parent, index) => ReplayRecovery.notifyParent mapped parent index outcome) := by
    cases location.parent? with
    | none => exact relation.pure _
    | some pair => exact notifyParent relation pair.1 pair.2 outcome
  unfold ReplayRecovery.notifyParent ReplayRecovery.publishParent ReplayRecovery.readParent at rest
  unfold ReplayInterpreter.Internal.finish
  apply relation.bind (load relation location)
  intro existing
  cases existing with
  | none => exact relation.bind (save relation location (.completed outcome)) (fun _ => rest)
  | some record =>
    cases record with
    | suspended _ => simpa only [throw_bind] using relation.throw _
    | completed actual =>
      by_cases changed : (actual != outcome) = true <;>
        simp only [changed, Bool.false_eq_true, ↓reduceIte]
      · simpa only [throw_bind] using relation.throw _
      · exact rest

/-- Reconstruction uses the same Cloud continuations, primitive requests and
replies under the supplied relation on backend actions. -/
theorem walk_add {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (blobs : BlobStorage σ m)
    (leasedBlobs : BlobStorage τ m) (fuel extra : Nat)
    (exhausted : ∀ program current target,
      relation.relates (ReplayInterpreter.Internal.walk db blobs 0 program current target)
        (ReplayInterpreter.Internal.walk mapped leasedBlobs extra program current target))
    (program : Cloud m Json) (supported : PureProgram program) (current target : Location) :
    relation.relates (ReplayInterpreter.Internal.walk db blobs fuel program current target)
      (ReplayInterpreter.Internal.walk mapped leasedBlobs (fuel + extra) program current target) := by
  induction fuel generalizing program current with
  | zero => simpa only [Nat.zero_add] using exhausted program current target
  | succ fuel ih =>
    simp only [Nat.succ_add]
    cases program with
    | pure value =>
      simp only [ReplayInterpreter.Internal.walk]
      by_cases same : (current == target) = true <;>
        simp only [same, Bool.false_eq_true, ↓reduceIte]
      · exact finish relation current _
      · simpa only [throw_bind] using relation.throw _
    | impure request rest =>
      cases request with
      | sequential codec operation => exact False.elim supported.1
      | choice codec count branches => exact False.elim supported.1
      | delay => exact ih (ArrsF.apply rest ()) (supported.2.apply ()) current
      | fail error =>
        simp only [ReplayInterpreter.Internal.walk]
        by_cases same : (current == target) = true <;>
          simp only [same, Bool.false_eq_true, ↓reduceIte]
        · exact finish relation current _
        · simpa only [throw_bind] using relation.throw _
      | parallel codec count branches =>
        simp only [ReplayInterpreter.Internal.walk]
        apply relation.bind (load relation current)
        intro existing
        by_cases fresh : ((current == target) && existing.isNone) = true
        · simp only [fresh, ↓reduceIte]
          exact relation.bind (save relation current _) (fun _ => relation.pure _)
        · simp only [fresh, Bool.false_eq_true, ↓reduceIte]
          cases existing with
          | none => simpa only [throw_bind] using relation.throw _
          | some record =>
            cases record with
            | completed outcome =>
              cases outcome with
              | success value =>
                apply relation.bind (decodeGroup relation codec count value)
                intro values
                by_cases same : (current == target) = true
                · simp only [same, ↓reduceIte]; exact relation.pure _
                · simp only [same, Bool.false_eq_true, ↓reduceIte]
                  by_cases obsolete : current.entersChild target = true
                  · simp only [obsolete, ↓reduceIte]; exact relation.pure _
                  · simp only [obsolete, Bool.false_eq_true, ↓reduceIte]
                    exact ih (ArrsF.apply rest values) (supported.2.apply values) current.next
              | failure error | cancelled error =>
                by_cases same : (current == target) = true <;>
                  by_cases obsolete : current.entersChild target = true <;>
                  simp only [same, obsolete, Bool.false_eq_true, ↓reduceIte]
                all_goals first | exact finish relation current _ | simpa only [throw_bind] using relation.throw _ | exact relation.pure _
            | suspended children =>
              by_cases different : (children.size != count) = true
              · simp only [different, ↓reduceIte]; simpa only [throw_bind] using relation.throw _
              · simp only [different, Bool.false_eq_true, ↓reduceIte]
                by_cases same : (current == target) = true
                · simp only [same, ↓reduceIte]; exact relation.pure _
                · simp only [same, Bool.false_eq_true, ↓reduceIte]
                  by_cases outside : (!current.entersChild target) = true
                  · simp only [outside, ↓reduceIte]; simpa only [throw_bind] using relation.throw _
                  · simp only [outside, Bool.false_eq_true, ↓reduceIte]
                    by_cases inside : target[current.size]!.1 < count
                    · simp only [inside, ↓reduceDIte]
                      exact ih (codec.encode <$> branches ⟨_, inside⟩)
                        ((supported.1.2 ⟨_, inside⟩).map codec.encode) (current.child target[current.size]!.1)
                    · simp only [inside, ↓reduceDIte]; simpa only [throw_bind] using relation.throw _

theorem step_add {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped) (blobs : BlobStorage σ m)
    (leasedBlobs : BlobStorage τ m) (fuel extra : Nat)
    (exhausted : ∀ program current target,
      relation.relates (ReplayInterpreter.Internal.walk db blobs 0 program current target)
        (ReplayInterpreter.Internal.walk mapped leasedBlobs extra program current target))
    (program : Cloud m Json) (supported : PureProgram program) (location : Location) :
    relation.relates (ReplayInterpreter.Internal.step db blobs fuel program location)
      (ReplayInterpreter.Internal.step mapped leasedBlobs (fuel + extra) program location) := by
  unfold ReplayInterpreter.Internal.step
  by_cases invalid : (location.isEmpty || location[0]!.1 != 0) = true
  · simp only [invalid, ↓reduceIte]; simpa only [throw_bind] using relation.throw _
  · simp only [invalid, Bool.false_eq_true, ↓reduceIte]
    cases location.parent? with
    | none => exact walk_add relation blobs leasedBlobs fuel extra exhausted program supported _ _
    | some pair =>
      obtain ⟨parent, index⟩ := pair
      apply relation.bind (load relation parent)
      intro result
      cases result with
      | none => exact walk_add relation blobs leasedBlobs fuel extra exhausted program supported _ _
      | some record =>
        cases record with
        | completed _ => exact relation.pure _
        | suspended _ => exact walk_add relation blobs leasedBlobs fuel extra exhausted program supported _ _

theorem step {db : Db σ m} {mapped : Db τ m} (relation : ReplayRelation db mapped)
    (blobs : BlobStorage σ m) (leasedBlobs : BlobStorage τ m) (fuel : Nat)
    (program : Cloud m Json) (supported : PureProgram program) (location : Location) :
    relation.relates (ReplayInterpreter.Internal.step db blobs fuel program location)
      (ReplayInterpreter.Internal.step mapped leasedBlobs fuel program location) := by
  simpa using relation.step_add blobs leasedBlobs fuel 0 (fun _ _ _ => relation.throw _) program supported location

end ReplayRelation
end LeanCloud.Proofs
