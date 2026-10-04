import LeanCloud.Proofs.CloudEffects
import LeanCloud.ReplayInterpreter

/-! Structural effect checks shared by interpreter proofs. These contracts are
about the existing ports and interpreter; they introduce no runtime evaluator. -/

namespace LeanCloud.Proofs.InterpreterEffects
open Lean LeanEff ReplayInterpreter Internal

universe u
variable {e : Type → Type u}

structure Ports (allowed : {β : Type} → e β → Prop)
    (store : ReplayStore (EffF e Empty)) (blobs : BlobStorage (EffF e Empty)) : Prop where
  read : ∀ key, Effects.Program allowed (store.read key)
  create : ∀ key record, Effects.Program allowed (store.create key record)
  execute : ∀ {β : Type} (codec : Codec β) (operation : Operation (EffF e Empty) β),
    CloudEffects.Request (fun action => Effects.Program allowed action) (.command codec operation) →
      Effects.Program allowed (blobs.execute operation).run

variable {allowed : {β : Type} → e β → Prop}
  {store : ReplayStore (EffF e Empty)} {blobs : BlobStorage (EffF e Empty)}

private theorem decode (codec : Codec α) (value : Json) :
    Effects.Program allowed (Internal.decode (m := EffF e Empty) codec value).run := by
  unfold Internal.decode
  split <;> trivial

private theorem decodeGroup (codec : Codec α) (count : Nat) (value : Json) :
    Effects.Program allowed (Internal.decodeGroup (m := EffF e Empty) codec count value).run := by
  apply Effects.except_bind _ (decode _ value)
  intro values
  split <;> trivial

private theorem check (expected : Request) (record : ReplayRecord) :
    Effects.Program allowed (Internal.check (m := EffF e Empty) expected record).run := by
  unfold Internal.check
  split <;> trivial

private theorem finish (ports : Ports allowed store blobs) (branch : Location) (outcome : Exit) :
    Effects.Program allowed (Internal.finish store branch outcome).run := by
  apply Effects.except_bind
  · apply Effects.except_bind _ (Effects.except_lift _ (ports.create _ _))
    intro record
    split <;> trivial
  · intro _
    trivial

private theorem outcome (ports : Ports allowed store blobs) (branch : Location) :
    Effects.Program allowed (store.outcome branch).run := by
  apply Effects.except_bind _ (Effects.except_lift _ (ports.read _))
  intro record
  cases record with
  | none => trivial
  | some record => dsimp only; split <;> trivial

private theorem join (ports : Ports allowed store blobs) (location : Location) (count : Nat) :
    Effects.Program allowed (Internal.join store location count).run := by
  apply Effects.except_bind
  · apply Effects.except_mapM
    intro index
    apply Effects.except_bind _ (outcome ports _)
    intro result
    cases result <;> trivial
  · intro _
    trivial

private theorem resume (ports : Ports allowed store blobs) (branch : Location)
    (decode : Json → ExceptT CloudError (EffF e Empty) α)
    (next : α → ExceptT CloudError (EffF e Empty) Progress)
    (decoding : ∀ value, Effects.Program allowed (decode value).run) (continuing : ∀ value, Effects.Program allowed (next value).run)
    (enabled : Bool) (result : Exit) :
    Effects.Program allowed ((match result with
      | .success value => do next (← decode value)
      | result => do
        unless enabled do throw ⟨.divergence, "Replay prefix failed"⟩
        Internal.finish store branch result) : ExceptT CloudError (EffF e Empty) Progress).run := by
  cases result with
  | success value => exact Effects.except_bind _ (decoding value) continuing
  | failure error | cancelled reason =>
    dsimp only
    split
    · exact finish ports _ _
    · trivial

/-- Every replay segment respects its port and user-action contracts, for any
fuel, location, or stored reply. This follows all decoded continuations. -/
theorem walk_preserves (ports : Ports allowed store blobs) (assignment : Assignment) (fuel : Nat)
    (encode : α → Json) (program : Cloud (EffF e Empty) α) (current : Location) (active : Bool)
    (valid : CloudEffects.Program (fun action => Effects.Program allowed action) program) :
    Effects.Program allowed (walk store blobs assignment fuel encode program current active).run := by
  induction fuel generalizing α encode program current active with
  | zero => trivial
  | succ fuel ih =>
    cases program with
    | pure info value =>
      simp only [walk]
      split
      · exact finish ports _ _
      · trivial
    | impure info control next =>
      have request := valid.1
      have continuation := valid.2
      cases control with
      | delay => exact ih encode _ _ _ (CloudEffects.apply _ next continuation ())
      | fail error =>
        simp only [walk]
        split
        · exact finish ports _ _
        · trivial
      | command codec operation =>
        have resumed := resume ports assignment.branch (Internal.decode codec)
          (fun decoded => walk store blobs assignment fuel encode (next.apply decoded)
            current.next (active || current == assignment.location))
          (decode codec) (fun decoded => ih encode _ _ _ (CloudEffects.apply _ next continuation decoded))
        simp only [walk]
        apply Effects.except_bind _ (Effects.except_lift _ (ports.read _))
        intro record
        cases record with
        | some record => exact Effects.except_bind _ (check _ _) (resumed _)
        | none =>
          dsimp only
          split
          · apply Effects.except_bind
            · apply Effects.except_catch
              · exact Effects.except_bind _ (ports.execute codec operation request) (fun _ => trivial)
              · intro _
                trivial
            · intro result
              apply Effects.except_bind _ (Effects.except_lift _ (ports.create _ _))
              intro accepted
              exact Effects.except_bind _ (check _ _) (resumed true)
          · trivial
      | parallel codec count branches =>
        have resumed := resume ports assignment.branch (Internal.decodeGroup codec count)
          (fun decoded => walk store blobs assignment fuel encode (next.apply decoded)
            current.next (active || current == assignment.location))
          (decodeGroup codec count) (fun decoded => ih encode _ _ _ (CloudEffects.apply _ next continuation decoded))
        simp only [walk]
        split
        · split
          · exact ih codec.encode _ _ _ (request _)
          · trivial
        · apply Effects.except_bind _ (Effects.except_lift _ (ports.read _))
          intro record
          split
          · split <;> trivial
          · cases record with
            | some record => exact Effects.except_bind _ (check _ _) (resumed _)
            | none =>
              dsimp only
              split
              · apply Effects.except_bind _ (join ports _ _)
                intro joined
                apply Effects.except_bind _ (Effects.except_lift _ (ports.create _ _))
                intro accepted
                exact Effects.except_bind _ (check _ _) (resumed true)
              · trivial

theorem step_preserves (ports : Ports allowed store blobs) [Codec α] (fuel : Nat)
    (program : ι → Cloud (EffF e Empty) α) (input : ι) (assignment : Assignment)
    (valid : CloudEffects.Program (fun action => Effects.Program allowed action) (program input)) :
    Effects.Program allowed (ReplayInterpreter.step store blobs fuel program input assignment).run := by
  unfold ReplayInterpreter.step
  split
  · apply Effects.except_bind _ (outcome ports _)
    intro completed
    split
    · trivial
    · exact walk_preserves ports assignment fuel Codec.encode _ Location.root false valid
  · trivial

end LeanCloud.Proofs.InterpreterEffects
