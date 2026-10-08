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

private theorem readChildren (ports : Ports allowed store blobs) (location : Location) (indices : List Nat) :
    Effects.Program allowed (Internal.readChildren store location indices).run := by
  induction indices with
  | nil => trivial
  | cons index rest ih =>
    apply Effects.except_bind _ (outcome ports _)
    intro first
    cases first with
    | none => trivial
    | some value => exact Effects.except_bind _ ih (fun _ => trivial)

private theorem join (ports : Ports allowed store blobs) (location : Location) (count : Nat) :
    Effects.Program allowed (Internal.tryJoin store location count).run := by
  apply Effects.except_bind
  · exact readChildren ports _ _
  · intro _
    trivial

private theorem resume (ports : Ports allowed store blobs) (branch : Location)
    (decode : Json → ExceptT CloudError (EffF e Empty) α)
    (next : α → ExceptT CloudError (EffF e Empty) Progress)
    (decoding : ∀ value, Effects.Program allowed (decode value).run)
    (continuing : ∀ value, Effects.Program allowed (next value).run) (result : Exit) :
    Effects.Program allowed (Internal.resume store branch decode next result).run := by
  cases result with
  | success value => exact Effects.except_bind _ (decoding value) continuing
  | failure error | cancelled reason => exact finish ports _ _

private theorem recorded (ports : Ports allowed store blobs) (current : Location)
    (expected : Request) (missing : String) :
    Effects.Program allowed (Internal.recorded store current expected missing).run := by
  apply Effects.except_bind _ (Effects.except_lift _ (ports.read _))
  intro record
  cases record with
  | none => trivial
  | some record =>
    apply Effects.except_bind _ (check _ _)
    intro result
    cases result <;> trivial

/-- Execution respects the port and user-action contracts at every continuation. -/
theorem replay_preserves (ports : Ports allowed store blobs) (branchStart : Location) (fuel : Nat)
    (encode : α → Json) (program : Cloud (EffF e Empty) α) (current : Location)
    (valid : CloudEffects.Program (fun action => Effects.Program allowed action) program) :
    Effects.Program allowed (replay store blobs branchStart fuel encode program current).run := by
  induction fuel generalizing α encode program current with
  | zero => trivial
  | succ fuel ih =>
    cases program with
    | pure info value => exact finish ports _ _
    | impure info control next =>
      have request := valid.1
      have continuation := valid.2
      cases control with
      | delay => exact ih encode _ _ (CloudEffects.apply _ next continuation ())
      | fail error => exact finish ports _ _
      | command codec operation =>
        have resumed := resume ports branchStart (Internal.decode codec)
          (fun decoded => replay store blobs branchStart fuel encode (next.apply decoded) current.next)
          (decode codec) (fun decoded => ih encode _ _ (CloudEffects.apply _ next continuation decoded))
        simp only [replay]
        apply Effects.except_bind _ ?_ resumed
        unfold Internal.command
        apply Effects.except_bind _ (Effects.except_lift _ (ports.read _))
        intro record
        cases record with
        | some record => exact check _ _
        | none =>
          unfold Internal.execute
          apply Effects.except_bind
          · apply Effects.except_catch
            · exact Effects.except_bind _ (ports.execute codec operation request) (fun _ => trivial)
            · intro _
              trivial
          · intro result
            apply Effects.except_bind _ (Effects.except_lift _ (ports.create _ _))
            intro accepted
            exact check _ _
      | parallel codec count branches =>
        have resumed := resume ports branchStart (Internal.decodeGroup codec count)
          (fun decoded => replay store blobs branchStart fuel encode (next.apply decoded) current.next)
          (decodeGroup codec count) (fun decoded => ih encode _ _ (CloudEffects.apply _ next continuation decoded))
        simp only [replay]
        apply Effects.except_bind _ (Effects.except_lift _ (ports.read _))
        intro record
        cases record with
        | some record => exact Effects.except_bind _ (check _ _) resumed
        | none =>
          apply Effects.except_bind _ (join ports _ _)
          intro joined
          cases joined with
          | none => trivial
          | some outcome =>
            apply Effects.except_bind _ (Effects.except_lift _ (ports.create _ _))
            intro accepted
            exact Effects.except_bind _ (check _ _) resumed

/-- Reconstruction follows recorded replies, then hands the same computation
and remaining fuel to execution. -/
theorem reconstruct_preserves (ports : Ports allowed store blobs) (branchStart : Location) (fuel : Nat)
    (encode : α → Json) (program : Cloud (EffF e Empty) α) (current : Location)
    (valid : CloudEffects.Program (fun action => Effects.Program allowed action) program) :
    Effects.Program allowed (reconstruct store blobs branchStart fuel encode program current).run := by
  induction fuel generalizing α encode program current with
  | zero => trivial
  | succ fuel ih =>
    rw [reconstruct.eq_def]
    dsimp only
    split
    · exact replay_preserves ports branchStart (fuel + 1) encode program current valid
    · cases program with
      | pure info value => trivial
      | impure info control next =>
        have request := valid.1
        have continuation := valid.2
        cases control with
        | delay => exact ih encode _ _ (CloudEffects.apply _ next continuation ())
        | fail error => trivial
        | command codec operation =>
          apply Effects.except_bind _ (recorded ports _ _ _)
          intro wire
          apply Effects.except_bind _ (decode codec wire)
          intro value
          exact ih encode _ _ (CloudEffects.apply _ next continuation value)
        | parallel codec count branches =>
          dsimp only
          split
          · split
            · exact ih codec.encode _ _ (request _)
            · trivial
          · apply Effects.except_bind _ (recorded ports _ _ _)
            intro wire
            apply Effects.except_bind _ (decodeGroup codec count wire)
            intro values
            exact ih encode _ _ (CloudEffects.apply _ next continuation values)

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
    · exact reconstruct_preserves ports assignment.branchStart fuel Codec.encode _ Location.root valid
  · trivial

end LeanCloud.Proofs.InterpreterEffects
