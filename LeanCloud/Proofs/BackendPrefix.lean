import LeanCloud.Proofs.BackendLeased

namespace LeanCloud.Backend.Proofs
open Lean LeanEff LeanCloud.Proofs

inductive Program.Prefix (stop : α → Prop) : Program α → Program α → Prop where
  | pure (value : α) : Prefix stop (.pure value) (.pure value)
  | stopped (value : α) (permitted : stop value) (remaining : Program α) :
      Prefix stop (.pure value) remaining
  | request {β : Type} (operation : Request β) (left right : β → Program α)
      (rest : ∀ value, Prefix stop (left value) (right value)) :
      Prefix stop (.request operation left) (.request operation right)

theorem Program.Prefix.refl (stop : α → Prop) (program : Program α) : Prefix stop program program := by
  induction program with
  | pure value => exact .pure value
  | request operation next ih => exact .request operation next next ih

theorem Program.Prefix.bind {stop : α → Prop} {halt : β → Prop}
    {first second : Program α} (same : Prefix stop first second)
    {left right : α → Program β}
    (short : ∀ value, stop value → ∀ remaining, Prefix halt (left value) remaining)
    (next : ∀ value, Prefix halt (left value) (right value)) :
    Prefix halt (first.bind left) (second.bind right) := by
  induction same with
  | pure value => exact next value
  | stopped value permitted remaining => exact short value permitted _
  | request operation first second rest ih => exact .request operation _ _ ih

theorem Safe.prefix {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : α → Backend.State → Prop} {stop : α → Prop} {first second : Program α} {state}
    (safe : Safe valid grows post second state) (same : Program.Prefix stop first second) :
    Safe valid grows (fun value final => stop value ∨ post value final) first state := by
  induction same generalizing state with
  | pure value => exact safe.weaken _ (fun _ _ _ result => .inr result)
  | stopped value permitted remaining => exact .pure fun _ _ _ => .inl permitted
  | request operation left right rest ih =>
    cases safe with
    | request commit resume =>
      exact .request commit fun before value after kept growth law =>
        ih value (resume before value after kept growth law)

def FuelStopped (error : ε) (returned : Except String (Except ε α × σ)) : Prop :=
  ∃ handle, returned = .ok (.error error, handle)

/-- Fuel can shorten a computation only by returning its designated exhaustion
error. Every preceding service request, and every possible reply, is unchanged. -/
def Truncates (error : ε) (first second : ExceptT ε (StateT σ Replay.M) α) : Prop :=
  ∀ handle, Program.Prefix (FuelStopped error)
    (replayView (first.run handle)) (replayView (second.run handle))

namespace Truncates

theorem refl (error : ε) (action : ExceptT ε (StateT σ Replay.M) α) :
    Truncates error action action := fun _ => Program.Prefix.refl _ _

theorem stop (error : ε) (action : ExceptT ε (StateT σ Replay.M) α) :
    Truncates error (throw error) action := by
  intro handle
  change Program.Prefix _ (.pure (Except.ok (ε := String) (Except.error error, handle))) _
  exact .stopped _ ⟨handle, rfl⟩ _

theorem bind {error : ε} {first second : ExceptT ε (StateT σ Replay.M) α}
    (same : Truncates error first second)
    {left right : α → ExceptT ε (StateT σ Replay.M) β}
    (next : ∀ value, Truncates error (left value) (right value)) :
    Truncates error (first >>= left) (second >>= right) := by
  intro handle
  change Program.Prefix _ (replayView (first.run handle >>= fun pair => ExceptT.bindCont left pair.1 pair.2))
    (replayView (second.run handle >>= fun pair => ExceptT.bindCont right pair.1 pair.2))
  simp only [replayView_bind]
  apply Program.Prefix.bind (same handle)
  · intro result stopped remaining
    obtain ⟨saved, rfl⟩ := stopped
    exact .stopped _ ⟨saved, rfl⟩ remaining
  · intro result
    cases result with
    | error error => exact .pure _
    | ok pair =>
      obtain ⟨result, saved⟩ := pair
      cases result with
      | error error => exact .pure _
      | ok value => exact next value saved

end Truncates

namespace Worker

def exhausted : CloudError := ⟨.protocol, "Interpreter fuel exhausted"⟩

private def truncation (db : Db σ Replay.M) : ReplayRelation db db where
  relates := Truncates exhausted
  pure _ := Truncates.refl _ _
  throw _ := Truncates.refl _ _
  bind := Truncates.bind
  get _ := Truncates.refl _ _
  put _ _ := Truncates.refl _ _

theorem step_truncates (db : Db σ Replay.M) (blobs : BlobStorage σ Replay.M)
    (program : Cloud Replay.M Json) (supported : PureProgram program) (location : Location) (fuel extra : Nat) :
    Truncates exhausted (ReplayInterpreter.Internal.step db blobs fuel program location)
      (ReplayInterpreter.Internal.step db blobs (fuel + extra) program location) :=
  (truncation db).step_add blobs blobs fuel extra (fun _ _ _ => Truncates.stop _ _) program supported location

theorem run_truncates [Codec α] (db : Db σ Replay.M) (blobs : BlobStorage σ Replay.M)
    (queue : WorkQueue σ Replay.M) (program : Cloud Replay.M Json)
    (supported : PureProgram program) (fuel extra : Nat) :
    Truncates exhausted
      (ReplayInterpreter.Internal.run (α := α) db blobs queue fuel program)
      (ReplayInterpreter.Internal.run db blobs queue (fuel + extra) program) := by
  induction fuel with
  | zero => exact Truncates.stop _ _
  | succ fuel ih =>
    simp only [Nat.succ_add, ReplayInterpreter.Internal.run]
    apply Truncates.bind (Truncates.refl _ _)
    intro work
    cases work with
    | completed outcome => exact Truncates.refl _ _
    | idle => exact ih
    | item location =>
      have steps := step_truncates db blobs program supported location (fuel + 1) extra
      rw [Nat.add_right_comm fuel 1 extra] at steps
      apply Truncates.bind steps
      intro response
      apply Truncates.bind (Truncates.refl _ _)
      intro _
      cases response with
      | done outcome => exact Truncates.refl _ _
      | runnable _ => exact ih

end Worker
end LeanCloud.Backend.Proofs
