import LeanCloud.Proofs.BackendReturns

namespace LeanCloud.Backend.Proofs
open Lean LeanEff LeanCloud.Proofs

def actionView (action : ExceptT ε (StateT σ Replay.M) α) (handle : σ) :
    Program (Except String (Except ε α × σ)) := replayView (action.run handle)

private def continueAction (next : α → ExceptT ε (StateT σ Replay.M) β) :
    Except String (Except ε α × σ) → Program (Except String (Except ε β × σ))
  | .error error => .pure (.error error)
  | .ok (.error error, handle) => .pure (.ok (.error error, handle))
  | .ok (.ok value, handle) => actionView (next value) handle

theorem actionView_bind (first : ExceptT ε (StateT σ Replay.M) α)
    (next : α → ExceptT ε (StateT σ Replay.M) β) (handle : σ) :
    actionView (first >>= next) handle = (actionView first handle).bind (continueAction next) := by
  change replayView (first.run handle >>= fun pair => ExceptT.bindCont next pair.1 pair.2) = _
  rw [replayView_bind]
  congr 1
  funext returned
  cases returned with
  | error error => rfl
  | ok pair => obtain ⟨result, saved⟩ := pair; cases result <;> rfl

theorem actionView_assoc (first : ExceptT ε (StateT σ Replay.M) α)
    (next : α → ExceptT ε (StateT σ Replay.M) β) (last : β → ExceptT ε (StateT σ Replay.M) γ) (handle : σ) :
    actionView ((first >>= next) >>= last) handle = actionView (first >>= fun value => next value >>= last) handle := by
  simp only [actionView_bind, Program.bind_assoc]
  congr 1
  funext returned
  cases returned with
  | error error => rfl
  | ok pair =>
    obtain ⟨result, saved⟩ := pair
    cases result with
    | error error => rfl
    | ok value => exact (actionView_bind (next value) last saved).symm

theorem actionView_congr {first second : ExceptT ε (StateT σ Replay.M) α}
    (same : ∀ handle, actionView first handle = actionView second handle)
    {left right : α → ExceptT ε (StateT σ Replay.M) β}
    (next : ∀ value handle, actionView (left value) handle = actionView (right value) handle)
    (handle : σ) : actionView (first >>= left) handle = actionView (second >>= right) handle := by
  simp only [actionView_bind, same]
  congr 1
  funext returned
  cases returned with
  | error error => rfl
  | ok pair =>
    obtain ⟨result, saved⟩ := pair
    cases result with
    | error error => rfl
    | ok value => exact next value saved

namespace Fuel
open Iteration

abbrev Answer (α : Type) := Except String (Except CloudError α × Replay.Worker)

def loop [Codec α] (fuel : Nat) (source : Cloud Replay.M Json) : Backend.M (Answer α) :=
  ((ReplayInterpreter.Internal.run Replay.db Replay.noBlobs Replay.queue fuel source).run ⟨(), none⟩).run

def resume [Codec α] (remaining : Nat) (source : Cloud Replay.M Json) : Outcome → Backend.M (Answer α)
  | .error error => pure (.error error)
  | .ok (.error error, handle) => pure (.ok (.error error, handle))
  | .ok (.ok none, handle) => ((ReplayInterpreter.Internal.run Replay.db Replay.noBlobs Replay.queue remaining source).run handle).run
  | .ok (.ok (some outcome), handle) =>
      ((ReplayInterpreter.Internal.result (m := StateT Replay.Worker Replay.M) outcome).run handle).run

theorem run_factor [Codec α] (remaining : Nat) (source : Cloud Replay.M Json) (handle : Replay.Worker) :
    actionView (ReplayInterpreter.Internal.run (α := α) Replay.db Replay.noBlobs Replay.queue (remaining + 1) source) handle =
      actionView (do
        match ← ReplayIteration.iteration Replay.db Replay.noBlobs Replay.queue (remaining + 1) source with
        | some outcome => ReplayInterpreter.Internal.result outcome
        | none => ReplayInterpreter.Internal.run Replay.db Replay.noBlobs Replay.queue remaining source) handle := by
  rw [ReplayInterpreter.Internal.run]
  unfold ReplayIteration.iteration
  apply Eq.symm
  apply (actionView_assoc (liftM Replay.queue.next) _ _ handle).trans
  apply actionView_congr (fun _ => rfl)
  intro work handle
  cases work with
  | idle | completed outcome => rfl
  | item location =>
    apply (actionView_assoc (ReplayInterpreter.Internal.step Replay.db Replay.noBlobs (remaining + 1) source location) _ _ handle).trans
    apply actionView_congr (fun _ => rfl)
    intro response handle
    apply (actionView_assoc (liftM (Replay.queue.complete location response)) _ _ handle).trans
    apply actionView_congr (fun _ => rfl)
    intro _ handle
    cases response <;> rfl

theorem loop_factor [Codec α] (remaining : Nat) (source : Cloud Replay.M Json) :
    Program.ofEff (loop (α := α) (remaining + 1) source) =
      (Program.ofEff (Iteration.program (remaining + 1) source)).bind
        (fun returned => Program.ofEff (resume remaining source returned)) := by
  change actionView (ReplayInterpreter.Internal.run (α := α) Replay.db Replay.noBlobs Replay.queue (remaining + 1) source) ⟨(), none⟩ = _
  rw [run_factor, actionView_bind]
  congr 1
  funext returned
  cases returned with
  | error error => rfl
  | ok pair =>
    cases pair with
    | mk outcome handle =>
      cases outcome with
      | error error => rfl
      | ok outcome => cases outcome <;> rfl

theorem iteration_prefix (smaller larger : Nat) (source : Cloud Replay.M Json)
    (supported : PureProgram source) (enough : smaller ≤ larger) :
    Program.Prefix (FuelStopped Worker.exhausted)
      (Program.ofEff (Iteration.program smaller source)) (Program.ofEff (Iteration.program larger source)) := by
  have monotone : Truncates Worker.exhausted
      (ReplayIteration.iteration Replay.db Replay.noBlobs Replay.queue smaller source)
      (ReplayIteration.iteration Replay.db Replay.noBlobs Replay.queue (smaller + (larger - smaller)) source) := by
    unfold ReplayIteration.iteration
    apply Truncates.bind (Truncates.refl _ _)
    intro work
    cases work with
    | idle | completed outcome => exact Truncates.refl _ _
    | item location =>
      apply Truncates.bind (Worker.step_truncates Replay.db Replay.noBlobs source supported location smaller _)
      intro response
      apply Truncates.bind (Truncates.refl _ _)
      intro _
      exact Truncates.refl _ _
  have initial := monotone ⟨(), none⟩
  simpa only [Nat.add_sub_of_le enough, Iteration.program, replayView] using initial

/-- The target appends the real outer-loop continuation. Only an explicit
iteration exhaustion may truncate the correspondence; workflow failures are
ordinary successful `some Exit` results and cannot trigger this escape. -/
inductive Follows (stop : α → Prop) (resume : α → Program β) : Program α → Program β → Prop where
  | returned (value : α) : Follows stop resume (.pure value) (resume value)
  | stopped (value : α) (allowed : stop value) (rest : Program β) : Follows stop resume (.pure value) rest
  | request {γ : Type} (operation : Request γ) (left : γ → Program α) (right : γ → Program β)
      (rest : ∀ value, Follows stop resume (left value) (right value)) :
      Follows stop resume (.request operation left) (.request operation right)

theorem Follows.of_prefix {stop : α → Prop} {first second : Program α}
    (initial : Program.Prefix stop first second) (resume : α → Program β) :
    Follows stop resume first (second.bind resume) := by
  induction initial with
  | pure value => exact .returned value
  | stopped value allowed rest => exact .stopped value allowed _
  | request operation left right rest ih => exact .request operation _ _ ih

theorem Follows.entry [Codec α] (traversal remaining : Nat) (source : Cloud Replay.M Json)
    (supported : PureProgram source) (enough : traversal ≤ remaining + 1) :
    Follows (FuelStopped Worker.exhausted) (fun returned => Program.ofEff (resume (α := α) remaining source returned))
      (Program.ofEff (Iteration.program traversal source)) (Program.ofEff (loop (remaining + 1) source)) := by
  rw [loop_factor]
  exact Follows.of_prefix (iteration_prefix traversal (remaining + 1) source supported enough) _

theorem Follows.returned_eq {stop : α → Prop} {resume : α → Program β} {value target}
    (same : Follows stop resume (.pure value) target) (complete : ¬ stop value) : target = resume value := by
  cases same with
  | returned => rfl
  | stopped _ allowed => exact False.elim (complete allowed)

theorem Follows.request_view {stop : α → Prop} {resume : α → Program β}
    {operation : Request γ} {next : γ → Program α} {target : Program β}
    (same : Follows stop resume (.request operation next) target) :
    ∃ rest, target = .request operation rest ∧ ∀ value, Follows stop resume (next value) (rest value) := by
  cases same with
  | request operation left right follows => exact ⟨right, rfl, follows⟩

end Fuel
end LeanCloud.Backend.Proofs
