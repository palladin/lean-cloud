import LeanCloud.Proofs.SimulationPrefix

/-! Appending the outer loop to a suspended iteration preserves every atomic
boundary, including saved replies. The iteration and final result may have
different types; their failures are not conflated by the simulation relation. -/

namespace LeanCloud.Simulation
open LeanEff

def Worker.bind (worker : Worker δ α) (next : α → SimM δ β) : Worker δ β :=
  match worker with
  | .waiting operation rest => .waiting operation (rest.append (.one next))
  | .responding value rest => .responding value (rest.append (.one next))
  | .finished value => .ofProgram (next value)
  | .stopped => .stopped

theorem Worker.bind_program (program : SimM δ α) (next : α → SimM δ β) :
    (Worker.ofProgram program).bind next = Worker.ofProgram (program >>= next) := by
  cases program with
  | pure value => rfl
  | impure operation rest => cases operation; rfl

def State.bind (state : State δ α count) (next : Fin count → α → SimM δ β) : State δ β count :=
  ⟨state.durable, fun index => (state.workers index).bind (next index)⟩

theorem State.bind_setWorker (state : State δ α count) (next : Fin count → α → SimM δ β)
    (index : Fin count) (worker : Worker δ α) :
    (state.setWorker index worker).bind next =
      (state.bind next).setWorker index (worker.bind (next index)) := by
  apply (State.mk.injEq ..).mpr
  refine ⟨rfl, ?_⟩
  funext other
  by_cases same : other = index <;> simp [State.bind, State.setWorker, same]

theorem State.bind_durable (state : State δ α count) (next : Fin count → α → SimM δ β) (durable : δ) :
    ({ state with durable }).bind next = { state.bind next with durable } := rfl

/-- Run one original event with an appended continuation. A returned iteration
may expose more code, but no new backend event is inserted or committed. -/
theorem State.bind_event (start : Fin count → SimM δ α) (clock : Nat → δ → δ)
    (next : Fin count → α → SimM δ β) (event : Event count) {source final : State δ α count}
    (executed : step start clock event source = .ok final) :
    ∃ bound, step (fun index => start index >>= next index) clock event (source.bind next) = .ok bound ∧
      State.Prefix (fun _ => False) (final.bind next) bound := by
  cases event with
  | commit index =>
    cases seen : source.workers index <;> simp only [step, seen] at executed
    case waiting operation rest =>
      cases executed
      refine ⟨_, by simp only [step, State.bind, seen, Worker.bind]; rfl, ?_⟩
      simp only [State.bind_durable, State.bind_setWorker, Worker.bind]
      exact .refl _ _
    all_goals cases executed
  | resume index =>
    cases seen : source.workers index <;> simp only [step, seen] at executed
    case responding value rest =>
      cases executed
      refine ⟨_, by simp only [step, State.bind, seen, Worker.bind]; rfl, ?_⟩
      rw [State.bind_setWorker, Worker.bind_program]
      exact (State.Prefix.refl (fun _ => False) (source.bind next)).replace index
        ((Equivalent.apply_append rest value (next index)).symm.prefix (fun _ => False)).workers source.durable
    all_goals cases executed
  | crash index =>
    cases seen : source.workers index <;> simp only [step, seen] at executed
    case waiting operation rest =>
      cases executed
      refine ⟨_, by simp only [step, State.bind, seen, Worker.bind]; rfl, ?_⟩
      rw [State.bind_setWorker]
      exact .refl _ _
    case responding value rest =>
      cases executed
      refine ⟨_, by simp only [step, State.bind, seen, Worker.bind]; rfl, ?_⟩
      rw [State.bind_setWorker]
      exact .refl _ _
    all_goals cases executed
  | restart index =>
    cases seen : source.workers index <;> simp only [step, seen] at executed
    case stopped =>
      cases executed
      refine ⟨_, by simp only [step, State.bind, seen, Worker.bind]; rfl, ?_⟩
      rw [State.bind_setWorker, Worker.bind_program]
      exact .refl _ _
    all_goals cases executed
  | advanceTime elapsed =>
    cases executed
    refine ⟨_, rfl, ?_⟩
    rw [State.bind_durable]
    exact .refl _ _

/-- Replay the same event in an equivalent surrounding loop. Only a restart
needs the fresh entry point; otherwise the worker keeps its saved continuation.
`False` permits no early return in this outer-loop correspondence. -/
theorem State.bind_step {first : Fin count → SimM δ α} {second : Fin count → SimM δ β}
    (clock : Nat → δ → δ) (next : Fin count → α → SimM δ β) (event : Event count)
    (starts : ∀ index, event = .restart index →
      Simulation.Prefix (fun _ => False) (first index >>= next index) (second index))
    {source final : State δ α count} {target : State δ β count}
    (same : State.Prefix (fun _ => False) (source.bind next) target)
    (executed : step first clock event source = .ok final) :
    ∃ extended, step second clock event target = .ok extended ∧
      State.Prefix (fun _ => False) (final.bind next) extended := by
  obtain ⟨bound, called, related⟩ := State.bind_event first clock next event executed
  obtain ⟨extended, ran, follows⟩ := Simulation.Prefix.step_at clock event starts same called
  exact ⟨extended, ran, related.trans follows⟩

end LeanCloud.Simulation
