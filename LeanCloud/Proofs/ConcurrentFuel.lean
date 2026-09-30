import LeanCloud.Proofs.ConcurrentCompletion
import LeanCloud.Proofs.SimulationBinding

/-! Relate a fixed-traversal iteration to the remaining finite replay loop.
The intermediate worker keeps iteration errors separate from workflow outcomes.
This prevents a workflow error equal to the fuel error from acting as a cut. -/

namespace LeanCloud.Proofs.ConcurrentFuel
open Lean Simulation SimulationBackend ConcurrentRepeated

abbrev Answer (α : Type) := Except CloudError α × SimulationBackend.Worker

def loop [Codec α] (duration fuel : Nat) (program : Cloud M Json) : M (Answer α) :=
  (ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs
    (queue duration) fuel program).run ⟨(), none⟩

theorem iteration_prefix (duration smaller larger : Nat) (program : Cloud M Json)
    (supported : PureProgram program) (enough : smaller ≤ larger) :
    Prefix (fun returned => returned.1 = .error ConcurrentQueue.exhausted)
      (rawIteration duration smaller program) (rawIteration duration larger program) := by
  have same := (ReplayIteration.iteration_truncates SimulationBackend.db SimulationBackend.noBlobs
    (queue duration) program supported smaller (larger - smaller)).program (⟨(), none⟩ : SimulationBackend.Worker)
  rwa [Nat.add_sub_of_le enough] at same

/-- The real loop's continuation after one iteration. -/
def resume [Codec α] (duration remaining : Nat) (program : Cloud M Json) : Outcome → M (Answer α)
  | (.error error, handle) => pure (.error error, handle)
  | (.ok none, handle) =>
    (ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs (queue duration) remaining program).run handle
  | (.ok (some outcome), handle) =>
    (ReplayInterpreter.Internal.result (m := StateT SimulationBackend.Worker M) (α := α) outcome).run handle

theorem run_equivalent [Codec α] (duration remaining : Nat) (program : Cloud M Json) :
    Equivalent ((ReplayInterpreter.Internal.run (α := α) SimulationBackend.db SimulationBackend.noBlobs
      (queue duration) (remaining + 1) program).run ⟨(), none⟩)
      (rawIteration duration (remaining + 1) program >>= resume duration remaining program) := by
  apply (ReplayIteration.run_succ_equivalent SimulationBackend.db SimulationBackend.noBlobs
    (queue duration) remaining program ⟨(), none⟩).trans
  change Equivalent (rawIteration duration (remaining + 1) program >>= _)
    (rawIteration duration (remaining + 1) program >>= resume duration remaining program)
  apply (Equivalent.refl _).bind
  intro returned
  rcases returned with ⟨result, handle⟩
  cases result with
  | error error => exact .refl _
  | ok outcome => cases outcome <;> exact .refl _

/-- A traversal may stop early only with an iteration error. Appending the
outer loop preserves every result exactly, including workflow errors. -/
def Follows [Codec α] (duration remaining : Nat) (program : Cloud M Json)
    (iteration : Simulation.Worker Durable Outcome) (running : Simulation.Worker Durable (Answer α)) : Prop :=
  ∃ expanded : Simulation.Worker Durable Outcome,
    Simulation.Worker.Prefix (fun returned => returned.1 = .error ConcurrentQueue.exhausted) iteration expanded ∧
    Simulation.Worker.Prefix (fun _ => False) (expanded.bind (resume duration remaining program)) running

/-- Enter the actual finite loop with any smaller iteration traversal budget. -/
theorem Follows.entry [Codec α] (duration traversal remaining : Nat) (program : Cloud M Json)
    (supported : PureProgram program) (enough : traversal ≤ remaining + 1) :
    Follows duration remaining program (.ofProgram (rawIteration duration traversal program))
      (.ofProgram ((ReplayInterpreter.Internal.run (α := α) SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) (remaining + 1) program).run ⟨(), none⟩)) := by
  have larger := iteration_prefix duration traversal (remaining + 1) program supported enough
  refine ⟨.ofProgram (rawIteration duration (remaining + 1) program), larger.workers, ?_⟩
  rw [Simulation.Worker.bind_program]
  exact ((run_equivalent (α := α) duration remaining program).symm.prefix (fun _ => False)).workers

theorem Follows.extend [Codec α] {duration remaining program}
    {iteration : Simulation.Worker Durable Outcome} {running extended : Simulation.Worker Durable (Answer α)}
    (follows : Follows duration remaining program iteration running)
    (same : Simulation.Worker.Prefix (fun _ => False) running extended) :
    Follows duration remaining program iteration extended := by
  obtain ⟨expanded, first, last⟩ := follows
  exact ⟨expanded, first, last.trans same⟩

/-- Successful iteration results cannot use the traversal-exhaustion escape.
The surrounding loop therefore reaches precisely the corresponding continuation. -/
theorem Follows.returned [Codec α] {duration remaining program outcome handle}
    {running : Simulation.Worker Durable (Answer α)}
    (follows : Follows duration remaining program (.finished (.ok outcome, handle)) running) :
    Simulation.Worker.Prefix (fun _ => False)
      (.ofProgram (resume duration remaining program (.ok outcome, handle))) running := by
  obtain ⟨expanded, first, last⟩ := follows
  cases first with
  | finished => exact last
  | truncated value allowed rest => cases allowed

/-- Repeating a successful unfinished iteration consumes one outer-loop unit.
It makes no backend request: the finite interpreter already has the next code. -/
theorem Follows.repeatIteration [Codec α] {duration remaining program}
    {running : Simulation.Worker Durable (Answer α)} (traversal : Nat) (supported : PureProgram program)
    (enough : traversal ≤ remaining + 1)
    (follows : Follows duration (remaining + 1) program (.finished (.ok none, ⟨(), none⟩)) running) :
    Follows duration remaining program (.ofProgram (rawIteration duration traversal program)) running :=
  (Follows.entry duration traversal remaining program supported enough).extend follows.returned

theorem Follows.reset [Codec α] {duration remaining program}
    {running : Simulation.Worker Durable (Answer α)}
    (follows : Follows duration remaining program .stopped running) (fresh : Nat) :
    Follows duration fresh program .stopped running := by
  obtain ⟨expanded, first, last⟩ := follows
  cases first
  exact ⟨.stopped, .stopped, last⟩

def Related [Codec α] (duration : Nat) (remaining : Fin count → Nat) (program : Cloud M Json)
    (source : Simulation.State Durable Outcome count) (target : Simulation.State Durable (Answer α) count) : Prop :=
  source.durable = target.durable ∧
    ∀ worker, Follows duration (remaining worker) program (source.workers worker) (target.workers worker)

theorem Related.expand [Codec α] {duration remaining program}
    {source : Simulation.State Durable Outcome count} {target : Simulation.State Durable (Answer α) count}
    (same : Related duration remaining program source target) :
    ∃ expanded : Simulation.State Durable Outcome count,
      Simulation.State.Prefix (fun returned => returned.1 = .error ConcurrentQueue.exhausted) source expanded ∧
      Simulation.State.Prefix (fun _ => False)
        (expanded.bind (fun worker => resume duration (remaining worker) program)) target := by
  let middle := fun worker => Classical.choose (same.2 worker)
  refine ⟨⟨source.durable, middle⟩, ⟨rfl, ?_⟩, ⟨same.1, ?_⟩⟩
  · intro worker
    exact (Classical.choose_spec (same.2 worker)).1
  · intro worker
    exact (Classical.choose_spec (same.2 worker)).2

theorem Related.of_expansion [Codec α] {duration remaining program}
    {source expanded : Simulation.State Durable Outcome count} {target : Simulation.State Durable (Answer α) count}
    (first : Simulation.State.Prefix (fun returned => returned.1 = .error ConcurrentQueue.exhausted) source expanded)
    (last : Simulation.State.Prefix (fun _ => False)
      (expanded.bind (fun worker => resume duration (remaining worker) program)) target) :
    Related duration remaining program source target :=
  ⟨first.1.trans last.1, fun worker => ⟨expanded.workers worker, first.2 worker, last.2 worker⟩⟩

def remainingAfter (initial remaining : Fin count → Nat) : Simulation.Event count → Fin count → Nat
  | .restart index => fun worker => if worker = index then initial worker else remaining worker
  | _ => remaining

/-- A restart discards the old local budget together with the stopped worker's
continuation. Every other worker retains its own remaining loop budget. -/
theorem Related.refresh [Codec α] {duration remaining program}
    {source final : Simulation.State Durable Outcome count} {target : Simulation.State Durable (Answer α) count}
    (same : Related duration remaining program source target) (initial : Fin count → Nat)
    (event : Simulation.Event count) {start : Fin count → M Outcome}
    (executed : Simulation.step start SimulationBackend.advance event source = .ok final) :
    Related duration (remainingAfter initial remaining event) program source target := by
  cases event with
  | commit _ | resume _ | crash _ | advanceTime _ => exact same
  | restart index =>
    have stopped : source.workers index = .stopped := by
      cases seen : source.workers index <;> simp only [Simulation.step, seen] at executed
      case stopped => rfl
      all_goals cases executed
    refine ⟨same.1, ?_⟩
    intro worker
    by_cases selected : worker = index
    · subst worker
      have current := same.2 index
      rw [stopped] at current ⊢
      simpa only [remainingAfter, ↓reduceIte] using current.reset (initial index)
    · simpa only [remainingAfter, selected, ↓reduceIte] using same.2 worker

/-- Every ordinary simulator event has the same durable effect in the finite
loop. The expanded iteration is proof data; the target runs the actual loop. -/
theorem Related.ordinary [Codec α] (duration traversal : Nat) (initial remaining : Fin count → Nat)
    (program : Cloud M Json) (supported : PureProgram program)
    (enough : ∀ worker, traversal ≤ initial worker + 1) (event : Simulation.Event count)
    {source final : Simulation.State Durable Outcome count} {target : Simulation.State Durable (Answer α) count}
    (same : Related duration remaining program source target)
    (executed : Simulation.step (fun _ => rawIteration duration traversal program) SimulationBackend.advance event source = .ok final) :
    ∃ extended,
      Simulation.step (fun worker => loop duration (initial worker + 1) program) SimulationBackend.advance event target = .ok extended ∧
      Related duration (remainingAfter initial remaining event) program final extended := by
  obtain ⟨expanded, first, last⟩ := (same.refresh initial event executed).expand
  obtain ⟨advanced, iterated, prefixSame⟩ := Prefix.step_at SimulationBackend.advance event
    (fun worker _ => iteration_prefix duration traversal (initial worker + 1) program supported (enough worker)) first executed
  have starts worker (restart : event = .restart worker) :
      Prefix (fun _ => False)
        (rawIteration duration (initial worker + 1) program >>=
          resume (α := α) duration (remainingAfter initial remaining event worker) program)
        (loop duration (initial worker + 1) program) := by
    rw [restart]
    simpa only [remainingAfter, ↓reduceIte, loop] using
      ((run_equivalent (α := α) duration (initial worker) program).symm.prefix (fun _ => False))
  obtain ⟨extended, ran, bound⟩ := Simulation.State.bind_step SimulationBackend.advance
    (fun worker => resume duration (remainingAfter initial remaining event worker) program) event starts last iterated
  exact ⟨extended, ran, Related.of_expansion prefixSame bound⟩

/-- A repeated-model loop boundary is a stuttering step of the actual loop:
only the proof's remaining budget changes, while shared storage stays equal. -/
theorem Related.repeatIteration [Codec α] {duration remaining program}
    {source : Simulation.State Durable Outcome count} {target : Simulation.State Durable (Answer α) count}
    (same : Related duration remaining program source target) (worker : Fin count)
    (traversal budget : Nat) (supported : PureProgram program) (enough : traversal ≤ budget + 1)
    (available : remaining worker = budget + 1)
    (returned : source.workers worker = .finished (.ok none, ⟨(), none⟩)) :
    Related duration (fun index => if index = worker then budget else remaining index) program
      (source.setWorker worker (.ofProgram (rawIteration duration traversal program))) target := by
  refine ⟨same.1, ?_⟩
  intro index
  by_cases selected : index = worker
  · subst index
    have follows := same.2 worker
    rw [returned, available] at follows
    simpa only [State.setWorker_same, ↓reduceIte] using follows.repeatIteration traversal supported enough
  · simpa only [selected, ↓reduceIte, State.setWorker_other _ _ _ _ selected] using same.2 index

end LeanCloud.Proofs.ConcurrentFuel
