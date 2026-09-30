import LeanCloud.Proofs.ConcurrentIteration
import LeanCloud.Proofs.ConcurrentNoLoss
import LeanCloud.Proofs.SimulationLoopHistory

/-! Repeated real replay iterations, before choosing a finite outer-loop budget.
Only a successful unfinished iteration may repeat. All journal and leased-queue
operations, saved replies, and independent crashes retain their actual meaning.
Completion is proved in ConcurrentCompletion; finite-fuel realization is proved
in ConcurrentRealization. -/

namespace LeanCloud.Proofs.ConcurrentRepeated
open Lean Simulation SimulationBackend ReplayRecovery ConcurrentAudit

abbrev Outcome := Except CloudError (Option Exit) × SimulationBackend.Worker

def again : Outcome → Bool
  | (.ok none, _) => true
  | _ => false

theorem again_iff (returned : Outcome) : again returned = true ↔ returned.1 = .ok none := by
  rcases returned with ⟨result, handle⟩
  cases result with
  | error error => simp [again]
  | ok outcome => cases outcome <;> simp [again]

/-- Name the existing iteration's continuation so delivery predicates can
refer to its suspended caller without duplicating the polling implementation. -/
def afterPoll (duration traversal : Nat) (program : Cloud M Json) :
    Work → ExceptT CloudError (StateT SimulationBackend.Worker M) (Option Exit)
  | .idle => pure none
  | .completed outcome => pure (some outcome)
  | .item location => do
    let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs traversal program location
    (queue duration).complete location response
    pure (match response with | .done outcome => some outcome | .runnable _ => none)

def rawIteration (duration traversal : Nat) (program : Cloud M Json) : M Outcome :=
  (ReplayIteration.iteration SimulationBackend.db SimulationBackend.noBlobs
    (queue duration) traversal program).run ⟨(), none⟩

def iteration (duration traversal : Nat) (program : Cloud M Json) : SimM ConcurrentHandoff.Log Outcome :=
  History.program (rawIteration duration traversal program)

abbrev RawTrace (duration traversal : Nat) (program : Cloud M Json) (count : Nat) :=
  Repeated.Trace (fun _ : Fin count => rawIteration duration traversal program)
    SimulationBackend.advance again

abbrev Trace (duration traversal : Nat) (program : Cloud M Json) (count : Nat) :=
  Repeated.Trace (fun _ : Fin count => iteration duration traversal program)
    (History.advance SimulationBackend.advance) again

/-- Attach proof history to the concrete execution; this is the same schedule,
not an additional assumption about backend snapshots. -/
def recordTrace (trace : RawTrace duration traversal program count) : Trace duration traversal program count :=
  History.repeatedTrace trace

def Returned (tree : ExecutionTree) (returned : Outcome) (log : ConcurrentHandoff.Log) : Prop :=
  ∃ outcome, returned = (.ok outcome, (⟨(), none⟩ : SimulationBackend.Worker)) ∧
    ∀ value, outcome = some value → value = tree.exit ∧ log.current.completed = some value

/-- Every state of a repeated concurrent execution has the same no-loss and
publication certificates as the fuel-based interpreter. Sufficient traversal
fuel excludes errors in an iteration; no bound on iteration count is assumed. -/
theorem trace_certified {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace duration traversal program count)
    (initialized : trace.states 0 = Simulation.State.initial ⟨SimulationBackend.initial, []⟩
      (fun _ : Fin count => iteration duration traversal program)) :
    (∀ n, AllSafe (Valid tree) Grows (fun _ => Returned tree) (trace.states n)) ∧
      ∀ before after, before ≤ after → Grows (trace.states before).durable (trace.states after).durable := by
  have fresh (worker : Fin count) log (valid : Valid tree log) :
      Safe (Valid tree) Grows (Returned tree) (.ofProgram (iteration duration traversal program)) log :=
    (iteration_safe whole supported comparable sameExit duration traversal enough ⟨(), none⟩ log valid).weaken _
      (fun _ _ _ ⟨outcome, returned, _advanced, correct⟩ => ⟨outcome, returned, correct⟩)
  apply trace.invariants Grows.refl (fun a b => a.trans b) fresh
    (fun elapsed log valid => ⟨valid.advance elapsed, Grows.advance elapsed log⟩)
  rw [initialized]
  exact ⟨Valid.initial tree, fun worker => fresh worker _ (Valid.initial tree)⟩

/-- Repeating an unfinished iteration does not lose pending work. Every
unfinished boundary still has a retained item that carries responsibility for
progress, using the same publication accounting as the original simulator. -/
theorem no_loss {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace duration traversal program count)
    (initialized : trace.states 0 = Simulation.State.initial ⟨SimulationBackend.initial, []⟩
      (fun _ : Fin count => iteration duration traversal program)) (n : Nat) :
    (trace.states n).durable.current.completed = some tree.exit ∨
      ConcurrentAudit.Outstanding (trace.states n).durable.current := by
  obtain ⟨kept, growth⟩ := trace_certified whole supported comparable sameExit duration traversal enough trace initialized
  apply (kept n).1.no_loss
  have initial := (growth 0 n (Nat.zero_le _)).2
  rw [initialized] at initial
  exact initial

/-- Once this worker's crashes stop, fair worker actions finish its current
iteration, even while other workers repeat or crash. This is an iteration
boundary, not an assertion that the workflow has completed. -/
theorem iteration_returns {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace duration traversal program count)
    (initialized : trace.states 0 = Simulation.State.initial ⟨SimulationBackend.initial, []⟩
      (fun _ : Fin count => iteration duration traversal program))
    (fair : trace.WeaklyFair) (worker : Fin count) (cut : Nat) (noCrash : trace.NoCrashesAfter worker cut) :
    ∃ later outcome, cut ≤ later ∧
      (trace.states later).workers worker = .finished (.ok outcome, ⟨(), none⟩) ∧
      ∀ value, outcome = some value → value = tree.exit ∧ (trace.states later).durable.current.completed = some value := by
  obtain ⟨kept, growth⟩ := trace_certified whole supported comparable sameExit duration traversal enough trace initialized
  have fresh log (valid : Valid tree log) :
      Safe (Valid tree) Grows (Returned tree) (.ofProgram (iteration duration traversal program)) log :=
    (iteration_safe whole supported comparable sameExit duration traversal enough ⟨(), none⟩ log valid).weaken _
      (fun _ _ _ ⟨outcome, returned, _advanced, correct⟩ => ⟨outcome, returned, correct⟩)
  obtain ⟨later, returned, after, finished, outcome, same, correct⟩ :=
    trace.schedule.finishes fair.workers worker Grows.refl (fun a b => a.trans b)
      (fun n => (kept n).1) growth fresh cut ((kept cut).2 worker) noCrash
  subst returned
  exact ⟨later, outcome, after, finished, correct⟩

/-- A finished unfinished iteration can make another full iteration under
fair repetition and worker scheduling. The later iteration may still be idle;
queue-delivery fairness is not built into this result. -/
theorem next_iteration {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace duration traversal program count)
    (initialized : trace.states 0 = Simulation.State.initial ⟨SimulationBackend.initial, []⟩
      (fun _ : Fin count => iteration duration traversal program))
    (fair : trace.WeaklyFair) (worker : Fin count) (cut : Nat) (noCrash : trace.NoCrashesAfter worker cut)
    (unfinished : (trace.states cut).workers worker = .finished (.ok none, ⟨(), none⟩)) :
    ∃ later outcome, cut < later ∧
      (trace.states later).workers worker = .finished (.ok outcome, ⟨(), none⟩) ∧
      ∀ value, outcome = some value → value = tree.exit ∧ (trace.states later).durable.current.completed = some value := by
  obtain ⟨started, afterStart, _⟩ := trace.eventually_repeats fair worker cut _ unfinished rfl
  obtain ⟨later, outcome, after, finished, correct⟩ := iteration_returns whole supported comparable sameExit
    duration traversal enough trace initialized fair worker started (fun n beyond => noCrash n (by omega))
  exact ⟨later, outcome, Nat.lt_of_lt_of_le afterStart after, finished, correct⟩

end LeanCloud.Proofs.ConcurrentRepeated
