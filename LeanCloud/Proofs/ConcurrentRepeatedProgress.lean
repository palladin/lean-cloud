import LeanCloud.Proofs.ConcurrentRepeated
import LeanCloud.Proofs.ConcurrentLiveness

/-! Progress of concrete repeated workers. Recording is derived from the raw
execution; polling and publication reuse the same proofs as finite attempts.
ConcurrentCompletion supplies queue liveness; ConcurrentRealization supplies
finite-fuel realization. -/

namespace LeanCloud.Proofs.ConcurrentRepeated
open Lean Simulation SimulationBackend ReplayRecovery ConcurrentAudit

variable {program : Cloud M Json} {tree : ExecutionTree}
  (whole : Expansion program tree) (supported : PureProgram program)
  (comparable : Comparable (tree.journal Location.root))
  (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
  (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
  (trace : RawTrace duration traversal program count)
  (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
    (fun _ : Fin count => rawIteration duration traversal program))

include whole supported comparable sameExit enough initialized

/-- The concrete trace supplies its own history and publication invariants. -/
theorem raw_certified :
    (∀ n, AllSafe (Valid tree) Grows (fun _ => Returned tree) ((recordTrace trace).states n)) ∧
      ∀ before after, before ≤ after →
        Grows ((recordTrace trace).states before).durable ((recordTrace trace).states after).durable :=
  trace_certified whole supported comparable sameExit duration traversal enough (recordTrace trace)
    (History.repeated_trace_initial trace SimulationBackend.initial initialized)

/-- Repetition and duplicate writes cannot prevent the finite visible journal
from stabilizing. No queue fairness or successful completion is assumed. -/
theorem journal_stable :
    ∃ cut, ∀ n, cut ≤ n →
      ConcurrentJournal.view (trace.states n).durable = ConcurrentJournal.view (trace.states cut).durable := by
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  apply JournalAdapter.finite_journal_stable (fun n => ConcurrentJournal.view (trace.states n).durable)
    ((tree.records Location.root).map Prod.fst)
  · intro before after later
    exact (growth before after later).1.journal.1
  · intro n key value recorded
    have bound := (kept n).1.1.journal key value recorded
    have member := (tree.journal_read_iff Location.root (by simp [Location.root]) key value).mp bound
    exact List.mem_map.mpr ⟨(key, value), member, rfl⟩

/-- A started iteration reaches the actual continuation of its leased poll.
This does not assume that the poll selected a message; idle is still possible. -/
theorem iteration_polls (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime)
    (continuing : (((recordTrace trace).states atTime).workers worker).Continues
      (iteration duration traversal program)) :
    ∃ later work handle, atTime < later ∧
      (((recordTrace trace).states later).workers worker).Continues
        (History.program ((afterPoll duration traversal program work).run handle)) ∧
      ConcurrentQueue.Next tree (work, handle) (trace.states later).durable ∧
      ConcurrentHandoff.Polled (work, handle) ((recordTrace trace).states later).durable ∧
      ((recordTrace trace).states atTime).durable.past.length < ((recordTrace trace).states later).durable.past.length := by
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  exact poll_scheduled (recordTrace trace).schedule tree duration (fun n => (kept n).1) growth
    (History.repeated_trace_fair trace fair).workers worker atTime noCrash ⟨(), none⟩ _ continuing

/-- Once selected code is entered, fair worker actions derive its publication.
For every emitted location, the conclusion identifies a real queue boundary,
even if another worker consumed that message before publication finished. -/
theorem selected_publishes (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime)
    (current : Location) (node : ExecutionTree) (route : TreeRoute tree Location.root current node)
    (active : route.Activated (ConcurrentJournal.view (trace.states atTime).durable))
    (receipt : LeaseQueueModel.Receipt)
    (received : ConcurrentHandoff.Received current receipt ((recordTrace trace).states atTime).durable)
    (continuing : (((recordTrace trace).states atTime).workers worker).Continues
      (History.program ((afterPoll duration traversal program (.item current)).run ⟨(), some (current, receipt)⟩))) :
    ∃ later response, atTime ≤ later ∧
      PublishedStep tree current node ((recordTrace trace).states atTime).durable response ((recordTrace trace).states later).durable ∧
      ∀ locations, response = .runnable locations → ∀ target ∈ locations,
        ∃ issuedAt, ∃ slot : Nat, ∃ message : LeaseQueueModel.Message Location, atTime < issuedAt ∧ issuedAt ≤ later ∧
          (trace.states issuedAt).durable.transport.messages[slot]? = some (some message) ∧ message.value = target := by
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  obtain ⟨later, response, after, _remaining, published⟩ := delivered_scheduled (recordTrace trace).schedule
    whole supported route comparable (sameExit _ _ route.member) duration traversal (Nat.le_trans route.fuel_bound enough)
    (fun n => (kept n).1) growth (History.repeated_trace_fair trace fair).workers worker atTime noCrash
    receipt active received _ continuing
  refine ⟨later, response, after, published, ?_⟩
  intro locations same target member
  subst response
  exact published.successor_at (History.repeated_trace_timeline trace) (kept later).1 member

/-- Once completion is durable, every fairly scheduled worker whose crashes
have stopped eventually returns it. A previously unfinished iteration may
finish first; its next iteration reads the final result without running a step. -/
theorem completed_returns (fair : trace.WeaklyFair) (worker : Fin count) (cut : Nat)
    (noCrash : trace.NoCrashesAfter worker cut)
    (completed : (trace.states cut).durable.completed = some tree.exit) :
    ∃ later, cut ≤ later ∧
      ((trace.states later).workers worker).outcome? = some (.ok (some tree.exit), ⟨(), none⟩) := by
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  have fairRecorded := History.repeated_trace_fair trace fair
  obtain ⟨boundary, outcome, after, finished, correct⟩ := iteration_returns whole supported comparable sameExit
    duration traversal enough (recordTrace trace) (History.repeated_trace_initial trace SimulationBackend.initial initialized)
    fairRecorded worker cut noCrash
  have eventually : ∃ later, cut ≤ later ∧
      ((recordTrace trace).states later).workers worker = .finished (.ok (some tree.exit), ⟨(), none⟩) := by
    cases outcome with
    | some outcome =>
      obtain ⟨rfl, _⟩ := correct outcome rfl
      exact ⟨boundary, after, finished⟩
    | none =>
      obtain ⟨started, afterStart, running⟩ := (recordTrace trace).eventually_repeats fairRecorded worker boundary _ finished rfl
      have afterCut : cut ≤ started := by omega
      have present := (growth cut started afterCut).1.completed tree.exit completed
      have progress := iteration_completed (tree := tree) duration traversal program ⟨(), none⟩
        ((recordTrace trace).states started).durable tree.exit present
      obtain ⟨later, beyond, returned⟩ := (recordTrace trace).schedule.eventually_reaches fairRecorded.workers worker
        Grows.refl (fun a b => a.trans b) (fun n => (kept n).1) growth progress started running
        (fun n beyond => noCrash n (by omega)) (.refl _)
      exact ⟨later, Nat.le_trans afterCut beyond, returned⟩
  obtain ⟨later, after, returned⟩ := eventually
  refine ⟨later, after, ?_⟩
  rw [← History.repeated_trace_outcome trace later worker]
  change (((recordTrace trace).states later).workers worker).outcome? = _
  rw [returned]
  rfl

end LeanCloud.Proofs.ConcurrentRepeated
