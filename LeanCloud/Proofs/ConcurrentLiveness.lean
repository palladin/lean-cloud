import LeanCloud.Proofs.ConcurrentRank

/-! Progress facts for the original concurrent interpreter. Its immutable
journal eventually stabilizes, independently of scheduling, crashes, or fuel.
This does not assume that all records have been written or the workflow ended. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery

/-- A set of locations closed under actual, unfinished step responses in a
fixed visible journal. This is an intermediate progress contract: a fair trace
must supply the completed steps and successor delivery, rather than assume this
property as queue fairness. Physical states may differ throughout the steps. -/
def StableResponses (tree : ExecutionTree) (state : Durable) (available : Location → Prop) : Prop :=
  ∀ current, available current → ∃ node, ∃ _route : TreeRoute tree Location.root current node,
    ∃ before after locations,
      view before = view state ∧ view after = view state ∧ Grows before after ∧
      StepProgress tree current node before (.runnable locations) after ∧
      Emits tree (.runnable locations) after ∧ ∀ target ∈ locations, available target

private noncomputable def closedAt (state : Durable) (location : Location) : Bool := by
  classical
  exact decide (∃ outcome, CompletedAt (view state) location.key outcome)

/-- With no new records or final result, finite program structure prevents an
endless chain of response work. Every location in such a closed set has already
reported to an incomplete enclosing group. No bound on duplicates is needed. -/
theorem StableResponses.reported {tree state available} (responses : StableResponses tree state available)
    (current : Location) (ready : available current) : OpenReport current state state := by
  classical
  obtain ⟨node, route, before, after, locations, first, last, growth, progress, emitted, supplied⟩ := responses current ready
  have correct location : closedAt state location = true ↔ ∃ outcome, CompletedAt (view after) location.key outcome := by
    rw [last]
    simp [closedAt]
  have reports (target : Location) (member : target ∈ locations) : OpenReport target after after := by
    have decreases := progress.rank_decreases route emitted (first.trans last.symm) (closedAt state) correct target member
    exact (responses.reported target (supplied target member)).fixed last.symm last.symm
  have reported := progress.open_report (.refl _) growth (.refl _)
    (by intro outcome impossible; cases impossible) (by
      intro children same target member
      cases same
      exact reports target member)
  exact reported.fixed first last
termination_by rank tree (closedAt state) current
decreasing_by
  exact decreases

end LeanCloud.Proofs.ConcurrentJournal

namespace LeanCloud.Proofs.ConcurrentAudit
open Lean Simulation SimulationBackend JournalAdapter ReplayRecovery

/-- Locate a published successor in any concrete chronological history. The
timeline covers both finite attempts and repeated polling iterations. -/
theorem PublishedStep.successor_at {logs : Nat → ConcurrentHandoff.Log}
    (timeline : History.Timeline logs) {tree current node atTime later locations}
    (valid : Valid tree (logs later))
    (published : PublishedStep tree current node (logs atTime) (.runnable locations) (logs later))
    {target : Location} (member : target ∈ locations) :
    ∃ issuedAt, ∃ slot : Nat, ∃ message : LeaseQueueModel.Message Location, atTime < issuedAt ∧ issuedAt ≤ later ∧
      (logs issuedAt).current.transport.messages[slot]? = some (some message) ∧ message.value = target := by
  obtain ⟨executed, began, finished, _progress, _emitted, publication⟩ := published
  obtain ⟨slot, issued, message, _fresh, _afterStep, recorded, held, value, newer⟩ :=
    ConcurrentHandoff.Published.fresh valid.2.1 finished.2 publication member
  have afterStart := Nat.lt_of_le_of_lt began.2.length newer
  obtain ⟨issuedAt, afterTime, beforeEnd, same⟩ := timeline.checkpoint_after later issued recorded atTime afterStart
  refine ⟨issuedAt, slot, message, afterTime, beforeEnd, ?_, value⟩
  rw [← same] at held
  exact held

/-- A published successor was retained at a real later boundary of this trace,
even when it was consumed before the publishing worker finished. Queue fairness
can be applied at that boundary instead of assuming the successor is still live. -/
theorem PublishedStep.successor {start : Fin count → SimM Durable α} {clock : Nat → Durable → Durable}
    (trace : Simulation.Trace start clock) {tree current node atTime later locations}
    (valid : Valid tree ((History.trace trace).states later).durable)
    (published : PublishedStep tree current node ((History.trace trace).states atTime).durable
      (.runnable locations) ((History.trace trace).states later).durable)
    {target : Location} (member : target ∈ locations) :
    ∃ issuedAt, ∃ slot : Nat, ∃ message : LeaseQueueModel.Message Location, atTime < issuedAt ∧ issuedAt ≤ later ∧
      (trace.states issuedAt).durable.transport.messages[slot]? = some (some message) ∧ message.value = target :=
  published.successor_at (History.trace_timeline trace) valid member

/-- Polling progress is shared by finite attempts and repeated iterations.
The selected continuation is derived from the actual queue operation. -/
theorem poll_scheduled {start : Fin count → SimM ConcurrentHandoff.Log (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → ConcurrentHandoff.Log → ConcurrentHandoff.Log} (trace : Simulation.Schedule start clock)
    (tree : ExecutionTree) (duration : Nat)
    (kept : ∀ n, Valid tree (trace.states n).durable)
    (growth : ∀ before after, before ≤ after →
      Grows (trace.states before).durable (trace.states after).durable)
    (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime) (handle : SimulationBackend.Worker)
    (next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (continuing : ((trace.states atTime).workers worker).Continues
      (History.program ((do
        let work ← (queue duration).next
        next work : ExceptT CloudError (StateT SimulationBackend.Worker M) α).run handle))) :
    ∃ later work handle, atTime < later ∧
      ((trace.states later).workers worker).Continues (History.program ((next work).run handle)) ∧
      ConcurrentQueue.Next tree (work, handle) (trace.states later).durable.current ∧
      ConcurrentHandoff.Polled (work, handle) (trace.states later).durable ∧
      (trace.states atTime).durable.past.length < (trace.states later).durable.past.length := by
  have progress := poll_reaches tree duration handle (trace.states atTime).durable
    (kept atTime) next _ continuing
  obtain ⟨later, after, work, handle, remaining, active, received, advanced⟩ :=
    trace.eventually_reaches fair worker
      Grows.refl (fun a b => a.trans b) kept growth progress atTime rfl
      noCrash (.refl _)
  have strictly : atTime < later := by
    by_cases same : atTime = later
    · subst later; exact False.elim (Nat.lt_irrefl _ advanced)
    · omega
  exact ⟨later, work, handle, strictly, remaining, active, received, advanced⟩

/-- Fairly scheduled polling reaches the actual code for its returned work.
An item carries its active route and a receipt from a real dequeue; idle and
already-completed replies are also allowed. The continuation may keep running.
The original interpreter supplies `kept` and `growth` through `trace_certified`. -/
theorem poll_continues {start : Fin count → M (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → Durable → Durable} (trace : Simulation.Trace start clock)
    (tree : ExecutionTree) (duration : Nat)
    (kept : ∀ n, Valid tree ((History.trace trace).states n).durable)
    (growth : ∀ before after, before ≤ after →
      Grows ((History.trace trace).states before).durable ((History.trace trace).states after).durable)
    (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime) (handle : SimulationBackend.Worker)
    (next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (continuing : (((History.trace trace).states atTime).workers worker).Continues
      (History.program ((do
        let work ← (queue duration).next
        next work : ExceptT CloudError (StateT SimulationBackend.Worker M) α).run handle))) :
    ∃ later work handle, atTime < later ∧
      (((History.trace trace).states later).workers worker).Continues (History.program ((next work).run handle)) ∧
      ConcurrentQueue.Next tree (work, handle) (trace.states later).durable ∧
      ConcurrentHandoff.Polled (work, handle) ((History.trace trace).states later).durable ∧
      ((History.trace trace).states atTime).durable.past.length < ((History.trace trace).states later).durable.past.length :=
  poll_scheduled (History.trace trace).schedule tree duration kept growth
    ((History.trace trace).schedule_fair (History.trace_fair trace fair)) worker atTime
    (fun n after same => noCrash n after (Option.some.inj same)) handle next continuing

/-- Unfold one polling iteration of the actual replay loop. The returned item
selects the actual step-and-publication continuation; it is not a promise that
the queue returns an item or that the remaining fuel is sufficient. -/
theorem run_polls [Codec α]
    {start : Fin count → M (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → Durable → Durable} (trace : Simulation.Trace start clock)
    (tree : ExecutionTree) (duration remaining : Nat) (program : Cloud M Json)
    (kept : ∀ n, Valid tree ((History.trace trace).states n).durable)
    (growth : ∀ before after, before ≤ after →
      Grows ((History.trace trace).states before).durable ((History.trace trace).states after).durable)
    (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime) (handle : SimulationBackend.Worker)
    (continuing : (((History.trace trace).states atTime).workers worker).Continues
      (History.program ((ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) (remaining + 1) program).run handle))) :
    let next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α := fun work =>
      match work with
      | .completed outcome => ReplayInterpreter.Internal.result outcome
      | .idle => ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs (queue duration) remaining program
      | .item location => do
        let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs (remaining + 1) program location
        (queue duration).complete location response
        match response with
        | .done outcome => ReplayInterpreter.Internal.result outcome
        | .runnable _ => ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs (queue duration) remaining program
    ∃ later work handle, atTime < later ∧
      (((History.trace trace).states later).workers worker).Continues (History.program ((next work).run handle)) ∧
      ConcurrentQueue.Next tree (work, handle) (trace.states later).durable ∧
      ConcurrentHandoff.Polled (work, handle) ((History.trace trace).states later).durable ∧
      ((History.trace trace).states atTime).durable.past.length < ((History.trace trace).states later).durable.past.length := by
  apply poll_continues trace tree duration kept growth fair worker atTime noCrash handle
  exact continuing

/-- A selected step reaches publication and the caller's next code. This
schedule-level proof applies unchanged when other workers repeat iterations. -/
theorem delivered_scheduled
    {start : Fin count → SimM ConcurrentHandoff.Log (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → ConcurrentHandoff.Log → ConcurrentHandoff.Log} (trace : Simulation.Schedule start clock)
    {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : route.prefixSteps + 1 ≤ traversal)
    (kept : ∀ n, Valid tree (trace.states n).durable)
    (growth : ∀ before after, before ≤ after → Grows (trace.states before).durable (trace.states after).durable)
    (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime)
    (receipt : LeaseQueueModel.Receipt)
    (active : route.Activated (ConcurrentJournal.view (trace.states atTime).durable.current))
    (received : ConcurrentHandoff.Received current receipt (trace.states atTime).durable)
    (next : StepResult → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (continuing : ((trace.states atTime).workers worker).Continues (History.program ((do
      let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs traversal program current
      (queue duration).complete current response
      next response).run ⟨(), some (current, receipt)⟩))) :
    ∃ later response, atTime ≤ later ∧
      ((trace.states later).workers worker).Continues (History.program ((next response).run ⟨(), none⟩)) ∧
      PublishedStep tree current node (trace.states atTime).durable response (trace.states later).durable := by
  have progress := delivered_continues whole supported route comparable sameExit duration traversal enough receipt
    (trace.states atTime).durable (kept atTime) active received next _ continuing
  obtain ⟨later, after, response, remaining, published⟩ := trace.eventually_reaches fair worker
    Grows.refl (fun a b => a.trans b) kept growth progress atTime rfl noCrash (.refl _)
  exact ⟨later, response, after, remaining, published⟩

/-- Fair worker actions carry a selected location through the actual step and
publication adapter after that worker's crashes stop. The `continuing` premise
identifies its current suspended code, not a successful response. Queue fairness
must still supply such selections; this theorem proves their subsequent progress. -/
theorem delivered_publishes [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat)
    (trace : Simulation.Trace (fun worker => attempt (fuel worker) duration program input) SimulationBackend.advance)
    (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
      (fun worker => attempt (fuel worker) duration program input))
    (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime)
    (current : Location) (node : ExecutionTree) (route : TreeRoute tree Location.root current node)
    (active : route.Activated (ConcurrentJournal.view (trace.states atTime).durable))
    (receipt : LeaseQueueModel.Receipt)
    (received : ConcurrentHandoff.Received current receipt ((History.trace trace).states atTime).durable)
    (traversal : Nat) (enough : route.prefixSteps + 1 ≤ traversal)
    (next : StepResult → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (continuing :
      let selected := do
        let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs traversal
          (codec.encode <$> program input) current
        (queue duration).complete current response
        next response
      (((History.trace trace).states atTime).workers worker).Continues
        (History.program (selected.run ⟨(), some (current, receipt)⟩))) :
    ∃ later response, atTime ≤ later ∧ PublishedStep tree current node
      ((History.trace trace).states atTime).durable response ((History.trace trace).states later).durable := by
  obtain ⟨kept, growth⟩ := trace_certified program input whole supported comparable sameExit duration fuel trace initialized
  obtain ⟨later, response, after, _remaining, published⟩ := delivered_scheduled (History.trace trace).schedule
    whole (supported.map codec.encode) route comparable (sameExit _ _ route.member) duration traversal enough kept growth
    ((History.trace trace).schedule_fair (History.trace_fair trace fair)) worker atTime
    (fun n beyond same => noCrash n beyond (Option.some.inj same)) receipt active received next continuing
  exact ⟨later, response, after, published⟩

/-- The pure workflow permits only finitely many immutable physical fields.
Concurrent retries can keep appending duplicate writes, but eventually the
visible journal is fixed. Queue state and the physical log may still change. -/
theorem journal_stable [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat)
    (trace : Simulation.Trace (fun worker => attempt (fuel worker) duration program input) SimulationBackend.advance)
    (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
      (fun worker => attempt (fuel worker) duration program input)) :
    ∃ cut, ∀ n, cut ≤ n →
      ConcurrentJournal.view (trace.states n).durable = ConcurrentJournal.view (trace.states cut).durable := by
  obtain ⟨kept, growth⟩ := trace_certified program input whole supported comparable sameExit duration fuel trace initialized
  apply finite_journal_stable (fun n => ConcurrentJournal.view (trace.states n).durable)
    ((tree.records Location.root).map Prod.fst)
  · intro before after later
    exact (growth before after later).1.journal.1
  · intro n key value recorded
    have bound := (kept n).1.journal key value recorded
    have member := (tree.journal_read_iff Location.root (by simp [Location.root]) key value).mp bound
    exact List.mem_map.mpr ⟨(key, value), member, rfl⟩

/-- Combine finite publication accounting with structural progress. An
unfinished initialized state cannot have all retained work belong to a set
closed under unfinished responses while the journal stays fixed. -/
theorem Valid.stable_complete {tree : ExecutionTree} {log : ConcurrentHandoff.Log}
    (valid : Valid tree log) (initialized : History.Grows ⟨SimulationBackend.initial, []⟩ log)
    (available : Location → Prop)
    (delivered : ∀ (slot : Nat) (message : LeaseQueueModel.Message Location),
      log.current.transport.messages[slot]? = some (some message) → available message.value)
    (responses : ConcurrentJournal.StableResponses tree log.current available) :
    log.current.completed = some tree.exit := by
  rcases valid.no_loss initialized with complete | ⟨slot, message, retained, outstanding⟩
  · exact complete
  · exact False.elim (outstanding (responses.reported message.value (delivered slot message retained)))

end LeanCloud.Proofs.ConcurrentAudit
