import LeanCloud.Proofs.ConcurrentDelivery

/-! Fair delivery closes the progress argument for repeated real workers.
After journal stabilization, fresh slots form a closed set of decreasing work.
The finitely many older slots are eventually removed or report to an open group.
No-loss then rules out an unfinished execution. -/

namespace LeanCloud.Proofs.ConcurrentRepeated
open Lean Simulation SimulationBackend ReplayRecovery ConcurrentAudit
open ConcurrentHandoff (Log)

private def FreshWork (trace : RawTrace duration traversal program count) (cut : Nat) (location : Location) : Prop :=
  ∃ atTime slot, ∃ message : LeaseQueueModel.Message Location, cut ≤ atTime ∧
    (trace.states cut).durable.transport.messages.size ≤ slot ∧
    (trace.states atTime).durable.transport.messages[slot]? = some (some message) ∧ message.value = location

variable {program : Cloud M Json} {tree : ExecutionTree}
  (whole : Expansion program tree) (supported : PureProgram program)
  (comparable : Comparable (tree.journal Location.root))
  (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
  (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
  (trace : RawTrace duration traversal program count)
  (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
    (fun _ : Fin count => rawIteration duration traversal program))
  (fair : trace.WeaklyFair) (deliveries : FairDelivery trace) (cut : Nat)
  (noCrash : ∀ worker, trace.NoCrashesAfter worker cut)
  (fixed : ∀ n, cut ≤ n →
    ConcurrentJournal.view (trace.states n).durable = ConcurrentJournal.view (trace.states cut).durable)
  (unfinished : ∀ n, (trace.states n).durable.completed ≠ some tree.exit)

include whole supported comparable sameExit enough initialized
include fixed

/-- A checkpoint between two fixed visible journals has that same journal. -/
private theorem checkpoint_fixed (n : Nat) (afterCut : cut ≤ n) (checkpoint : Log)
    (afterStart : History.Grows ((recordTrace trace).states cut).durable checkpoint)
    (recorded : History.Grows checkpoint ((recordTrace trace).states n).durable) :
    ConcurrentJournal.view checkpoint.current = ConcurrentJournal.view (trace.states cut).durable := by
  obtain ⟨kept, _⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  have before := ((kept n).1.growth afterStart recorded).journal.1
  have after := ((kept n).1.growth recorded (.refl _)).journal.1
  change JournalAdapter.Extends (ConcurrentJournal.view checkpoint.current) (ConcurrentJournal.view (trace.states n).durable) at after
  rw [fixed n afterCut] at after
  exact after.antisymm before

include unfinished

/-- Publication in the stable suffix yields runnable successors at fresh real
queue slots. A final-result publication contradicts the unfinished hypothesis. -/
private theorem stable_response (n : Nat) (afterCut : cut ≤ n)
    (before after : Log) (response : StepResult)
    (started : History.Grows ((recordTrace trace).states cut).durable before)
    (executed : History.Grows before after)
    (recorded : History.Grows after ((recordTrace trace).states n).durable)
    (published : ConcurrentHandoff.Published after.past.length response ((recordTrace trace).states n).durable) :
    ∃ locations, response = .runnable locations ∧
      ConcurrentJournal.view before.current = ConcurrentJournal.view (trace.states cut).durable ∧
      ConcurrentJournal.view after.current = ConcurrentJournal.view (trace.states cut).durable ∧
      ConcurrentJournal.Grows before.current after.current ∧
      ConcurrentJournal.Emits tree (.runnable locations) after.current ∧
      ∀ target ∈ locations, FreshWork trace cut target := by
  obtain ⟨kept, _⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  cases response with
  | done outcome =>
    have completed := (kept n).1.published_done (.refl _) published
    have same := (kept n).1.1.completed outcome completed
    exact False.elim (unfinished n (completed.trans (congrArg some same)))
  | runnable locations =>
    have first := checkpoint_fixed whole supported comparable sameExit duration traversal enough trace initialized
      cut fixed n afterCut before started (executed.trans recorded)
    have last := checkpoint_fixed whole supported comparable sameExit duration traversal enough trace initialized
      cut fixed n afterCut after (started.trans executed) recorded
    have emitted (target : Location) (member : target ∈ locations) :
        tree.Activated (ConcurrentJournal.view after.current) target ∧ FreshWork trace cut target := by
      obtain ⟨slot, issued, message, fresh, later, logged, held, value, newer⟩ :=
        ConcurrentHandoff.Published.fresh (kept n).1.2.1 recorded published member
      have offset := (started.trans executed).length
      obtain ⟨issuedAt, afterTime, beforeEnd, same⟩ := (History.repeated_trace_timeline trace).checkpoint_after
        n issued logged cut (Nat.lt_of_le_of_lt offset newer)
      have checkpointSize := ((kept n).1.2.1.earlier recorded).lineage (started.trans executed)
      have freshAtCut : (trace.states cut).durable.transport.messages.size ≤ slot :=
        Nat.le_trans checkpointSize.size fresh
      have actual : (trace.states issuedAt).durable.transport.messages[slot]? = some (some message) := by
        rw [← same] at held
        exact held
      have active := (kept issuedAt).1.1.pending slot message actual
      change tree.Activated (ConcurrentJournal.view (trace.states issuedAt).durable) message.value at active
      rw [value, fixed issuedAt (by omega), ← last] at active
      exact ⟨active, issuedAt, slot, message, by omega, freshAtCut, actual, value⟩
    refine ⟨locations, rfl, first, last, ((kept n).1.growth executed recorded).journal, ?_, ?_⟩
    · exact fun target member => (emitted target member).1
    · exact fun target member => (emitted target member).2

include fair deliveries noCrash unfinished

omit fixed in
/-- A fresh slot cannot have been processed before the stable checkpoint.
Fair delivery either obtains a new step or finds an already-published removal. -/
private theorem fresh_response {location : Location} (available : FreshWork trace cut location) :
    ∃ n node before after response, ∃ _route : TreeRoute tree Location.root location node,
      cut ≤ n ∧ History.Grows ((recordTrace trace).states cut).durable before ∧
      History.Grows before after ∧ History.Grows after ((recordTrace trace).states n).durable ∧
      ConcurrentJournal.StepProgress tree location node before.current response after.current ∧
      ConcurrentHandoff.Published after.past.length response ((recordTrace trace).states n).durable := by
  obtain ⟨availableAt, slot, message, beyond, fresh, stored, value⟩ := available
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  rcases fair_delivery whole supported comparable sameExit duration traversal enough trace initialized fair deliveries
    availableAt (fun worker n later => noCrash worker n (by omega)) slot message stored with done | removed | processed
  · obtain ⟨n, _, completed⟩ := done
    exact False.elim (unfinished n completed)
  · obtain ⟨n, later, absent⟩ := removed
    rcases (kept n).1.work_accounted (growth availableAt n later).2 stored with live | retired
    · obtain ⟨current, held, _⟩ := live
      change (trace.states n).durable.transport.messages[slot]? = some (some current) at held
      rw [absent] at held
      cases held
    · obtain ⟨response, node, before, after, acknowledged, route, executed, ended, recorded, inside, progress, published⟩ := retired
      have began := (BeforeSlot.fresh (kept n).1 (growth cut n (by omega)).2 fresh).2
        before (executed.trans (ended.trans recorded)) inside
      rw [value] at route progress
      exact ⟨n, node, before, after, response, route, by omega, began, executed,
        ended.trans recorded, progress, published.grow recorded⟩
  · obtain ⟨started, node, route, n, response, newer, later, after, began, ended, progress, _emitted, published⟩ := processed
    rw [value] at route progress
    exact ⟨n, node, ((recordTrace trace).states started).durable, after, response, route, by omega,
      (growth cut started (by omega)).2, began.2, ended.2, progress, published⟩

private theorem fresh_responses :
    ConcurrentJournal.StableResponses tree (trace.states cut).durable (FreshWork trace cut) := by
  intro location available
  obtain ⟨n, node, before, after, response, route, beyond, began, executed, recorded, progress, published⟩ :=
    fresh_response whole supported comparable sameExit duration traversal enough trace initialized fair deliveries cut noCrash unfinished available
  obtain ⟨locations, same, first, last, growth, emitted, successors⟩ :=
    stable_response whole supported comparable sameExit duration traversal enough trace initialized cut fixed unfinished
      n beyond before after response began executed recorded published
  subst response
  exact ⟨node, route, before.current, after.current, locations, first, last, growth, progress, emitted, successors⟩

/-- Even an older slot reports to an open group if a later delivery processes
it in the stable suffix: its emitted work belongs to the fresh closed set. -/
private theorem processed_reported {started n current node response}
    (afterCut : cut ≤ started) (later : started ≤ n)
    (publishedStep : PublishedStep tree current node ((recordTrace trace).states started).durable
      response ((recordTrace trace).states n).durable) :
    ConcurrentJournal.OpenReport current (trace.states cut).durable (trace.states cut).durable := by
  obtain ⟨_, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  obtain ⟨after, began, ended, progress, _emitted, published⟩ := publishedStep
  obtain ⟨locations, same, first, last, executed, _emitted, successors⟩ :=
    stable_response whole supported comparable sameExit duration traversal enough trace initialized cut fixed unfinished
      n (by omega) ((recordTrace trace).states started).durable after response (growth cut started afterCut).2 began.2 ended.2 published
  subst response
  have responses := fresh_responses whole supported comparable sameExit duration traversal enough trace initialized
    fair deliveries cut noCrash fixed unfinished
  have report := progress.open_report (.refl _) executed (.refl _)
    (by intro outcome impossible; cases impossible) (by
      intro children same target member
      cases same
      exact (responses.reported target (successors target member)).fixed last.symm last.symm)
  exact report.fixed first last

/-- Each of the finitely many slots present at the cut is eventually absent,
or every retained copy of its payload already reports to an open group. -/
private theorem old_settles (slot : Nat) (inside : slot < (trace.states cut).durable.transport.messages.size) :
    ∃ atTime, cut ≤ atTime ∧ ∀ later, atTime ≤ later → ∀ message : LeaseQueueModel.Message Location,
      (trace.states later).durable.transport.messages[slot]? = some (some message) →
      ConcurrentJournal.OpenReport message.value (trace.states cut).durable (trace.states cut).durable := by
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  have lineage before after (later : before ≤ after) :
      LeaseQueue.Lineage (trace.states before).durable.transport (trace.states after).durable.transport :=
    (kept after).1.2.1.lineage (growth before after later).2
  cases stored : (trace.states cut).durable.transport.messages[slot]? with
  | none => have outside := Array.getElem?_eq_none_iff.mp stored; omega
  | some item =>
    cases item with
    | none =>
      refine ⟨cut, Nat.le_refl _, ?_⟩
      intro later after message held
      obtain ⟨previous, present, _⟩ := (lineage cut later after).retained slot message inside held
      rw [stored] at present
      cases present
    | some message =>
      rcases fair_delivery whole supported comparable sameExit duration traversal enough trace initialized fair deliveries
        cut noCrash slot message stored with completed | removed | processed
      · obtain ⟨n, _, done⟩ := completed
        exact False.elim (unfinished n done)
      · obtain ⟨atTime, afterCut, absent⟩ := removed
        refine ⟨atTime, afterCut, ?_⟩
        intro later after message held
        have stillInside := Nat.lt_of_lt_of_le inside (lineage cut atTime afterCut).size
        obtain ⟨previous, present, _⟩ := (lineage atTime later after).retained slot message stillInside held
        rw [absent] at present
        cases present
      · obtain ⟨started, node, route, n, response, afterCut, later, published⟩ := processed
        have reported := processed_reported whole supported comparable sameExit duration traversal enough trace initialized
          fair deliveries cut noCrash fixed unfinished (Nat.le_of_lt afterCut) later published
        refine ⟨cut, Nat.le_refl _, ?_⟩
        intro later after current held
        obtain ⟨previous, present, payload⟩ := (lineage cut later after).retained slot current inside held
        rw [stored] at present
        cases present
        rwa [← payload]

private theorem stable_unfinished_impossible : False := by
  let size := (trace.states cut).durable.transport.messages.size
  have bounded (limit : Nat) (within : limit ≤ size) :
      ∃ atTime, cut ≤ atTime ∧ ∀ slot, slot < limit → ∀ later, atTime ≤ later → ∀ message : LeaseQueueModel.Message Location,
        (trace.states later).durable.transport.messages[slot]? = some (some message) →
        ConcurrentJournal.OpenReport message.value (trace.states cut).durable (trace.states cut).durable := by
    induction limit with
    | zero => exact ⟨cut, Nat.le_refl _, by intro slot impossible; omega⟩
    | succ limit ih =>
      obtain ⟨first, afterFirst, previous⟩ := ih (by omega)
      obtain ⟨last, afterLast, latest⟩ := old_settles whole supported comparable sameExit duration traversal enough trace initialized
        fair deliveries cut noCrash fixed unfinished limit (by dsimp [size] at within; omega)
      refine ⟨max first last, by omega, ?_⟩
      intro slot inside later after message held
      by_cases earlier : slot < limit
      · exact previous slot earlier later (by omega) message held
      · have same : slot = limit := by omega
        subst slot
        exact latest later (by omega) message held
  obtain ⟨atTime, afterCut, older⟩ := bounded size (Nat.le_refl _)
  have fresh := fresh_responses whole supported comparable sameExit duration traversal enough trace initialized
    fair deliveries cut noCrash fixed unfinished
  rcases no_loss whole supported comparable sameExit duration traversal enough (recordTrace trace)
    (History.repeated_trace_initial trace SimulationBackend.initial initialized) atTime with completed | outstanding
  · exact unfinished atTime completed
  · obtain ⟨slot, message, stored, unreported⟩ := outstanding
    have reported : ConcurrentJournal.OpenReport message.value (trace.states cut).durable (trace.states cut).durable := by
      by_cases old : slot < size
      · exact older slot old atTime (Nat.le_refl _) message stored
      · exact fresh.reported message.value ⟨atTime, slot, message, afterCut, by omega, stored, rfl⟩
    have same := fixed atTime afterCut
    exact unreported (reported.fixed same.symm same.symm)

omit fixed unfinished in
/-- Fair queue commits and worker actions eventually make the correct final
outcome durable once crashes stop. Journal stabilization and the elimination
of unfinished work are derived, rather than supplied as fairness premises. -/
theorem eventually_completed : ∃ n, (trace.states n).durable.completed = some tree.exit := by
  classical
  apply Classical.byContradiction
  intro never
  obtain ⟨journalCut, stable⟩ := journal_stable whole supported comparable sameExit duration traversal enough trace initialized
  let settled := max cut journalCut
  have stopped worker : trace.NoCrashesAfter worker settled := fun n later => noCrash worker n (by dsimp [settled] at later; omega)
  have fixed n (later : settled ≤ n) :
      ConcurrentJournal.view (trace.states n).durable = ConcurrentJournal.view (trace.states settled).durable :=
    (stable n (by dsimp [settled] at later; omega)).trans (stable settled (by dsimp [settled]; omega)).symm
  exact stable_unfinished_impossible whole supported comparable sameExit duration traversal enough trace initialized
    fair deliveries settled stopped fixed (fun n present => never ⟨n, present⟩)

omit fixed unfinished in
/-- The actual repeated workers both persist and observe the expected result.
This is liveness of the repeated model; ConcurrentRealization proves the
connection to the finite-fuel interpreter. -/
theorem eventually_returns (worker : Fin count) :
    ∃ later, cut ≤ later ∧
      ((trace.states later).workers worker).outcome? = some (.ok (some tree.exit), ⟨(), none⟩) ∧
      (trace.states later).durable.completed = some tree.exit := by
  obtain ⟨completedAt, recorded⟩ := eventually_completed whole supported comparable sameExit duration traversal enough trace initialized
    fair deliveries cut noCrash
  obtain ⟨_, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  let ready := max cut completedAt
  have present := (growth completedAt ready (by dsimp [ready]; omega)).1.completed tree.exit recorded
  obtain ⟨later, after, returned⟩ := completed_returns whole supported comparable sameExit duration traversal enough trace initialized
    fair worker ready (fun n beyond => noCrash worker n (by dsimp [ready] at beyond; omega)) present
  exact ⟨later, by dsimp [ready] at after; omega, returned,
    (growth ready later after).1.completed tree.exit present⟩

end LeanCloud.Proofs.ConcurrentRepeated
