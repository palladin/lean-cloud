import LeanCloud.Proofs.BackendPublication

/-! Completion follows from finite pure structure, actual publication-before-
acknowledgement, fair consumer demand and eventual recovery. No service contract
mentions the workflow result or assumes a successful replay step. -/

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs Execution

private def Fresh (trace : Trace traversal source count) (cut : Nat) (location : Location) : Prop :=
  ∃ (time id : Nat) (message : Backend.Message), cut ≤ time ∧ (trace.states time).services.queue.messages[id]? = some message ∧
    message.location = location ∧ Journal.Grows (trace.states cut).services message.published.state

variable {source : Cloud Replay.M Json} {tree : ExecutionTree}
  (whole : Expansion source tree) (supported : PureProgram source)
  (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
  (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
  (traversal : Nat) (enough : sizeOf tree ≤ traversal)
  (trace : Trace traversal source count)
  (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
  (fair : trace.schedule.WeaklyFair) (deliveries : trace.FairDelivery)
  (demand : PollingForever trace.states trace.schedule.events) (cut : Nat)
  (noCrash : ∀ worker, trace.schedule.NoCrashesAfter worker cut) (live : trace.LiveCommits cut)
  (fixed : ∀ n, cut ≤ n → Journal.view (trace.states n).services = Journal.view (trace.states cut).services)
  (unfinished : ∀ n, Worker.completed (trace.states n).services ≠ some (toJson tree.exit))

include fixed in
private theorem checkpoint_fixed (n : Nat) (beyond : cut ≤ n) (checkpoint : Backend.State)
    (begun : Journal.Grows (trace.states cut).services checkpoint)
    (recorded : Journal.Grows checkpoint (trace.states n).services) :
    Journal.view checkpoint = Journal.view (trace.states cut).services := by
  have later : JournalAdapter.Extends (Journal.view checkpoint) (Journal.view (trace.states n).services) := recorded.reads
  rw [fixed n beyond] at later
  exact later.antisymm begun.reads


include whole supported comparable sameExit enough initialized fixed unfinished in
private theorem stable_response (n : Nat) (beyond : cut ≤ n) (before after : Backend.State) (response : StepResult)
    (begun : Journal.Grows (trace.states cut).services before) (executed : Worker.Grows before after)
    (recorded : Worker.Grows after (trace.states n).services)
    (stored : Worker.FinalStored response (trace.states n).services)
    (successors : Accounting.Successors after response (trace.states n).services) :
    ∃ locations, response = .runnable locations ∧
      Journal.view before = Journal.view (trace.states cut).services ∧
      Journal.view after = Journal.view (trace.states cut).services ∧
      ∀ target ∈ locations, Fresh trace cut target := by
  cases response with
  | done outcome =>
    obtain ⟨kept, _⟩ := certified whole supported comparable sameExit traversal enough trace initialized
    have same := (kept n).services.safety.completed (toJson outcome) stored
    exact False.elim (unfinished n (stored.trans (congrArg some same)))
  | runnable locations =>
    refine ⟨locations, rfl,
      checkpoint_fixed traversal trace cut fixed n beyond before begun (executed.journal.trans recorded.journal),
      checkpoint_fixed traversal trace cut fixed n beyond after (begun.trans executed.journal) recorded.journal, ?_⟩
    intro target member
    obtain ⟨id, message, fresh, held, same, born⟩ := successors target member
    exact ⟨n, id, message, beyond, held, same, begun.trans (executed.journal.trans born)⟩

include whole supported comparable sameExit enough initialized fair deliveries demand noCrash live in
private theorem fresh_response {location} (available : Fresh trace cut location) :
    ∃ n node before after response, ∃ _route : TreeRoute tree Location.root location node,
      cut ≤ n ∧ Journal.Grows (trace.states cut).services before ∧ Worker.Grows before after ∧
      Worker.Grows after (trace.states n).services ∧ Worker.Valid tree after ∧
      Journal.StepProgress tree location node before response after ∧ Journal.Emits tree response after ∧
      Worker.FinalStored response (trace.states n).services ∧ Accounting.Successors after response (trace.states n).services := by
  obtain ⟨atTime, id, message, beyond, held, payload, born⟩ := available
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  rcases fair_delivery whole supported comparable sameExit traversal enough trace initialized fair deliveries demand atTime
    (fun worker n after => noCrash worker n (by omega))
    (fun n after => live n (by omega)) id message held with settled | processed
  · obtain ⟨n, current, later, stored, acknowledged⟩ := settled
    obtain ⟨actual, found, same, birth, _⟩ := (growth atTime n later).queue.messages id message held
    have equal := Option.some.inj (stored.symm.trans found)
    subst actual
    have retired := (kept n).services.retired id current stored acknowledged
    rw [same, birth, payload] at retired
    obtain ⟨node, before, after, response, route, began, executed, recorded, inside, valid, emitted,
      progress, final, successors⟩ := retired
    exact ⟨n, node, before, after, response, route, by omega, born.trans began,
      executed, recorded, valid, progress, emitted, final, successors⟩
  · obtain ⟨start, node, route, n, response, later, afterTime, after, executed, recorded,
      valid, progress, emitted, stored, successors⟩ := processed
    rw [payload] at route progress
    exact ⟨n, node, (trace.states start).services, after, response, route, by omega,
      (growth cut start (by omega)).journal, executed, recorded, valid, progress, emitted, stored, successors⟩

include whole supported comparable sameExit enough initialized fair deliveries demand noCrash live fixed unfinished in
private theorem fresh_responses : Journal.StableResponses tree (trace.states cut).services (Fresh trace cut) := by
  intro location available
  obtain ⟨n, node, before, after, response, route, beyond, begun, executed, recorded,
    valid, progress, emitted, stored, successors⟩ :=
      fresh_response whole supported comparable sameExit traversal enough trace initialized fair deliveries demand cut noCrash live available
  obtain ⟨locations, same, first, last, fresh⟩ := stable_response whole supported comparable sameExit traversal enough trace initialized
    cut fixed unfinished n beyond before after response begun executed recorded stored successors
  subst response
  exact ⟨node, route, before, after, locations, first, last, executed.journal, valid.ordered, progress, emitted, fresh⟩

include whole supported comparable sameExit enough initialized fair deliveries demand noCrash live fixed unfinished in
private theorem processed_reported {start n location node response}
    (afterCut : cut ≤ start) (later : start ≤ n)
    (published : Published tree location node (trace.states start).services response (trace.states n).services) :
    Journal.OpenReport location (trace.states cut).services (trace.states cut).services := by
  obtain ⟨_, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  obtain ⟨after, executed, recorded, valid, progress, emitted, stored, successors⟩ := published
  obtain ⟨locations, same, first, last, fresh⟩ := stable_response whole supported comparable sameExit traversal enough trace initialized
    cut fixed unfinished n (by omega) (trace.states start).services after response (growth cut start afterCut).journal
    executed recorded stored successors
  subst response
  have responses := fresh_responses whole supported comparable sameExit traversal enough trace initialized fair deliveries demand cut noCrash live fixed unfinished
  have report := progress.open_report valid.ordered (.refl _) executed.journal (.refl _)
    (by intro outcome impossible; cases impossible) (by
      intro children same target member
      cases same
      exact (responses.reported target (fresh target member)).fixed last.symm last.symm)
  exact report.fixed first last

include whole supported comparable sameExit enough initialized fair deliveries demand noCrash live fixed unfinished in
private theorem old_settles (id : Nat) (inside : id < (trace.states cut).services.queue.messages.size) :
    ∃ atTime, cut ≤ atTime ∧ ∀ later, atTime ≤ later → ∀ message : Backend.Message,
      (trace.states later).services.queue.messages[id]? = some message →
      message.acknowledged = true ∨ Journal.OpenReport message.location (trace.states cut).services (trace.states cut).services := by
  obtain ⟨_, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  let message := (trace.states cut).services.queue.messages[id]
  have stored : (trace.states cut).services.queue.messages[id]? = some message := Array.getElem?_eq_getElem inside
  rcases fair_delivery whole supported comparable sameExit traversal enough trace initialized fair deliveries demand cut noCrash live id message stored with settled | processed
  · obtain ⟨atTime, current, afterCut, held, acked⟩ := settled
    refine ⟨atTime, afterCut, ?_⟩
    intro later after message found
    obtain ⟨actual, stored, payload, birth, persisted⟩ := (growth atTime later after).queue.messages id current held
    have same := Option.some.inj (found.symm.trans stored)
    subst actual
    exact .inl (persisted acked)
  · obtain ⟨start, node, route, n, response, afterCut, later, published⟩ := processed
    have report := processed_reported whole supported comparable sameExit traversal enough trace initialized
      fair deliveries demand cut noCrash live fixed unfinished (Nat.le_of_lt afterCut) later published
    refine ⟨cut, Nat.le_refl _, ?_⟩
    intro later after current held
    obtain ⟨actual, found, payload, _⟩ := (growth cut later after).queue.messages id message stored
    have same := Option.some.inj (held.symm.trans found)
    subst actual
    exact .inr (by simpa [payload] using report)

include whole supported comparable sameExit enough initialized fair deliveries demand noCrash live fixed unfinished in
private theorem stable_unfinished_impossible : False := by
  let size := (trace.states cut).services.queue.messages.size
  have bounded (limit : Nat) (within : limit ≤ size) :
      ∃ atTime, cut ≤ atTime ∧ ∀ id, id < limit → ∀ later, atTime ≤ later → ∀ message : Backend.Message,
        (trace.states later).services.queue.messages[id]? = some message →
        message.acknowledged = true ∨ Journal.OpenReport message.location (trace.states cut).services (trace.states cut).services := by
    induction limit with
    | zero => exact ⟨cut, Nat.le_refl _, by intro id impossible; omega⟩
    | succ limit ih =>
      obtain ⟨first, afterFirst, previous⟩ := ih (by omega)
      obtain ⟨last, afterLast, latest⟩ := old_settles whole supported comparable sameExit traversal enough trace initialized
        fair deliveries demand cut noCrash live fixed unfinished limit (by dsimp [size] at within; omega)
      refine ⟨max first last, by omega, ?_⟩
      intro id inside later after message held
      by_cases earlier : id < limit
      · exact previous id earlier later (by omega) message held
      · have same : id = limit := by omega
        subst id
        exact latest later (by omega) message held
  obtain ⟨time, afterCut, older⟩ := bounded size (Nat.le_refl _)
  have responses := fresh_responses whole supported comparable sameExit traversal enough trace initialized
    fair deliveries demand cut noCrash live fixed unfinished
  rcases no_loss whole supported comparable sameExit traversal enough trace initialized time with completed | outstanding
  · exact unfinished time completed
  · obtain ⟨id, message, stored, unsettled, unreported⟩ := outstanding
    have reported : Journal.OpenReport message.location (trace.states cut).services (trace.states cut).services := by
      by_cases old : id < size
      · rcases older id old time (Nat.le_refl _) message stored with acked | report
        · rw [unsettled] at acked; cases acked
        · exact report
      · have born := publications_after whole supported comparable sameExit traversal enough trace initialized
          afterCut id message stored (by dsimp [size] at old; omega)
        exact responses.reported message.location ⟨time, id, message, afterCut, stored, rfl, born⟩
    have same := fixed time afterCut
    exact unreported (reported.fixed same.symm same.symm)

include whole supported comparable sameExit enough initialized deliveries in
/-- The shared Db/queue/restart model eventually records the direct outcome.
Journal stabilization, continued polling, useful delivery and successful
publication are all derived from the actual interpreter. -/
theorem eventually_completed (fairWorkers : trace.WeaklyFair) (nonempty : 0 < count)
    (recoveryCut : Nat) (recovered : ∀ worker, trace.schedule.NoCrashesAfter worker recoveryCut) :
    ∃ time, Worker.completed (trace.states time).services = some (toJson tree.exit) := by
  classical
  apply Classical.byContradiction
  intro never
  have unfinished time : Worker.completed (trace.states time).services ≠ some (toJson tree.exit) :=
    fun present => never ⟨time, present⟩
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  obtain ⟨journalCut, stable⟩ := Journal.eventually_stable tree (fun n => (trace.states n).services)
    (fun n => (kept n).services.safety.journal) (fun first last later => (growth first last later).journal)
  obtain ⟨liveCut, afterRecovery, live⟩ := trace.eventually_live_commits recoveryCut recovered
  let settled := max journalCut liveCut
  have stopped worker : trace.schedule.NoCrashesAfter worker settled :=
    fun n later => recovered worker n (by dsimp [settled] at later; omega)
  have liveAfter : trace.LiveCommits settled := fun n beyond => live n (by dsimp [settled] at beyond; omega)
  have fixed n (later : settled ≤ n) : Journal.view (trace.states n).services = Journal.view (trace.states settled).services :=
    (stable n (by dsimp [settled] at later; omega)).trans (stable settled (by dsimp [settled]; omega)).symm
  have demand := polling_forever whole supported comparable sameExit traversal enough trace initialized fairWorkers nonempty recoveryCut recovered unfinished
  exact stable_unfinished_impossible whole supported comparable sameExit traversal enough trace initialized fairWorkers.workers
    deliveries demand settled stopped liveAfter fixed unfinished

end LeanCloud.Backend.Proofs.Iteration
