import LeanCloud.Proofs.BackendLeased
import LeanCloud.Proofs.BackendLineage

namespace LeanCloud.Backend.Proofs.Worker
open Lean LeanEff LeanCloud.Proofs

def completed (state : Backend.State) : Option Json := Backend.Db.view state CompletionStore.key

/-- Historical publications remain meaningful even after acknowledgement.
The final result is checked in the same Db as the location journal. -/
structure Valid (tree : ExecutionTree) (state : Backend.State) : Prop where
  journal : Journal.Valid (tree.journal Location.root) state
  messages : ∀ (id : Nat) (message : Backend.Message), state.queue.messages[id]? = some message →
    tree.Activated (Journal.view state) message.location
  completed : ∀ value, completed state = some value → value = toJson tree.exit
  ordered : Journal.Ordered state
  published : ∀ (id : Nat) (message : Backend.Message), state.queue.messages[id]? = some message →
    Journal.Grows message.published.state state

structure Grows (before after : Backend.State) : Prop where
  journal : Journal.Grows before after
  completed : ∀ value, completed before = some value → completed after = some value
  queue : QueueLineage before.queue after.queue

theorem Grows.refl (state : Backend.State) : Grows state state := ⟨.refl _, fun _ stored => stored, .refl _⟩

theorem Grows.trans {before middle after : Backend.State}
    (first : Grows before middle) (last : Grows middle after) : Grows before after :=
  ⟨first.journal.trans last.journal, fun value stored => last.completed value (first.completed value stored),
    first.queue.trans last.queue⟩

def Received (location : Location) (receipt : Receipt) (state : Backend.State) : Prop :=
  ∃ (id : Nat) (message : Backend.Message), state.queue.receipts[receipt]? = some id ∧
    state.queue.messages[id]? = some message ∧ message.location = location

theorem Received.grow {location receipt before after} (received : Received location receipt before)
    (growth : Grows before after) : Received location receipt after := by
  obtain ⟨id, message, receipt, stored, same⟩ := received
  obtain ⟨current, found, location, _⟩ := growth.queue.messages id message stored
  exact ⟨id, current, growth.queue.receipts _ _ receipt, found, location.trans same⟩

theorem Valid.initial (tree : ExecutionTree) : Valid tree Replay.initial := by
  constructor
  · intro key value stored
    simp [Journal.view, Backend.Db.view, Replay.initial] at stored
  · intro id message stored
    have same : message = { location := Location.root } := by
      have := Array.mem_of_getElem? stored
      simpa [Replay.initial] using this
    subst message
    exact ExecutionTree.Activated.root tree _
  · intro value stored
    cases stored
  · exact Journal.Ordered.initial _ rfl
  · intro id message stored
    have same : message = { location := Location.root } := by
      have := Array.mem_of_getElem? stored
      simpa [Replay.initial] using this
    subst message
    exact Journal.Grows.snapshot Replay.initial

private theorem queue_frame {tree before after} (valid : Valid tree before)
    (same : after.records = before.records)
    (past : after.pastRecords = before.pastRecords)
    (queue : QueueLineage before.queue after.queue)
    (messages : ∀ (id : Nat) (message : Backend.Message), after.queue.messages[id]? = some message →
      tree.Activated (Journal.view before) message.location ∧ Journal.Grows message.published.state before) :
    Valid tree after ∧ Grows before after := by
  have view : Journal.view after = Journal.view before := by
    funext key; simp [Journal.view, Backend.Db.view, same]
  have completion : completed after = completed before := by simp [completed, Backend.Db.view, same]
  have history : Journal.history after = Journal.history before := by simp [Journal.history, same, past]
  have journalGrowth : Journal.Grows before after :=
    ⟨fun key value stored => (congrFun view key).trans stored, by rw [history]; exact .refl _⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, journalGrowth, ?_, queue⟩
  · simpa only [Journal.Valid, view] using valid.journal
  · intro id message stored
    rw [view]
    exact (messages id message stored).1
  · intro value stored; exact valid.completed value (completion.symm.trans stored)
  · simpa only [Journal.Ordered, history] using valid.ordered
  · intro id message stored
    exact ((messages id message stored).2).trans journalGrowth
  · intro value stored; exact completion.trans stored

theorem enqueue_preserves {tree before after location value} (valid : Valid tree before)
    (active : tree.Activated (Journal.view before) location)
    (law : Commits before (.enqueue location) value after) : Valid tree after ∧ Grows before after := by
  obtain ⟨rfl, rfl⟩ := law
  refine queue_frame valid ?_ ?_ (.enqueue _ _) ?_
  · rfl
  · rfl
  intro id message stored
  rw [Array.getElem?_push] at stored
  split at stored
  · cases stored; exact ⟨active, Journal.Grows.snapshot before⟩
  · exact ⟨valid.messages id message stored, valid.published id message stored⟩

theorem dequeue_preserves {tree before after value} (valid : Valid tree before)
    (law : Commits before .dequeue value after) :
    Valid tree after ∧ Grows before after ∧
      ∀ location receipt, value = some (location, receipt) →
        tree.Activated (Journal.view after) location ∧ Received location receipt after := by
  cases value with
  | none =>
    have same : after = before := law
    subst after
    exact ⟨valid, .refl _, by simp⟩
  | some pair =>
    rcases pair with ⟨location, receipt⟩
    obtain ⟨id, message, stored, rfl, rfl, rfl⟩ := law
    have framed := queue_frame (after := { before with queue.receipts := before.queue.receipts.push id })
      valid rfl rfl (.receive _ _) (fun id message stored =>
        ⟨valid.messages id message stored, valid.published id message stored⟩)
    refine ⟨framed.1, framed.2, ?_⟩
    intro _ _ equal
    cases equal
    exact ⟨valid.messages id message stored, id, message, by simp, stored, rfl⟩

theorem acknowledge_preserves {tree before after receipt value} (valid : Valid tree before)
    (law : Commits before (.acknowledge receipt) value after) : Valid tree after ∧ Grows before after := by
  cases value with
  | false =>
    have same : after = before := law
    subst after
    exact ⟨valid, .refl _⟩
  | true =>
    obtain ⟨id, message, received, stored, rfl⟩ := law
    refine queue_frame valid ?_ ?_ (.acknowledge _ _ _ stored) ?_
    · rfl
    · rfl
    intro other actual found
    rw [Array.getElem?_setIfInBounds] at found
    split at found
    · split at found
      · cases found; exact ⟨valid.messages id message stored, valid.published id message stored⟩
      · cases found
    · exact ⟨valid.messages other actual found, valid.published other actual found⟩

theorem journal_commit {tree : ExecutionTree} {α : Type} {operation : Request α}
    (only : Footprint.JournalOnly operation) {before after value}
    (valid : Valid tree before) (law : Commits before operation value after)
    (kept : Journal.Valid (tree.journal Location.root) after)
    (growth : Journal.Grows before after) : Valid tree after ∧ Grows before after := by
  have frames : after.queue = before.queue ∧ completed after = completed before := by
    cases operation with
    | get key => obtain ⟨_, rfl⟩ := law; exact ⟨rfl, rfl⟩
    | put key stored =>
      cases value with
      | false => obtain ⟨_, rfl⟩ := law; exact ⟨rfl, rfl⟩
      | true =>
        obtain ⟨_, unchanged, queue, _⟩ := law
        exact ⟨queue, unchanged CompletionStore.key (Ne.symm only)⟩
    | enqueue _ | dequeue | acknowledge _ => cases only
  have ordered : Journal.Ordered after := by
    cases operation with
    | get key => obtain ⟨_, rfl⟩ := law; exact valid.ordered
    | put key stored =>
      cases value with
      | false => obtain ⟨_, rfl⟩ := law; exact valid.ordered
      | true => exact valid.ordered.write growth law.2.2.2
    | enqueue _ | dequeue | acknowledge _ => cases only
  exact ⟨⟨kept,
    fun id message stored => (valid.messages id message (by simpa [frames.1] using stored)).grow growth,
    fun value stored => valid.completed value (frames.2.symm.trans stored), ordered,
    fun id message stored => (valid.published id message (by simpa [frames.1] using stored)).trans growth⟩,
    growth, (fun value stored => frames.2.trans stored), commits_lineage law⟩

theorem step_safe {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true)
    (state : Backend.State) (valid : Valid tree state)
    (active : route.Activated (Journal.view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel)
    (worker : Replay.Worker) :
    ProgramSafe (Valid tree) Grows
      (fun returned final => ∃ response, returned = .ok (.ok response, worker) ∧
        Journal.Emits tree response final ∧ Journal.StepProgress tree current node state response final)
      (((ReplayInterpreter.Internal.step Replay.db Replay.noBlobs fuel program current).run worker).run) state := by
  apply (Journal.leased_step_checked whole supported route comparable sameExit state valid.journal
    active fuel enough worker).refine Footprint.JournalOnly (Footprint.step fuel program supported current worker)
      (fun _ h => h.journal) (fun h => h.journal)
  exact fun operation only before value after valid law kept growth => journal_commit only valid law kept growth

end LeanCloud.Backend.Proofs.Worker
