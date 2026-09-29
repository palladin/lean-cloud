import LeanCloud.Proofs.TreeCoverage
import LeanCloud.Proofs.LeasePublication
import LeanCloud.Proofs.CrashSpec

/-! The transport side of workflow coverage. Polling and lease expiry retain
messages; acknowledgement may remove only its incoming slot, after publication.
Worker preservation of the tree invariant is a separate proof obligation. -/

namespace LeanCloud.Proofs.LeasePublication
open Lean LeaseQueueModel CrashModel CrashRecovery

/-- Presence includes leased and currently invisible messages. -/
def Pending (state : Durable) (location : Location) : Prop :=
  ∃ message, some message ∈ state.transport.messages ∧ message.value = location

def Covered (tree : ExecutionTree) (journal : Journal) (state : Durable) : Prop :=
  Coverage journal (Pending state) tree Location.root (state.completed = some tree.exit)

theorem Covered.initial (tree : ExecutionTree) (journal : Journal) :
    Covered tree journal (enqueueOp Location.root {}) := by
  apply Coverage.queued (source := Location.root) _ (.here _)
  exact ⟨⟨Location.root, 0, 0⟩, by simp [enqueueOp, LeaseQueueModel.enqueue], rfl⟩

theorem Pending.enqueued {state location} (present : Pending state location) (locations : List Location) :
    Pending (enqueued locations state) location := by
  obtain ⟨message, member, value⟩ := present
  exact ⟨message, Array.mem_append_left _ member, value⟩

theorem Covered.enqueued {tree journal state} (covered : Covered tree journal state) (locations : List Location) :
    Covered tree journal (enqueued locations state) :=
  covered.mono_work (fun _ present => present.enqueued locations)

/-- Leasing changes the selected slot's receipt and visibility, but preserves
every location that can witness unfinished work. -/
theorem Pending.dequeue {state location} (present : Pending state location) (duration : Nat) :
    Pending { state with transport := (LeaseQueueModel.dequeue duration state.transport).2 } location := by
  unfold LeaseQueueModel.dequeue
  split
  · exact present
  · rename_i selected found
    split
    · rename_i old slot
      obtain ⟨message, member, value⟩ := present
      obtain ⟨index, inside, stored⟩ := Array.mem_iff_getElem.mp member
      have original : state.transport.messages[index]? = some (some message) := by
        simp [inside, stored]
      by_cases sameIndex : index = selected
      · subst index
        have sameMessage : message = old := Option.some.inj (Option.some.inj (original.symm.trans slot))
        subst message
        refine ⟨old.lease state.transport.now duration, Array.mem_of_getElem? (i := selected) ?_, value⟩
        simp [inside]
      · refine ⟨message, Array.mem_of_getElem? (i := index) ?_, value⟩
        simpa [Ne.symm sameIndex] using original
    · exact present

theorem Covered.dequeue {tree journal state} (covered : Covered tree journal state) (duration : Nat) :
    Covered tree journal { state with transport := (LeaseQueueModel.dequeue duration state.transport).2 } :=
  covered.mono_work (fun _ present => present.dequeue duration)

/-- Coverage survives the actual poll, even if leasing commits and its reply is
lost. Invisibility is not removal of unfinished work. -/
theorem Covered.next_spec (tree : ExecutionTree) (journal : Journal) (worker : Worker) :
    Triple (Covered tree journal) (queue.next worker)
      (fun _ state => Covered tree journal state) (Covered tree journal) := by
  rw [next_eq]
  have read : Triple (Covered tree journal) (atomic fun state : Durable => (state.completed, state))
      (fun _ state => Covered tree journal state) (Covered tree journal) :=
    Triple.atomic _ (fun _ h => h) (fun _ h => h) (fun _ h => h)
  apply read.bind
  intro completed
  cases completed with
  | some outcome =>
    exact (Triple.pure _ _).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)
  | none =>
    have polled : Triple (Covered tree journal)
        (atomic fun state : Durable =>
          let (delivery, next) := LeaseQueueModel.dequeue 1 state.transport
          (delivery, { state with transport := next }))
        (fun _ state => Covered tree journal state) (Covered tree journal) :=
      Triple.atomic _ (fun _ h => h.dequeue 1) (fun _ h => h) (fun _ h => h.dequeue 1)
    apply polled.bind
    intro delivery
    cases delivery <;>
      exact (Triple.pure _ _).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)

/-- Work in every slot other than the currently acknowledged message. -/
def Remaining (state : Durable) (receipt : Receipt) (location : Location) : Prop :=
  ∃ index message, receipt.message ≠ index ∧
    state.transport.messages[index]? = some (some message) ∧ message.value = location

theorem Remaining.published {state receipt location} (present : Remaining state receipt location)
    (locations : List Location) : Pending (ackOp receipt (enqueued locations state)) location := by
  obtain ⟨index, message, different, stored, value⟩ := present
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  refine ⟨message, Array.mem_of_getElem? (i := index) ?_, value⟩
  change (LeaseQueueModel.acknowledge receipt (enqueued locations state).transport).2.messages[index]? = _
  rw [LeaseQueue.acknowledge_preserves_other receipt _ index different, enqueued_old _ _ _ inside, stored]

/-- The worker must justify replacing its incoming slot by its successors.
This is structural coverage of those locations, not an assumption that any
worker execution has succeeded or the whole workflow will terminate. -/
def Replaced (tree : ExecutionTree) (journal : Journal) (state : Durable) (receipt : Receipt)
    (locations : Array Location) : Prop :=
  Coverage journal (fun location => Remaining state receipt location ∨ location ∈ locations)
    tree Location.root (state.completed = some tree.exit)

/-- A runnable response replaces its delivery's responsibilities; a final
response supplies the original program's outcome. -/
def CoversResponse (tree : ExecutionTree) (journal : Journal) (state : Durable) (receipt : Receipt) :
    StepResult → Prop
  | .runnable locations => Replaced tree journal state receipt locations
  | .done outcome => outcome = tree.exit

/-- Publication preserves coverage at every physical crash prefix. Before
acknowledgement the old work remains; afterwards every successor has its own
slot and all unrelated messages remain. -/
theorem Covered.publish {tree journal} (location : Location) (receipt : Receipt) (locations : Array Location)
    (start : CrashModel.State Durable) (covered : Covered tree journal start.durable)
    (replaced : Replaced tree journal start.durable receipt locations)
    (inside : receipt.message < start.durable.transport.messages.size) :
    Covered tree journal ((queue.complete location (.runnable locations) ⟨(), some (location, receipt)⟩).run start).2.durable := by
  rcases runnable_cases location receipt locations start with ⟨count, _, published⟩ | acknowledged
  · rw [published]
    exact covered.enqueued _
  · rw [acknowledged]
    have fresh := ack_fresh receipt locations _ _ inside (enqueued_fresh locations start.durable)
    apply replaced.mono_work
    intro next represented
    rcases represented with retained | member
    · exact retained.published _
    · obtain ⟨index, bound, same⟩ := Array.mem_iff_getElem.mp member
      obtain ⟨message, stored, value⟩ := fresh index bound
      exact ⟨message, Array.mem_of_getElem? stored, value.trans (by simpa [getElem!_pos, bound] using same)⟩

/-- Final publication follows the same rule: the incoming work remains before
the outcome write, and the durable outcome itself supplies coverage afterwards. -/
theorem Covered.finish {tree journal} (location : Location) (receipt : Receipt)
    (start : CrashModel.State Durable) (covered : Covered tree journal start.durable) :
    Covered tree journal ((queue.complete location (.done tree.exit) ⟨(), some (location, receipt)⟩).run start).2.durable := by
  obtain ⟨count, bound, committed⟩ := complete_prefix location receipt (.done tree.exit) start
  simp only [operations, List.length_cons, List.length_nil] at bound
  have cases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · simpa [committed, operations, applyOps] using covered
  · apply Coverage.reported
    simp [committed, operations, applyOps, doneOp]
  · apply Coverage.reported
    simp [committed, operations, applyOps, doneOp, ackOp]

end LeanCloud.Proofs.LeasePublication
