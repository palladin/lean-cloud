import LeanCloud.Proofs.CrashEmbedding
import LeanCloud.Proofs.JournalMap
import LeanCloud.Proofs.LeaseMap
import LeanCloud.Proofs.InterpreterMap
import LeanCloud.Proofs.TreeLeaseSafety
import LeanCloud.Proofs.TreeCausalPublication

/-! One durable state and one fault script for the physical journal, leased
transport, and final outcome. These are the existing adapters over embedded
primitives, not atomic replacements for their multi-operation sequences. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

abbrev Durable := Journal × LeasePublication.Durable
abbrev M := CrashModel.M Durable
abbrev Worker := LeasePublication.Worker

def journalMap := leftMap Journal LeasePublication.Durable
def transportMap := rightMap Journal LeasePublication.Durable

def rawDb : Db Unit M := journalMap.db atomicDb
def db : Db Unit M := JournalDb.ofDb rawDb

def transport : LeanCloud.LeaseQueue Unit M LeaseQueueModel.Receipt :=
  transportMap.lease LeasePublication.transport

def queue : WorkQueue Worker M := transport.toWorkQueue
  ((transportMap.state Unit).map LeasePublication.readCompleted)
  (fun outcome => (transportMap.state Unit).map (LeasePublication.writeCompleted outcome))

/-- Embedding is below the journal adapter. Every raw read and write retains
its own before/after crash boundary and shares the transport's fault script. -/
theorem db_eq : db = journalMap.db ReplayRecovery.db :=
  (journalMap.journal_map atomicDb).symm

theorem queue_next (worker : Worker) :
    queue.next worker = withRight (LeasePublication.queue.next worker) :=
  congrFun (transportMap.next_map LeasePublication.transport
    LeasePublication.readCompleted LeasePublication.writeCompleted).symm worker

theorem queue_complete (location : Location) (response : StepResult) (worker : Worker) :
    queue.complete location response worker = withRight (LeasePublication.queue.complete location response worker) :=
  congrFun (transportMap.complete_map LeasePublication.transport
    LeasePublication.readCompleted LeasePublication.writeCompleted location response).symm worker

def Valid (tree : ExecutionTree) (state : Durable) : Prop :=
  Extends state.1 (tree.journal Location.root) ∧ tree.Causal Location.root state.1 ∧
    LeasePublication.ActivatedQueue tree state.1 state.2

def initial : Durable := (Journal.empty, LeasePublication.enqueueOp Location.root {})

theorem valid_initial (tree : ExecutionTree) : Valid tree initial := by
  refine ⟨?_, ExecutionTree.Causal.empty _ _, LeasePublication.ActivatedQueue.initial _ _⟩
  intro key value recorded
  cases recorded

/-- Polling in the combined backend retains both invariants, even when a
dequeue commits and its reply is lost to a crash. -/
theorem next_spec {m : Type → Type} {program : Cloud m Json} {tree}
    (expansion : Expansion program tree) (worker : Worker) :
    Triple (Valid tree) (queue.next worker)
      (fun returned state => Valid tree state ∧
        LeasePublication.PollValid (tree.Activated state.1) tree.exit returned state.2 ∧
        ∀ location, returned.1 = .item location →
          ∃ node, ∃ route : TreeRoute tree Location.root location node,
            route.Activated state.1 ∧
              ((route.Ready state.1 ∧ OpenParent state.1 location) ∨ Obsolete state.1 location))
      (Valid tree) := by
  rw [queue_next]
  intro start valid
  have component := LeasePublication.next_delivery_ready expansion valid.1 valid.2.1 worker
  have shared := component.withRight (fun journal => journal = start.durable.1)
  apply shared.weaken (pre' := (· = start.durable))
    (post' := fun returned state => Valid tree state ∧
      LeasePublication.PollValid (tree.Activated state.1) tree.exit returned state.2 ∧
      ∀ location, returned.1 = .item location →
        ∃ node, ∃ route : TreeRoute tree Location.root location node,
          route.Activated state.1 ∧
            ((route.Ready state.1 ∧ OpenParent state.1 location) ∨ Obsolete state.1 location))
    (stopped' := Valid tree) _ _ _ start rfl
  · intro state same
    subst state
    exact ⟨rfl, valid.2.2⟩
  · intro returned state h
    obtain ⟨same, polled, ready⟩ := h
    unfold Valid
    rw [same]
    exact ⟨⟨valid.1, valid.2.1, polled.1⟩, polled, ready⟩
  · intro state h
    exact ⟨h.1 ▸ valid.1, h.1 ▸ valid.2.1, h.1 ▸ h.2⟩

/-- Queue publication has its own physical crash boundaries in the shared
backend. It changes no journal record and clears the receipt only on return. -/
theorem complete_spec {tree} (location : Location) (receipt : LeaseQueueModel.Receipt)
    (response : StepResult) (initial : Durable) (valid : Valid tree initial)
    (emits : ExecutionTree.EmitsActivated tree initial.1 response) :
    Triple (· = initial) (queue.complete location response ⟨(), some (location, receipt)⟩)
      (fun returned state => returned = ((), (⟨(), none⟩ : Worker)) ∧ Valid tree state ∧ state.1 = initial.1)
      (fun state => Valid tree state ∧ state.1 = initial.1) := by
  rw [queue_complete]
  have component := LeasePublication.QueueValid.complete_spec location receipt response emits
  apply (component.withRight (· = initial.1)).weaken
  · intro state same; subst state; exact ⟨rfl, valid.2.2⟩
  · intro returned state h
    obtain ⟨sameJournal, sameReturn, validQueue⟩ := h
    exact ⟨sameReturn, ⟨sameJournal ▸ valid.1, sameJournal ▸ valid.2.1,
      sameJournal ▸ validQueue⟩, sameJournal⟩
  · intro state h
    exact ⟨⟨h.1 ▸ valid.1, h.1 ▸ valid.2.1, h.1 ▸ h.2⟩, h.1⟩

/-- Time is advanced explicitly by the environment, not by catching a crash. -/
def advance (elapsed : Nat) (state : Durable) : Durable :=
  (state.1, { state.2 with transport := LeaseQueueModel.advance elapsed state.2.transport })

theorem valid_advance {tree state} (valid : Valid tree state) (elapsed : Nat) :
    Valid tree (advance elapsed state) := ⟨valid.1, valid.2.1, valid.2.2.advance elapsed⟩

end LeanCloud.Proofs.SharedRecovery
