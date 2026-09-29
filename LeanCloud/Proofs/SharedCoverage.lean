import LeanCloud.Proofs.SharedRecovery
import LeanCloud.Proofs.QueueCoverage
import LeanCloud.Proofs.CoveragePublication
import LeanCloud.Proofs.DeliveryTarget
import LeanCloud.Proofs.SharedWorker

/-! Preservation of unfinished work in the shared journal/transport state,
through the actual worker and its interrupted successor publication. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

def Covered (tree : ExecutionTree) (state : Durable) : Prop :=
  LeasePublication.Covered tree state.1 state.2

theorem covered_initial (tree : ExecutionTree) : Covered tree initial :=
  LeasePublication.Covered.initial tree Journal.empty

theorem Covered.advance {tree state} (covered : Covered tree state) (elapsed : Nat) :
    Covered tree (advance elapsed state) := covered

/-- Polling cannot discard coverage, including a committed dequeue whose
receipt was lost to a crash. The journal is framed by the shared embedding. -/
theorem next_covered (tree : ExecutionTree) (worker : Worker) :
    Triple (Covered tree) (queue.next worker) (fun _ state => Covered tree state) (Covered tree) := by
  rw [queue_next]
  intro start covered
  have component := LeasePublication.Covered.next_spec tree start.durable.1 worker
  apply (component.withRight (· = start.durable.1)).weaken
    (pre' := (· = start.durable)) (post' := fun _ state => Covered tree state) (stopped' := Covered tree)
    _ _ _ start rfl
  · intro state same; subst state; exact ⟨rfl, covered⟩
  · intro _ state h; unfold Covered; rw [h.1]; exact h.2
  · intro state h; unfold Covered; rw [h.1]; exact h.2

/-- A worker's structural replacement proof suffices for every interrupted
prefix of the actual shared queue publication. It is not assumed by the queue. -/
theorem publish_covered {tree} (location : Location) (receipt : LeaseQueueModel.Receipt)
    (locations : Array Location) (start : State Durable) (covered : Covered tree start.durable)
    (replaced : LeasePublication.Replaced tree start.durable.1 start.durable.2 receipt locations)
    (inside : receipt.message < start.durable.2.transport.messages.size) :
    Covered tree ((queue.complete location (.runnable locations) ⟨(), some (location, receipt)⟩).run start).2.durable := by
  rw [queue_complete]
  exact covered.publish location receipt locations ⟨start.durable.2, start.faults⟩ replaced inside

theorem finish_covered {tree} (location : Location) (receipt : LeaseQueueModel.Receipt)
    (start : State Durable) (covered : Covered tree start.durable) :
    Covered tree ((queue.complete location (.done tree.exit) ⟨(), some (location, receipt)⟩).run start).2.durable := by
  rw [queue_complete]
  exact covered.finish location receipt ⟨start.durable.2, start.faults⟩

/-- The actual worker now proves the queue's replacement obligation. The
transport is unchanged during journal execution, so its retained receipt and
all unrelated messages are available to the subsequent publication. -/
theorem step_covered {source : Cloud (CrashModel.M Journal) Json} {tree target node receipt message}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root target node)
    (initial : Durable) (valid : Valid tree initial) (covered : Covered tree initial)
    (activated : route.Activated initial.1)
    (held : LeaseQueueModel.current receipt initial.2.transport = some message) (payload : message.value = target)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Worker M)
    (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Triple (· = initial)
      ((ReplayInterpreter.Internal.step workerDb blobs fuel (journalMap.program source) target).run ⟨(), some (target, receipt)⟩)
      (fun returned state => ∃ response, returned = (.ok response, (⟨(), some (target, receipt)⟩ : Worker)) ∧
        Covered tree state ∧ LeasePublication.CoversResponse tree state.1 state.2 receipt response ∧ state.2 = initial.2)
      (Covered tree) := by
  rw [step_eq blobs fuel source supported target ⟨(), some (target, receipt)⟩]
  have sourceSpec := route.activated_delivery expansion supported initial.1 valid.1 valid.2.1 activated covered
    held payload comparable sameExit noBlobs fuel enough
  apply ((sourceSpec.withLeft (· = initial.2)).map (fun outcome => (outcome, (⟨(), some (target, receipt)⟩ : Worker)))).weaken
  · intro state same; subst state; exact ⟨rfl, rfl⟩
  · intro returned state h
    obtain ⟨outcome, same, ⟨response, outcomeEq, _, coveredNow, replaces⟩, queueSame⟩ := h
    refine ⟨response, same.trans (congrArg (fun outcome => (outcome, (⟨(), some (target, receipt)⟩ : Worker))) outcomeEq), ?_, ?_, queueSame⟩
    · unfold Covered; rw [queueSame]; exact coveredNow
    · rw [queueSame]; exact replaces
  · intro state h
    unfold Covered
    rw [h.2]
    exact h.1.2

/-- Completing the worker's response preserves both validity and coverage at
every publication boundary, including after acknowledging the incoming slot. -/
theorem complete_covered_spec {tree} (location : Location) (receipt : LeaseQueueModel.Receipt)
    (response : StepResult) (initial : Durable) (valid : Valid tree initial) (covered : Covered tree initial)
    (emits : tree.EmitsActivated initial.1 response)
    (replaces : LeasePublication.CoversResponse tree initial.1 initial.2 receipt response)
    (inside : receipt.message < initial.2.transport.messages.size) :
    Triple (· = initial) (queue.complete location response ⟨(), some (location, receipt)⟩)
      (fun returned state => returned = ((), (⟨(), none⟩ : Worker)) ∧
        (Valid tree state ∧ Covered tree state) ∧ state.1 = initial.1)
      (fun state => (Valid tree state ∧ Covered tree state) ∧ state.1 = initial.1) := by
  have kept (start : State Durable) (same : start.durable = initial) :
      Covered tree ((queue.complete location response ⟨(), some (location, receipt)⟩).run start).2.durable := by
    have coverage : Covered tree start.durable := same ▸ covered
    cases response with
    | done outcome =>
      have correct : outcome = tree.exit := replaces
      subst outcome
      exact finish_covered location receipt start coverage
    | runnable locations =>
      exact publish_covered location receipt locations start coverage (same ▸ replaces) (same ▸ inside)
  exact ((complete_spec location receipt response initial valid emits).ensure kept).weaken
    (fun _ h => h) (fun _ _ h => ⟨h.1.1, ⟨h.1.2.1, h.2⟩, h.1.2.2⟩)
    (fun _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)

/-- An actual delivery executes its journal step and publishes its response.
The incoming receipt supplies replacement coverage; neither a return nor a
crash can discard unfinished workflow work. -/
theorem step_complete_covered {source : Cloud (CrashModel.M Journal) Json} {tree target node receipt message}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root target node)
    (initial : Durable) (valid : Valid tree initial) (covered : Covered tree initial)
    (activated : route.Activated initial.1)
    (held : LeaseQueueModel.current receipt initial.2.transport = some message) (payload : message.value = target)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Worker M)
    (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Triple (· = initial)
      ((do
        let response ← step workerDb blobs fuel (journalMap.program source) target
        queue.complete target response
        pure response : ExceptT CloudError (StateT Worker M) StepResult).run ⟨(), some (target, receipt)⟩)
      (fun returned state => ∃ response, returned = (.ok response, (⟨(), none⟩ : Worker)) ∧
        (Extends initial.1 state.1 ∧ Valid tree state ∧ Covered tree state) ∧ tree.EmitsActivated state.1 response)
      (fun state => Extends initial.1 state.1 ∧ Valid tree state ∧ Covered tree state) := by
  rw [report_eq]
  have checked := ((step_spec expansion supported route initial valid activated comparable sameExit
    blobs ⟨(), some (target, receipt)⟩ fuel enough).conjoin
    (step_covered expansion supported route initial valid covered activated held payload comparable sameExit
      blobs fuel enough)).weaken
        (pre' := (· = initial)) (stopped' := fun state => Extends initial.1 state.1 ∧ Valid tree state ∧ Covered tree state)
        (fun _ h => ⟨h, h⟩) (fun _ _ h => h) (fun _ h => ⟨h.1.1, h.1.2.1, h.2⟩)
  apply checked.bind
  intro returned current h
  obtain ⟨⟨response, rfl, growth, validNow, queueSame, emits⟩,
    response', equal, coveredNow, replaces, _⟩ := h
  have sameResponse : response = response' := by cases equal; rfl
  subst response'
  have inside := (Array.getElem?_eq_some_iff.mp (LeaseQueue.current_iff.mp held).1).choose
  have insideNow : receipt.message < current.durable.2.transport.messages.size := queueSame ▸ inside
  have publication := complete_covered_spec target receipt response current.durable validNow coveredNow
    emits replaces insideNow
  apply (publication.map (fun returned => (Except.ok (ε := CloudError) response, returned.2))).weaken
    (pre' := (· = current.durable))
    (post' := fun returned state => ∃ response, returned = (.ok response, (⟨(), none⟩ : Worker)) ∧
      (Extends initial.1 state.1 ∧ Valid tree state ∧ Covered tree state) ∧ tree.EmitsActivated state.1 response)
    (stopped' := fun state => Extends initial.1 state.1 ∧ Valid tree state ∧ Covered tree state) (fun _ h => h) _ (fun _ h => ⟨h.2 ▸ growth, h.1⟩) current rfl
  intro returned state h
  obtain ⟨value, same, valueEq, validFinal, untouched⟩ := h
  exact ⟨response, same.trans (congrArg (fun returned => (Except.ok (ε := CloudError) response, returned.2)) valueEq),
    ⟨untouched ▸ growth, validFinal⟩, untouched ▸ emits⟩

end LeanCloud.Proofs.SharedRecovery
