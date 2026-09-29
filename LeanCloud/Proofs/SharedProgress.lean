import LeanCloud.Proofs.SharedTrace
import LeanCloud.Proofs.StableWorker

/-! Structural progress of the actual worker over the combined durable Db and
leased transport. A successful publication makes every emitted successor
available even when earlier crashed attempts created duplicate messages. -/

namespace LeanCloud.Proofs
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

theorem LeasePublication.complete_available (location : Location) (receipt : LeaseQueueModel.Receipt)
    (response : StepResult) (start final : State LeasePublication.Durable) (worker : LeasePublication.Worker)
    (returned : (LeasePublication.queue.complete location response ⟨(), some (location, receipt)⟩).run start =
      (.ok ((), worker), final)) (inside : receipt.message < start.durable.transport.messages.size) :
    ResponseAvailable (final.durable.completed ≠ none) (LeasePublication.Pending final.durable) response := by
  have committed := (LeasePublication.complete_returned location receipt response start final worker returned).1
  cases response with
  | done outcome =>
    change final.durable.completed ≠ none
    rw [committed]
    simp [LeasePublication.operations, LeasePublication.applyOps, LeasePublication.doneOp, LeasePublication.ackOp]
  | runnable locations =>
    have shape : final.durable = LeasePublication.ackOp receipt (LeasePublication.enqueued locations.toList start.durable) := by
      rw [committed]
      simp only [LeasePublication.operations, LeasePublication.applyOps, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact congrArg (LeasePublication.ackOp receipt) (LeasePublication.apply_enqueue locations.toList start.durable)
    have fresh := LeasePublication.ack_fresh receipt locations start.durable _ inside
      (LeasePublication.enqueued_fresh locations start.durable)
    intro location member
    obtain ⟨index, bound, same⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨message, stored, payload⟩ := fresh index bound
    rw [shape]
    exact ⟨message, Array.mem_of_getElem? stored, payload.trans (by simpa [getElem!_pos, bound] using same)⟩

namespace SharedRecovery

theorem step_stable {source : Cloud (CrashModel.M Journal) Json} {tree target node}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root target node)
    (initial : Durable) (valid : Valid tree initial) (activated : route.Activated initial.1)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Worker M)
    (worker : Worker) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Triple (· = initial) ((step workerDb blobs fuel (journalMap.program source) target).run worker)
      (fun returned state => ∃ response, returned = (.ok response, worker) ∧
        StableResponse initial.1 node target response state.1 ∧ ParentResponse initial.1 target response ∧ state.2 = initial.2)
      (fun _ => True) := by
  rw [step_eq blobs fuel source supported target worker]
  have checked := route.activated_stable expansion supported initial.1 valid.1 valid.2.1 activated
    comparable sameExit noBlobs fuel enough
  apply ((checked.withLeft (· = initial.2)).map (fun outcome => (outcome, worker))).weaken
  · intro state same; subst state; exact ⟨rfl, rfl⟩
  · intro returned state h
    obtain ⟨outcome, same, ⟨response, outcomeEq, _, advances, parent⟩, queueSame⟩ := h
    exact ⟨response, same.trans (congrArg (fun outcome => (outcome, worker)) outcomeEq), advances, parent, queueSame⟩
  · intro _ _; trivial

/-- A normal shared publication has really published its response. The
journal embedding frames all transport operations, including acknowledgement. -/
theorem complete_available (location : Location) (receipt : LeaseQueueModel.Receipt)
    (response : StepResult) (start final : State Durable) (worker : Worker)
    (returned : (queue.complete location response ⟨(), some (location, receipt)⟩).run start =
      (.ok ((), worker), final)) (inside : receipt.message < start.durable.2.transport.messages.size) :
    ResponseAvailable (final.durable.2.completed ≠ none) (LeasePublication.Pending final.durable.2) response := by
  rw [queue_complete] at returned
  simp only [withRight, ExceptT.run] at returned
  generalize executed : (LeasePublication.queue.complete location response ⟨(), some (location, receipt)⟩)
    ⟨start.durable.2, start.faults⟩ = observed at returned
  obtain ⟨result, committed⟩ := observed
  cases result with
  | error crash => cases returned
  | ok pair =>
    cases returned
    exact LeasePublication.complete_available location receipt response ⟨start.durable.2, start.faults⟩ committed
      worker executed inside

theorem complete_published_spec {tree} (location : Location) (receipt : LeaseQueueModel.Receipt)
    (response : StepResult) (initial : Durable) (valid : Valid tree initial)
    (emits : tree.EmitsActivated initial.1 response)
    (inside : receipt.message < initial.2.transport.messages.size) :
    Triple (· = initial) (queue.complete location response ⟨(), some (location, receipt)⟩)
      (fun returned state => returned = ((), (⟨(), none⟩ : Worker)) ∧ state.1 = initial.1 ∧
        ResponseAvailable (state.2.completed ≠ none) (LeasePublication.Pending state.2) response)
      (fun _ => True) := by
  intro start same
  have checked := complete_spec location receipt response initial valid emits start same
  generalize executed : (queue.complete location response ⟨(), some (location, receipt)⟩).run start = observed at *
  obtain ⟨result, final⟩ := observed
  refine ⟨checked.1, ?_⟩
  cases result with
  | error crash => exact ⟨trivial, checked.2.2⟩
  | ok value =>
    obtain ⟨valueUnit, worker⟩ := value
    cases valueUnit
    exact ⟨checked.2.1, checked.2.2.2,
      complete_available location receipt response start final worker executed (same ▸ inside)⟩

/-- Execute and publish an actual delivery. On return its structural progress
is backed by retained successor messages or a durable final outcome. -/
theorem step_complete_published {source : Cloud (CrashModel.M Journal) Json} {tree target node receipt message}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root target node)
    (initial : Durable) (valid : Valid tree initial) (activated : route.Activated initial.1)
    (held : LeaseQueueModel.current receipt initial.2.transport = some message)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Worker M)
    (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Triple (· = initial)
      ((do
        let response ← step workerDb blobs fuel (journalMap.program source) target
        queue.complete target response
        pure response : ExceptT CloudError (StateT Worker M) StepResult).run ⟨(), some (target, receipt)⟩)
      (fun returned state => ∃ response, returned = (.ok response, (⟨(), none⟩ : Worker)) ∧
        StableResponse initial.1 node target response state.1 ∧ ParentResponse initial.1 target response ∧
        ResponseAvailable (state.2.completed ≠ none) (LeasePublication.Pending state.2) response)
      (fun _ => True) := by
  rw [report_eq]
  have checked := ((step_spec expansion supported route initial valid activated comparable sameExit
    blobs ⟨(), some (target, receipt)⟩ fuel enough).conjoin
    (step_stable expansion supported route initial valid activated comparable sameExit
      blobs ⟨(), some (target, receipt)⟩ fuel enough)).weaken
        (pre' := (· = initial)) (stopped' := fun _ => True)
        (fun _ h => ⟨h, h⟩) (fun _ _ h => h) (fun _ _ => trivial)
  apply checked.bind
  intro returned current h
  obtain ⟨⟨response, rfl, _, validNow, queueSame, emits⟩, response', equal, advances, parent, _⟩ := h
  have sameResponse : response = response' := by cases equal; rfl
  subst response'
  have inside := (Array.getElem?_eq_some_iff.mp (LeaseQueue.current_iff.mp held).1).choose
  have publication := complete_published_spec target receipt response current.durable validNow emits (queueSame ▸ inside)
  apply (publication.map (fun returned => (Except.ok (ε := CloudError) response, returned.2))).weaken
    (pre' := (· = current.durable))
    (post' := fun returned state => ∃ response, returned = (.ok response, (⟨(), none⟩ : Worker)) ∧
      StableResponse initial.1 node target response state.1 ∧ ParentResponse initial.1 target response ∧
      ResponseAvailable (state.2.completed ≠ none) (LeasePublication.Pending state.2) response)
    (stopped' := fun _ => True) (fun _ h => h) _ (fun _ h => h) current rfl
  intro returned state h
  obtain ⟨value, same, valueEq, journalSame, available⟩ := h
  exact ⟨response, same.trans (congrArg (fun returned => (Except.ok (ε := CloudError) response, returned.2)) valueEq),
    journalSame ▸ advances, parent, available⟩

end SharedRecovery
end LeanCloud.Proofs
