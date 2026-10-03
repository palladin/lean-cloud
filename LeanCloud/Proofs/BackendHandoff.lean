import LeanCloud.Proofs.BackendAccounted

namespace LeanCloud.Backend.Proofs.Accounting
open Lean LeanEff LeanCloud.Proofs
open Worker (checked_pure)

theorem enqueue_checked {tree : ExecutionTree} (checkpoint state : Backend.State)
    (begun : Worker.Grows checkpoint state) (location : Location)
    (active : tree.Activated (Journal.view state) location) :
    Checked tree (Replay.transport.enqueue location) (fun _ _ final => Issued checkpoint location final) () state := by
  apply Safe.request
  · intro current value after kept growth law
    have preserved := Worker.enqueue_preserves kept.safety (active.grow growth.journal) law
    exact ⟨kept.no_ack_commit (operation := .enqueue location) trivial law preserved.1 preserved.2, preserved.2⟩
  · intro current value after kept growth law
    obtain ⟨rfl, rfl⟩ := law
    have issued : Issued checkpoint location
        { current with queue.messages := current.queue.messages.push { location, published := current.snapshot } } :=
      ⟨current.queue.messages.size, { location, published := current.snapshot },
        (begun.trans growth).queue.size, by simp, rfl, (begun.trans growth).journal.to_snapshot⟩
    exact .pure fun final bounded later => ⟨(), (), rfl, issued.grow later⟩

/-- Permission to acknowledge a particular delivered publication. The receipt
may be stale; its identity and the completed handoff are still preserved. -/
def AllowedAck (tree : ExecutionTree) (receipt : Receipt) (state : Backend.State) : Prop :=
  ∃ (id : Nat) (message : Backend.Message), state.queue.receipts[receipt]? = some id ∧
    state.queue.messages[id]? = some message ∧ Retired tree id message.location message.published state

theorem AllowedAck.grow {tree receipt before after} (allowed : AllowedAck tree receipt before)
    (growth : Worker.Grows before after) : AllowedAck tree receipt after := by
  obtain ⟨id, message, received, stored, permitted⟩ := allowed
  obtain ⟨current, found, payload, birth, _⟩ := growth.queue.messages id message stored
  exact ⟨id, current, growth.queue.receipts _ _ received, found,
    by simpa only [payload, birth] using permitted.grow growth⟩

theorem Valid.ack_commit {tree receipt before after accepted}
    (valid : Valid tree before) (allowed : AllowedAck tree receipt before)
    (law : Commits before (.acknowledge receipt) accepted after) :
    Valid tree after ∧ Worker.Grows before after := by
  have preserved := Worker.acknowledge_preserves valid.safety law
  refine ⟨⟨preserved.1, ?_⟩, preserved.2⟩
  intro other actual found acknowledged
  cases accepted with
  | false =>
    have same : after = before := law
    subst after
    exact valid.retired other actual found acknowledged
  | true =>
    obtain ⟨id, message, received, stored, rfl⟩ := law
    obtain ⟨permittedId, permittedMessage, allowedReceipt, allowedStored, permitted⟩ := allowed
    have equalId := Option.some.inj (received.symm.trans allowedReceipt)
    subst permittedId
    have equalMessage := Option.some.inj (stored.symm.trans allowedStored)
    subst permittedMessage
    rw [Array.getElem?_setIfInBounds] at found
    split at found
    · rename_i same
      subst other
      split at found
      · cases found; exact permitted.grow preserved.2
      · cases found
    · exact (valid.retired other actual found acknowledged).grow preserved.2

theorem acknowledge_checked {tree : ExecutionTree} (receipt : Receipt) (state : Backend.State)
    (allowed : AllowedAck tree receipt state) :
    Checked tree (Replay.transport.acknowledge receipt) (fun _ _ _ => True) () state := by
  apply Safe.request
  · intro current value after kept growth law
    exact kept.ack_commit (allowed.grow growth) law
  · intro current value after kept growth law
    exact .pure fun _ _ _ => ⟨value, (), rfl, trivial⟩

private abbrev enqueueBody (location : Location) (_ : PUnit.{1}) :
    StateT Replay.Worker Replay.M (ForInStep PUnit.{1}) := do
  LeaseQueue.liftBackend (Replay.transport.enqueue location)
  pure (.yield PUnit.unit)

private theorem enqueue_list_checked {tree : ExecutionTree} (checkpoint : Backend.State) (locations : List Location)
    (worker : Replay.Worker) (state : Backend.State) (valid : Valid tree state)
    (begun : Worker.Grows checkpoint state)
    (active : ∀ location ∈ locations, tree.Activated (Journal.view state) location) :
    Checked tree (forIn locations PUnit.unit enqueueBody)
      (fun _ handle final => handle = worker ∧ ∀ location ∈ locations, Issued checkpoint location final) worker state := by
  induction locations generalizing worker state with
  | nil => exact checked_pure _ _ _ _ (fun _ _ _ => ⟨rfl, by simp⟩)
  | cons location rest ih =>
    rw [List.forIn_cons]
    have first : Checked tree (enqueueBody location PUnit.unit)
        (fun value handle final => value = .yield PUnit.unit ∧ handle = worker ∧ Issued checkpoint location final) worker state := by
      unfold enqueueBody
      apply Checked.bind (Worker.Checked.leased (enqueue_checked checkpoint state begun location (active location (by simp))) valid
        (fun _ _ _ _ growth issued => issued.grow growth) worker) valid
      intro ignored handle current kept growth result
      obtain ⟨rfl, issued⟩ := result
      exact checked_pure _ _ _ _ (fun _ _ later => ⟨rfl, rfl, issued.grow later⟩)
    apply Checked.bind first valid
    intro value handle current kept growth result
    obtain ⟨rfl, same, issued⟩ := result
    subst handle
    have tail := ih worker current kept (begun.trans growth)
      (fun item member => (active item (by simp [member])).grow growth.journal)
    apply Worker.Checked.weaken (Worker.Checked.remember tail)
    intro ignored handle final result
    obtain ⟨later, rfl, restIssued⟩ := result
    refine ⟨rfl, ?_⟩
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact issued.grow later
    · exact restIssued item member

/-- The real adapter publishes every successor (or the final result) before
its acknowledgement can commit. The certificate survives a lost ack reply. -/
theorem complete_published_checked {tree : ExecutionTree} {node : ExecutionTree}
    (reflexive : (toJson tree.exit == toJson tree.exit) = true)
    (location : Location) (receipt : Receipt) (response : StepResult)
    (route : TreeRoute tree Location.root location node)
    (before state : Backend.State) (beforeValid : Worker.Valid tree before)
    (begun : Worker.Grows before state) (received : Worker.Received location receipt before)
    (progress : Journal.StepProgress tree location node before response state)
    (valid : Valid tree state) (emitted : Journal.Emits tree response state) :
    Checked tree (Replay.queue.complete location response)
      (fun _ worker final => worker = ⟨(), none⟩ ∧ Worker.FinalStored response final ∧ Successors state response final)
      ⟨(), some (location, receipt)⟩ state := by
  have published : Checked tree
      (match response with
        | .runnable locations => forIn locations PUnit.unit enqueueBody
        | .done outcome => LeaseQueue.liftBackend (CompletionStore.write Replay.rawDb throw outcome))
      (fun _ worker final => worker = ⟨(), some (location, receipt)⟩ ∧
        Worker.FinalStored response final ∧ Successors state response final)
      ⟨(), some (location, receipt)⟩ state := by
    cases response with
    | runnable locations =>
      simp only []
      rw [← Array.forIn_toList]
      exact Worker.Checked.weaken
        (enqueue_list_checked state locations.toList _ state valid (.refl _)
          (fun item member => emitted item (by simpa using member)))
        (fun _ _ _ result => ⟨result.1, trivial, fun item member => result.2 item (by simpa using member)⟩)
    | done outcome =>
      change outcome = tree.exit at emitted
      subst outcome
      exact Worker.Checked.weaken
        (Worker.Checked.leased (write_checked tree reflexive state valid) valid
          (fun _ _ _ _ growth stored => growth.completed _ stored) _)
        (fun _ _ _ result => ⟨result.1, result.2, trivial⟩)
  have acknowledge (current : Backend.State) (kept : Valid tree current)
      (grown : Worker.Grows state current) (stored : Worker.FinalStored response current)
      (successors : Successors state response current) :
      Checked tree (do
        let _ ← LeaseQueue.liftBackend (Replay.transport.acknowledge receipt)
        modify fun worker : Replay.Worker => { worker with delivery := none })
        (fun _ worker final => worker = ⟨(), none⟩ ∧ Worker.FinalStored response final ∧ Successors state response final)
        ⟨(), some (location, receipt)⟩ current := by
    obtain ⟨id, message, delivered, existed, same⟩ := received
    have growth := begun.trans grown
    obtain ⟨actual, found, payload, birth, _⟩ := growth.queue.messages id message existed
    have allowed : AllowedAck tree receipt current := by
      refine ⟨id, actual, growth.queue.receipts _ _ delivered, found, ?_⟩
      rw [payload, birth, same]
      exact ⟨node, before, state, response, route, beforeValid.published id message existed,
        begun, grown, (Array.getElem?_eq_some_iff.mp existed).choose, valid.safety, emitted, progress, stored, successors⟩
    apply Checked.bind (Worker.Checked.leased (acknowledge_checked receipt current allowed) kept
      (fun _ _ _ _ _ _ => trivial) _) kept
    intro accepted worker acknowledged bounded later result
    obtain ⟨rfl, _⟩ := result
    exact .pure fun final finalValid last => ⟨(), ⟨(), none⟩, rfl, rfl, stored.grow (later.trans last), successors.grow (later.trans last)⟩
  unfold Replay.queue LeaseQueue.toWorkQueue
  simp only []
  have get : Checked tree (get : StateT Replay.Worker Replay.M Replay.Worker)
      (fun value worker _ => value = ⟨(), some (location, receipt)⟩ ∧ worker = value)
      ⟨(), some (location, receipt)⟩ state := .pure fun _ _ _ => ⟨_, _, rfl, rfl, rfl⟩
  apply Checked.bind get valid
  intro value worker current kept growth done
  obtain ⟨rfl, rfl⟩ := done
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have published := (Worker.Checked.remember published).mono (fun a b => a.trans b) growth
  cases response <;> apply Checked.bind published kept <;>
    intro ignored worker final bounded later result <;>
    obtain ⟨grown, rfl, stored, successors⟩ := result <;>
    exact acknowledge final bounded grown stored successors

theorem complete_checked {tree : ExecutionTree} {node : ExecutionTree}
    (reflexive : (toJson tree.exit == toJson tree.exit) = true)
    (location : Location) (receipt : Receipt) (response : StepResult)
    (route : TreeRoute tree Location.root location node)
    (before state : Backend.State) (beforeValid : Worker.Valid tree before)
    (begun : Worker.Grows before state) (received : Worker.Received location receipt before)
    (progress : Journal.StepProgress tree location node before response state)
    (valid : Valid tree state) (emitted : Journal.Emits tree response state) :
    Checked tree (Replay.queue.complete location response)
      (fun _ worker final => worker = ⟨(), none⟩ ∧ Worker.FinalStored response final)
      ⟨(), some (location, receipt)⟩ state :=
  Worker.Checked.weaken
    (complete_published_checked reflexive location receipt response route before state beforeValid
      begun received progress valid emitted)
    (fun _ _ _ result => ⟨result.1, result.2.1⟩)

end LeanCloud.Backend.Proofs.Accounting
