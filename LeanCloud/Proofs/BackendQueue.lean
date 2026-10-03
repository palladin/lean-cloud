import LeanCloud.Proofs.BackendOperations
import Init.Data.Array.Monadic

namespace LeanCloud.Backend.Proofs.Worker
open Lean LeanEff LeanCloud.Proofs

def Next (tree : ExecutionTree) (work : Work) (worker : Replay.Worker) (state : Backend.State) : Prop :=
  match work with
  | .idle => worker.delivery = none
  | .completed outcome => worker.delivery = none ∧ outcome = tree.exit ∧ completed state = some (toJson outcome)
  | .item location => ∃ receipt, worker.delivery = some (location, receipt) ∧
      tree.Activated (Journal.view state) location ∧ Received location receipt state

theorem Next.grow {tree work worker before after} (next : Next tree work worker before)
    (growth : Grows before after) : Next tree work worker after := by
  cases work with
  | idle => exact next
  | completed outcome => exact ⟨next.1, next.2.1, growth.completed _ next.2.2⟩
  | item location =>
    obtain ⟨receipt, held, active, received⟩ := next
    exact ⟨receipt, held, active.grow growth.journal, received.grow growth⟩

theorem next_checked (tree : ExecutionTree) (worker : Replay.Worker)
    (state : Backend.State) (valid : Valid tree state) :
    Checked (Valid tree) Replay.queue.next (Next tree) worker state := by
  unfold Replay.queue LeaseQueue.toWorkQueue
  simp only []
  have clear : Checked (Valid tree) (modify fun handle : Replay.Worker => { handle with delivery := none })
      (fun _ handle _ => handle = { worker with delivery := none }) worker state :=
    .pure fun _ _ _ => ⟨(), _, rfl, rfl⟩
  apply Checked.bind clear valid
  intro ignored handle initial initialValid initialGrowth same
  subst handle
  have read := (read_completed tree initial initialValid).leased initialValid
    (by
      intro answer handle before after growth result
      cases answer with
      | none => trivial
      | some outcome => exact ⟨result.1, growth.completed _ result.2⟩)
    { worker with delivery := none }
  apply Checked.bind read initialValid
  intro answer handle current kept growth result
  obtain ⟨rfl, result⟩ := result
  cases answer with
  | some outcome =>
    exact checked_pure _ _ _ _ (fun _ _ later => ⟨rfl, result.1, later.completed _ result.2⟩)
  | none =>
    have polled := (dequeue_checked tree current).leased kept
      (fun _ _ _ _ growth result location receipt same =>
        ⟨(result location receipt same).1.grow growth.journal, (result location receipt same).2.grow growth⟩)
      { worker with delivery := none }
    apply Checked.bind polled kept
    intro delivery handle polled bounded later result
    obtain ⟨rfl, result⟩ := result
    cases delivery with
    | none => exact checked_pure _ _ _ _ (fun _ _ _ => rfl)
    | some pair =>
      obtain ⟨location, receipt⟩ := pair
      exact .pure fun final finalValid last =>
        ⟨.item location, { worker with delivery := some (location, receipt) }, rfl,
          receipt, rfl, (result location receipt rfl).1.grow last.journal,
          (result location receipt rfl).2.grow last⟩

private abbrev enqueueBody (location : Location) (_ : PUnit.{1}) :
    StateT Replay.Worker Replay.M (ForInStep PUnit.{1}) := do
  LeaseQueue.liftBackend (Replay.transport.enqueue location)
  pure (.yield PUnit.unit)

private theorem enqueue_list_checked {tree : ExecutionTree} (locations : List Location)
    (worker : Replay.Worker) (state : Backend.State) (valid : Valid tree state)
    (active : ∀ location ∈ locations, tree.Activated (Journal.view state) location) :
    Checked (Valid tree) (forIn locations PUnit.unit enqueueBody)
      (fun _ handle _ => handle = worker) worker state := by
  induction locations generalizing worker state with
  | nil => exact checked_pure _ _ _ _ (fun _ _ _ => rfl)
  | cons location rest ih =>
    rw [List.forIn_cons]
    have first : Checked (Valid tree) (enqueueBody location PUnit.unit)
        (fun value handle _ => value = .yield PUnit.unit ∧ handle = worker) worker state := by
      unfold enqueueBody
      apply Checked.bind ((enqueue_checked state (active location (by simp))).leased valid
        (fun _ _ _ _ _ _ => trivial) worker) valid
      intro value handle current kept growth result
      obtain ⟨rfl, _⟩ := result
      exact checked_pure _ _ _ _ (fun _ _ _ => ⟨rfl, rfl⟩)
    apply Checked.bind first valid
    intro value handle current kept growth result
    obtain ⟨rfl, same⟩ := result
    subst handle
    exact ih _ current kept (fun item member => (active item (by simp [member])).grow growth.journal)

def FinalStored (response : StepResult) (state : Backend.State) : Prop :=
  match response with
  | .done outcome => completed state = some (toJson outcome)
  | .runnable _ => True

theorem FinalStored.grow {response before after} (stored : FinalStored response before)
    (growth : Grows before after) : FinalStored response after := by
  cases response with
  | done outcome => exact growth.completed _ stored
  | runnable _ => trivial

theorem complete_checked {tree : ExecutionTree}
    (reflexive : (toJson tree.exit == toJson tree.exit) = true)
    (location : Location) (receipt : Receipt) (response : StepResult)
    (state : Backend.State) (valid : Valid tree state) (emitted : Journal.Emits tree response state) :
    Checked (Valid tree) (Replay.queue.complete location response)
      (fun _ worker final => worker = ⟨(), none⟩ ∧ FinalStored response final)
      ⟨(), some (location, receipt)⟩ state := by
  have published : Checked (Valid tree)
      (match response with
        | .runnable locations => forIn locations PUnit.unit enqueueBody
        | .done outcome => LeaseQueue.liftBackend (CompletionStore.write Replay.rawDb throw outcome))
      (fun _ worker final => worker = ⟨(), some (location, receipt)⟩ ∧ FinalStored response final)
      ⟨(), some (location, receipt)⟩ state := by
    cases response with
    | runnable locations =>
      simp only []
      rw [← Array.forIn_toList]
      exact (enqueue_list_checked locations.toList _ state valid
        (fun item member => emitted item (by simpa using member))).weaken
        (fun _ _ _ same => ⟨same, trivial⟩)
    | done outcome =>
      change outcome = tree.exit at emitted
      subst outcome
      exact (write_completed tree reflexive state valid).leased valid
        (fun _ _ _ _ growth stored => growth.completed _ stored) _
  have acknowledge (current : Backend.State) (kept : Valid tree current) (stored : FinalStored response current) :
      Checked (Valid tree) (do
        let _ ← LeaseQueue.liftBackend (Replay.transport.acknowledge receipt)
        modify fun worker : Replay.Worker => { worker with delivery := none })
        (fun _ worker final => worker = ⟨(), none⟩ ∧ FinalStored response final)
        ⟨(), some (location, receipt)⟩ current := by
    apply Checked.bind ((acknowledge_checked tree receipt current).leased kept
      (fun _ _ _ _ _ _ => trivial) _) kept
    intro accepted worker acknowledged bounded later result
    obtain ⟨rfl, _⟩ := result
    exact .pure fun final finalValid last => ⟨(), ⟨(), none⟩, rfl, rfl, stored.grow (later.trans last)⟩
  unfold Replay.queue LeaseQueue.toWorkQueue
  simp only []
  have get : Checked (Valid tree) (get : StateT Replay.Worker Replay.M Replay.Worker)
      (fun value worker _ => value = ⟨(), some (location, receipt)⟩ ∧ worker = value)
      ⟨(), some (location, receipt)⟩ state := .pure fun _ _ _ => ⟨_, _, rfl, rfl, rfl⟩
  apply Checked.bind get valid
  intro value worker current kept growth done
  obtain ⟨rfl, rfl⟩ := done
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have published := published.mono (fun a b => a.trans b) growth
  cases response <;> apply Checked.bind published kept <;>
    intro ignored worker final bounded later result <;>
    obtain ⟨rfl, stored⟩ := result <;>
    exact acknowledge final bounded stored

end LeanCloud.Backend.Proofs.Worker
