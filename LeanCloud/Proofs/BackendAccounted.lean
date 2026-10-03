import LeanCloud.Proofs.BackendAccounting

namespace LeanCloud.Backend.Proofs.Accounting
open Lean LeanEff LeanCloud.Proofs
open Worker (checked_pure)

abbrev Checked (tree : ExecutionTree) (action : StateT σ Replay.M α)
    (post : α → σ → Backend.State → Prop) (worker : σ) (state : Backend.State) : Prop :=
  Worker.Checked (Valid tree) action post worker state

namespace Checked
export Worker.Checked (bind weaken leased except remember)
end Checked

def NoAck : {α : Type} → Request α → Prop
  | _, .acknowledge _ => False
  | _, _ => True

private theorem old_acknowledgement {α : Type} {operation : Request α} {before after value}
    (allowed : NoAck operation) (law : Commits before operation value after)
    (id : Nat) (message : Backend.Message) (stored : after.queue.messages[id]? = some message)
    (acked : message.acknowledged = true) : before.queue.messages[id]? = some message := by
  cases operation with
  | get key => obtain ⟨_, rfl⟩ := law; exact stored
  | put key actual =>
    cases value with
    | false => obtain ⟨_, rfl⟩ := law; exact stored
    | true => rw [law.2.2.1] at stored; exact stored
  | enqueue location =>
    obtain ⟨rfl, rfl⟩ := law
    rw [Array.getElem?_push] at stored
    split at stored
    · cases stored; cases acked
    · exact stored
  | dequeue =>
    cases value with
    | none => have same : after = before := law; subst after; exact stored
    | some pair => obtain ⟨_, _, _, _, _, rfl⟩ := law; exact stored
  | acknowledge receipt => cases allowed

theorem Valid.no_ack_commit {tree : ExecutionTree} {α : Type} {operation : Request α} {before after value}
    (valid : Valid tree before) (allowed : NoAck operation) (law : Commits before operation value after)
    (safe : Worker.Valid tree after) (growth : Worker.Grows before after) : Valid tree after := by
  refine ⟨safe, ?_⟩
  intro id message stored acknowledged
  exact (valid.retired id message (old_acknowledgement allowed law id message stored acknowledged) acknowledged).grow growth

theorem account {tree : ExecutionTree} {action : StateT σ Replay.M α}
    {post : α → σ → Backend.State → Prop} {worker state}
    (safe : Worker.Checked (Worker.Valid tree) action post worker state)
    (uses : Uses NoAck ((action worker).run)) : Checked tree action post worker state := by
  apply safe.refine NoAck uses (fun _ valid => valid.safety) (fun growth => growth)
  intro β operation allowed before value after valid law kept growth
  exact ⟨valid.no_ack_commit allowed law kept growth, growth⟩

private theorem raw_get_uses (key : String) : StateUses NoAck (Replay.rawDb.get key) :=
  fun _ => ⟨trivial, fun _ => trivial⟩

private theorem raw_put_uses (key : String) (value : Json) : StateUses NoAck (Replay.rawDb.put key value) :=
  fun _ => ⟨trivial, fun _ => trivial⟩

theorem next_uses (worker : Replay.Worker) : Uses NoAck ((Replay.queue.next worker).run) := by
  have read : StateUses NoAck (CompletionStore.read Replay.rawDb throw) := by
    unfold CompletionStore.read
    apply StateUses.bind (raw_get_uses _)
    intro value
    cases value with
    | none => exact .pure _
    | some value =>
      simp only []
      cases fromJson? (α := Exit) value <;> exact fun _ => Uses.pure _ _
  have next : StateUses NoAck Replay.queue.next := by
    unfold Replay.queue LeaseQueue.toWorkQueue
    apply StateUses.bind (fun _ => Uses.pure _ _)
    intro _
    apply StateUses.bind read.leased
    intro answer
    cases answer with
    | some outcome => exact .pure _
    | none =>
      have polled : StateUses NoAck Replay.transport.dequeue := fun _ => ⟨trivial, fun _ => trivial⟩
      apply StateUses.bind polled.leased
      intro delivery
      cases delivery with
      | none => exact .pure _
      | some pair =>
        obtain ⟨location, receipt⟩ := pair
        apply StateUses.bind (fun _ => Uses.pure _ _)
        intro _
        exact .pure _
  exact next worker

theorem write_uses (outcome : Exit) :
    Uses NoAck ((CompletionStore.write Replay.rawDb throw outcome ()).run) := by
  have write : StateUses NoAck (CompletionStore.write Replay.rawDb throw outcome) := by
    unfold CompletionStore.write
    apply StateUses.bind (StateUses.putSame Replay.rawDb _ _ (raw_get_uses _) (raw_put_uses _ _))
    intro accepted
    cases accepted <;> exact fun _ => Uses.pure _ _
  exact write ()

theorem next_checked (tree : ExecutionTree) (worker : Replay.Worker)
    (state : Backend.State) (valid : Valid tree state) :
    Checked tree Replay.queue.next (Worker.Next tree) worker state :=
  account (Worker.next_checked tree worker state valid.safety) (next_uses worker)

theorem write_checked (tree : ExecutionTree) (reflexive : (toJson tree.exit == toJson tree.exit) = true)
    (state : Backend.State) (valid : Valid tree state) :
    Checked tree (CompletionStore.write Replay.rawDb throw tree.exit)
      (fun _ _ final => Worker.completed final = some (toJson tree.exit)) () state :=
  account (Worker.write_completed tree reflexive state valid.safety) (write_uses tree.exit)

theorem step_checked {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true)
    (state : Backend.State) (valid : Valid tree state)
    (active : route.Activated (Journal.view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel)
    (worker : Replay.Worker) :
    ProgramSafe (Valid tree) Worker.Grows
      (fun returned final => ∃ response, returned = .ok (.ok response, worker) ∧
        Journal.Emits tree response final ∧ Journal.StepProgress tree current node state response final)
      (((ReplayInterpreter.Internal.step Replay.db Replay.noBlobs fuel program current).run worker).run) state := by
  have footprint := (Footprint.step fuel program supported current worker).mono
    (second := NoAck) (by intro β operation allowed; cases operation <;> trivial)
  apply (Worker.step_safe whole supported route comparable sameExit state valid.safety active fuel enough worker).refine
    NoAck footprint (fun _ valid => valid.safety) (fun growth => growth)
  intro β operation allowed before value after valid law kept growth
  exact ⟨valid.no_ack_commit allowed law kept growth, growth⟩

end LeanCloud.Backend.Proofs.Accounting
