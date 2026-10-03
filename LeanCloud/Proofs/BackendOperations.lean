import LeanCloud.Proofs.BackendInvariant

namespace LeanCloud.Backend.Proofs.Worker
open Lean LeanEff LeanCloud.Proofs

/-- Successful backend action with an explicit local handle. This retains both
error layers in the real execution and proves infrastructure errors unreachable. -/
def Checked (invariant : Backend.State → Prop) (action : StateT σ Replay.M α)
    (post : α → σ → Backend.State → Prop) (worker : σ) (state : Backend.State) : Prop :=
  ProgramSafe (invariant) Grows
    (fun returned final => ∃ value handle, returned = .ok (value, handle) ∧ post value handle final)
    ((action worker).run) state

theorem checked_pure {invariant : Backend.State → Prop} (value : α) (post : α → σ → Backend.State → Prop)
    (worker : σ) (state : Backend.State)
    (done : ∀ final, invariant final → Grows state final → post value worker final) :
    Checked invariant (pure value) post worker state :=
  .pure fun final valid growth => ⟨value, worker, rfl, done final valid growth⟩

theorem Checked.bind {invariant : Backend.State → Prop} {action : StateT σ Replay.M α}
    {next : α → StateT σ Replay.M β} {first : α → σ → Backend.State → Prop}
    {post : β → σ → Backend.State → Prop} {worker state}
    (safe : Checked invariant action first worker state) (valid : invariant state)
    (resume : ∀ value handle current, invariant current → Grows state current → first value handle current →
      Checked invariant (next value) post handle current) :
    Checked invariant (action >>= next) post worker state := by
  apply ProgramSafe.bind Grows.refl (fun a b => a.trans b) safe valid
  intro returned current kept growth done
  obtain ⟨value, handle, rfl, result⟩ := done
  exact resume value handle current kept growth result

theorem Checked.weaken {invariant : Backend.State → Prop} {action : StateT σ Replay.M α}
    {first post : α → σ → Backend.State → Prop} {worker state}
    (safe : Checked invariant action first worker state)
    (implies : ∀ value handle final, first value handle final → post value handle final) :
    Checked invariant action post worker state := by
  apply Safe.weaken safe
  intro returned final kept result
  obtain ⟨value, handle, rfl, result⟩ := result
  exact ⟨value, handle, rfl, implies value handle final result⟩

theorem Checked.leased {invariant : Backend.State → Prop} {action : StateT Unit Replay.M α}
    {post : α → Unit → Backend.State → Prop} {state}
    (safe : Checked invariant action post () state) (valid : invariant state)
    (stable : ∀ value handle before after, Grows before after → post value handle before → post value handle after)
    (worker : Replay.Worker) :
    Checked invariant (LeaseQueue.liftBackend action)
      (fun value handle final => handle = worker ∧ post value () final) worker state := by
  cases worker with
  | mk backend delivery =>
    cases backend
    apply ProgramSafe.bind Grows.refl (fun a b => a.trans b) safe valid
    intro returned current kept growth done
    obtain ⟨value, handle, rfl, result⟩ := done
    cases handle
    exact .pure fun final bounded later => ⟨value, _, rfl, rfl, stable value () current final later result⟩

theorem Checked.remember {invariant : Backend.State → Prop} {action : StateT σ Replay.M α}
    {post : α → σ → Backend.State → Prop} {worker state}
    (safe : Checked invariant action post worker state) :
    Checked invariant action (fun value handle final => Grows state final ∧ post value handle final) worker state := by
  apply Safe.weaken (Safe.remember safe (fun a b => a.trans b) state (Grows.refl _))
  intro returned final kept result
  obtain ⟨growth, value, handle, rfl, done⟩ := result
  exact ⟨value, handle, rfl, growth, done⟩

theorem Checked.except {invariant : Backend.State → Prop} {action : StateT σ Replay.M α}
    {post : α → σ → Backend.State → Prop} {worker state}
    (safe : Checked invariant action post worker state) (valid : invariant state)
    (stable : ∀ value handle before after, Grows before after → post value handle before → post value handle after) :
    Checked invariant ((liftM action : ExceptT ε (StateT σ Replay.M) α).run)
      (fun result handle final => ∃ value, result = .ok value ∧ post value handle final) worker state := by
  change Checked invariant (action >>= fun value => pure (Except.ok value)) _ worker state
  apply Checked.bind safe valid
  intro value handle current kept growth result
  exact checked_pure _ _ _ _ (fun _ _ later => ⟨value, rfl, stable value handle current _ later result⟩)

theorem completion_get (tree : ExecutionTree) (state : Backend.State) :
    Checked (Valid tree) (Replay.rawDb.get CompletionStore.key)
      (fun value _ final => match value with
        | none => True
        | some value => value = toJson tree.exit ∧ completed final = some value) () state := by
  apply Safe.request
  · intro current value after kept growth law
    obtain ⟨_, rfl⟩ := law
    exact ⟨kept, .refl _⟩
  · intro current value after kept growth law
    obtain ⟨observed, same⟩ := law
    subst after
    subst value
    apply Safe.pure
    intro final bounded later
    refine ⟨completed current, (), rfl, ?_⟩
    cases stored : completed current with
    | none => trivial
    | some value => exact ⟨kept.completed value stored, later.completed value stored⟩

theorem completion_put_preserves {tree before after accepted}
    (valid : Valid tree before)
    (law : Commits before (.put CompletionStore.key (toJson tree.exit)) accepted after) :
    accepted = true ∧ Valid tree after ∧ Grows before after ∧ completed after = some (toJson tree.exit) := by
  cases accepted with
  | false =>
    obtain ⟨conflict, _⟩ := law
    apply False.elim
    apply conflict
    cases stored : completed before with
    | none => exact .inl stored
    | some value => exact .inr (by rw [valid.completed value stored] at stored; exact stored)
  | true =>
    obtain ⟨stored, unchanged, queue, recorded⟩ := law
    have view : Journal.view after = Journal.view before := by
      funext key
      by_cases same : key = CompletionStore.key
      · simp [Journal.view, same]
      · simpa only [Journal.view, ite_eq_right same] using unchanged key same
    have journalGrowth : Journal.Grows before after := ⟨fun key value found => (congrFun view key).trans found,
      ⟨[after.records], by simp [Journal.history, Simulation.History.Store.states, recorded]⟩⟩
    refine ⟨rfl, ⟨?_, ?_, ?_, valid.ordered.write journalGrowth recorded, ?_⟩,
      ⟨journalGrowth, ?_, by rw [queue]; exact .refl _⟩, stored⟩
    · simpa only [Journal.Valid, view] using valid.journal
    · intro id message found
      rw [queue] at found
      rw [view]
      exact valid.messages id message found
    · intro value found
      exact Option.some.inj (found.symm.trans stored)
    · intro id message found
      rw [queue] at found
      exact (valid.published id message found).trans journalGrowth
    · intro value found
      rw [valid.completed value found]
      exact stored

theorem completion_put (tree : ExecutionTree) (state : Backend.State) :
    Checked (Valid tree) (Replay.rawDb.put CompletionStore.key (toJson tree.exit))
      (fun accepted _ final => accepted = true ∧ completed final = some (toJson tree.exit)) () state := by
  apply Safe.request
  · intro current accepted after kept growth law
    obtain ⟨_, bounded, later, _⟩ := completion_put_preserves kept law
    exact ⟨bounded, later⟩
  · intro current accepted after kept growth law
    obtain ⟨rfl, bounded, later, stored⟩ := completion_put_preserves kept law
    exact .pure fun final finalValid last => ⟨true, (), rfl, rfl, last.completed _ stored⟩

theorem completion_putSame (tree : ExecutionTree)
    (reflexive : (toJson tree.exit == toJson tree.exit) = true)
    (state : Backend.State) (valid : Valid tree state) :
    Checked (Valid tree) (JournalDb.putSame Replay.rawDb CompletionStore.key (toJson tree.exit))
      (fun accepted _ final => accepted = true ∧ completed final = some (toJson tree.exit)) () state := by
  unfold JournalDb.putSame
  apply Checked.bind (completion_get tree state) valid
  intro previous handle current kept growth result
  cases handle
  cases previous with
  | none => exact completion_put tree current
  | some value =>
    obtain ⟨rfl, stored⟩ := result
    apply checked_pure
    intro final bounded later
    exact ⟨reflexive, later.completed _ stored⟩

theorem read_completed (tree : ExecutionTree) (state : Backend.State) (valid : Valid tree state) :
    Checked (Valid tree) (CompletionStore.read Replay.rawDb throw)
      (fun answer _ final => match answer with
        | none => True
        | some outcome => outcome = tree.exit ∧ completed final = some (toJson outcome)) () state := by
  unfold CompletionStore.read
  apply Checked.bind (completion_get tree state) valid
  intro value handle current kept growth result
  cases handle
  cases value with
  | none => exact checked_pure _ _ _ _ (fun _ _ _ => trivial)
  | some value =>
    obtain ⟨rfl, stored⟩ := result
    simp only []
    rw [exit_roundtrip]
    exact checked_pure _ _ _ _ (fun _ _ later => ⟨rfl, later.completed _ stored⟩)

theorem write_completed (tree : ExecutionTree)
    (reflexive : (toJson tree.exit == toJson tree.exit) = true)
    (state : Backend.State) (valid : Valid tree state) :
    Checked (Valid tree) (CompletionStore.write Replay.rawDb throw tree.exit)
      (fun _ _ final => completed final = some (toJson tree.exit)) () state := by
  unfold CompletionStore.write
  apply Checked.bind (completion_putSame tree reflexive state valid) valid
  intro accepted handle current kept growth result
  cases handle
  obtain ⟨rfl, stored⟩ := result
  exact checked_pure _ _ _ _ (fun _ _ later => later.completed _ stored)

theorem enqueue_checked {tree location} (state : Backend.State)
    (active : tree.Activated (Journal.view state) location) :
    Checked (Valid tree) (Replay.transport.enqueue location) (fun _ _ _ => True) () state := by
  apply Safe.request
  · intro current value after kept growth law
    exact enqueue_preserves kept (active.grow growth.journal) law
  · intro current value after kept growth law
    cases value
    exact .pure fun _ _ _ => ⟨(), (), rfl, trivial⟩

theorem dequeue_checked (tree : ExecutionTree) (state : Backend.State) :
    Checked (Valid tree) Replay.transport.dequeue
      (fun value _ final => ∀ location receipt, value = some (location, receipt) →
        tree.Activated (Journal.view final) location ∧ Received location receipt final) () state := by
  apply Safe.request
  · intro current value after kept growth law
    have proved := dequeue_preserves kept law
    exact ⟨proved.1, proved.2.1⟩
  · intro current value after kept growth law
    have proved := dequeue_preserves kept law
    exact .pure fun final bounded later => ⟨value, (), rfl,
      fun location receipt same => ⟨(proved.2.2 location receipt same).1.grow later.journal,
        (proved.2.2 location receipt same).2.grow later⟩⟩

theorem acknowledge_checked (tree : ExecutionTree) (receipt : Receipt) (state : Backend.State) :
    Checked (Valid tree) (Replay.transport.acknowledge receipt) (fun _ _ _ => True) () state := by
  apply Safe.request
  · intro current value after kept growth law
    exact acknowledge_preserves kept law
  · intro current value after kept growth law
    exact .pure fun _ _ _ => ⟨value, (), rfl, trivial⟩

end LeanCloud.Backend.Proofs.Worker
