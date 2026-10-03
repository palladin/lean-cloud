import LeanCloud.Proofs.BackendRead

namespace LeanCloud.Backend.Proofs.Journal

abbrev Action := ExceptT CloudError (StateT Unit Replay.M)
abbrev workerDb := JournalDb.ofDb Replay.rawDb

/-- An interpreter action returns normally; protocol/infrastructure errors
remain in the executed code and must be ruled out by its preconditions. -/
def ActionChecked (expected : View) (action : Action α)
    (post : α → Backend.State → Prop) (state : Backend.State) : Prop :=
  Checked expected action.run
    (fun returned final => ∃ value, returned = .ok value ∧ post value final) state

theorem action_pure {expected : View} (value : α) (post : α → Backend.State → Prop)
    (state : Backend.State)
    (done : ∀ final, Valid expected final → Grows state final → post value final) :
    ActionChecked expected (pure value) post state :=
  checked_pure _ _ state fun final kept growth => ⟨value, rfl, done final kept growth⟩

theorem ActionChecked.bind {expected : View} {action : Action α} {next : α → Action β}
    {first : α → Backend.State → Prop} {post : β → Backend.State → Prop} {state : Backend.State}
    (safe : ActionChecked expected action first state) (kept : Valid expected state)
    (resume : ∀ value current, Valid expected current → Grows state current → first value current →
      ActionChecked expected (next value) post current) :
    ActionChecked expected (action >>= next) post state := by
  apply Checked.bind safe kept
  intro returned current currentValid growth result
  obtain ⟨value, rfl, result⟩ := result
  exact resume value current currentValid growth result

theorem ActionChecked.weaken {expected : View} {action : Action α}
    {first post : α → Backend.State → Prop} {state : Backend.State}
    (safe : ActionChecked expected action first state)
    (implies : ∀ value final, first value final → post value final) :
    ActionChecked expected action post state := by
  apply Checked.weaken safe
  intro returned final result
  obtain ⟨value, rfl, result⟩ := result
  exact ⟨value, rfl, implies value final result⟩

theorem ActionChecked.remember {expected : View} {action : Action α}
    {post : α → Backend.State → Prop} {state : Backend.State}
    (safe : ActionChecked expected action post state) :
    ActionChecked expected action (fun value final => Grows state final ∧ post value final) state := by
  apply Checked.weaken (Checked.remember safe)
  intro returned final result
  obtain ⟨growth, value, rfl, result⟩ := result
  exact ⟨value, rfl, growth, result⟩

theorem Checked.lift {expected : View} {action : StateT Unit Replay.M α}
    {post : α → Backend.State → Prop} {state : Backend.State}
    (safe : Checked expected action post state) (kept : Valid expected state)
    (stable : ∀ value before after, Grows before after → post value before → post value after) :
    ActionChecked expected (monadLift action) post state := by
  change Checked expected (action >>= fun value => pure (Except.ok (ε := CloudError) value)) _ state
  apply Checked.bind safe kept
  intro value current currentValid growth result
  apply checked_pure
  intro final finalValid later
  exact ⟨value, rfl, stable value current final later result⟩

theorem action_pure_bind (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

end LeanCloud.Backend.Proofs.Journal
