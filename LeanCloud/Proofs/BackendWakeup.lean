import LeanCloud.Proofs.BackendFinish

/-! The latest child reread observes every earlier committed child result.
The ordering comes from specification snapshots, with no physical Db log or
multi-key snapshot-read requirement. -/

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalAdapter JournalDb ReplayRecovery

theorem notifications_wake (parent : Location) (outcomes : Array Exit)
    (nonempty : 0 < outcomes.size) (before final : Backend.State) (historyOrdered : Ordered final)
    (descriptor : view before (forkKey parent.key) = some (toJson outcomes.size))
    (responses : Fin outcomes.size → StepResult)
    (notified : ∀ i, Notification parent i.val outcomes[i] before final (responses i)) :
    ∃ i, responses i = .runnable #[parent] := by
  classical
  by_cases missing : ∃ i, responses i = .runnable #[parent]
  · exact missing
  apply False.elim
  have waiting : ∀ i : Fin outcomes.size, ∃ checked,
      Grows before checked ∧ Grows checked final ∧
      view checked (childKey parent.key i.val) = some (toJson outcomes[i]) ∧
      ∀ result, ¬ CompletedAt (view checked) parent.key result := by
    intro i
    have h := notified i
    generalize response : responses i = answer at h
    cases h with
    | wake result completed => exact False.elim (missing ⟨i, response⟩)
    | waiting checked started finished child incomplete =>
      exact ⟨checked, started, finished, child, incomplete⟩
  let checked i := (waiting i).choose
  have started i := (waiting i).choose_spec.1
  have finished i := (waiting i).choose_spec.2.1
  have child i := (waiting i).choose_spec.2.2.1
  have incomplete i := (waiting i).choose_spec.2.2.2
  obtain ⟨latest, ordered⟩ := Grows.latest nonempty checked final historyOrdered finished
  have settled : ∃ result, Result.settle (outcomes.map some) = .completed result := by
    rw [Result.settle_completed]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨result, settled⟩ := settled
  apply incomplete latest result
  refine .group (outcomes.map some) ?_ ?_ settled
  · simpa using started latest _ _ descriptor
  · intro index inside
    have bound : index < outcomes.size := by simpa using inside
    exact ⟨outcomes[index], by simp [getElem!_pos, bound], ordered ⟨index, bound⟩ _ _ (child ⟨index, bound⟩)⟩

/-- A partial read only republishes missing children. Children already present
at that publication point need no new notification. The remaining nonempty set
still cannot all return empty: its latest reread also sees the earlier slots. -/
theorem missing_notifications_wake (parent : Location) (outcomes : Array Exit)
    (before final : Backend.State) (historyOrdered : Ordered final)
    (descriptor : view before (forkKey parent.key) = some (toJson outcomes.size))
    (known : Fin outcomes.size → Prop)
    (recorded : ∀ i, known i → view before (childKey parent.key i.val) = some (toJson outcomes[i]))
    (missing : ∃ i, ¬ known i)
    (responses : Fin outcomes.size → StepResult)
    (notified : ∀ i, ¬ known i → Notification parent i.val outcomes[i] before final (responses i)) :
    ∃ i, ¬ known i ∧ responses i = .runnable #[parent] := by
  classical
  by_cases woken : ∃ i, ¬ known i ∧ responses i = .runnable #[parent]
  · exact woken
  apply False.elim
  obtain ⟨index, absent⟩ := missing
  have wait : ∃ checked, Grows before checked ∧ Grows checked final ∧
      ∀ outcome, ¬ CompletedAt (view checked) parent.key outcome := by
    have result := notified index absent
    generalize equal : responses index = response at result
    cases result with
    | wake outcome complete => exact False.elim (woken ⟨index, absent, equal⟩)
    | waiting checked started later _ incomplete => exact ⟨checked, started, later, incomplete⟩
  obtain ⟨checked, started, later, incomplete⟩ := wait
  let allResponses i := if known i then .runnable #[] else responses i
  have allNotified i : Notification parent i.val outcomes[i] before final (allResponses i) := by
    dsimp only [allResponses]
    split
    · rename_i present
      exact .waiting before (.refl _) (started.trans later) (recorded i present)
        (fun outcome complete => incomplete outcome (complete.grow started.reads))
    · rename_i absent
      exact notified i absent
  obtain ⟨i, wake⟩ := notifications_wake parent outcomes (Nat.zero_lt_of_lt index.isLt)
    before final historyOrdered descriptor allResponses allNotified
  by_cases present : known i
  · simp [allResponses, present] at wake
  · exact woken ⟨i, present, by simpa [allResponses, present] using wake⟩

end LeanCloud.Backend.Proofs.Journal
