import LeanCloud.Proofs.CompletionView
import LeanCloud.Proofs.CompletionCode

/-! Recovery of child completion, including interruption between saving its
own result, publishing its parent slot, and caching the completed group. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean CrashModel CrashRecovery JournalAdapter JournalDb ReplayInterpreter.Internal

/-- A completed child remains durable during every parent-publication attempt. -/
def ChildFinished (initial expected : Journal) (current : Location) (outcome : Exit)
    (journal : Journal) : Prop :=
  Between initial expected journal ∧ CompletedAt journal current.key outcome

theorem ChildFinished.grow {initial expected before after : Journal} {current : Location} {outcome : Exit}
    (valid : ChildFinished initial expected current outcome before)
    (growth : Extends before after) (bound : Extends after expected) :
    ChildFinished initial expected current outcome after :=
  ⟨valid.1.grow growth bound, valid.2.grow growth⟩

private theorem publishParent_spec {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (comparable : Comparable expected) :
    Spec (ChildFinished initial expected current outcome)
      (publishParent db parent (children.set! index (some outcome))
        (Result.settle (children.set! index (some outcome))))
      (fun response journal => ChildFinished initial expected current outcome journal ∧
        JournalDb.get raw parent.key journal =
          (some (toJson (Result.settle (children.set! index (some outcome)))), journal) ∧
        response = completionResponse parent (Result.settle (children.set! index (some outcome))))
      (ChildFinished initial expected current outcome) := by
  let slots := children.set! index (some outcome)
  let invariant := ChildFinished initial expected current outcome
  let marked := fun journal => invariant journal ∧
    journal (childKey parent.key index) = some (toJson outcome)
  have first := save_preserves expected invariant parent (.suspended slots)
    (layout.slots_agree comparable) (fun _ h => h.1.2) (fun _ _ h growth bound => h.grow growth bound)
  have slot_present (journal : Journal) (recorded : Published (records parent.key (.suspended slots)) journal) :
      journal (childKey parent.key index) = some (toJson outcome) := by
    exact (published_fork recorded).2 index (by simpa [slots] using layout.inside) outcome
      (Array.getElem!_set!_self _ _ _ layout.inside)
  have publish_slot : Spec invariant (save db parent (.suspended slots))
      (fun _ journal => marked journal) invariant :=
    first.weaken (fun _ h => h) (fun _ journal h => ⟨h.1, slot_present journal h.2⟩) (fun _ h => h)
  have cache : Spec marked
      (if let .completed _ := Result.settle slots then save db parent (Result.settle slots) else pure ())
      (fun _ journal => marked journal) marked := by
    cases settled : Result.settle slots with
    | suspended values =>
      exact (Spec.pure marked ()).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)
    | completed result =>
      apply (save_preserves expected marked parent (.completed result)
        (layout.cache_agrees comparable result settled) (fun _ h => h.1.1.2)
        (fun _ _ h growth bound => ⟨h.1.grow growth bound, growth _ _ h.2⟩)).weaken
        (fun _ h => h) (fun _ _ h => h.1) (fun _ h => h)
  have last : Spec marked (readParent db parent)
      (fun response journal => invariant journal ∧
        JournalDb.get raw parent.key journal = (some (toJson (Result.settle slots)), journal) ∧
        response = completionResponse parent (Result.settle slots)) invariant := by
    unfold readParent
    apply Spec.bind ((load_spec parent marked
      (fun record journal => record = some (Result.settle slots) ∧ marked journal)
      (fun journal h => ⟨some (Result.settle slots), layout.parent_updated journal h.1.1 h.2, rfl, h⟩)).weaken
        (fun _ h => h) (fun _ _ h => h) (fun _ h => h.1))
    intro record start h
    rcases h with ⟨rfl, kept, stored⟩
    have view := layout.parent_updated start.durable kept.1 stored
    change JournalDb.get raw parent.key start.durable = (some (toJson (Result.settle slots)), start.durable) at view
    cases settled : Result.settle slots with
    | suspended values => rw [settled] at view; exact ⟨Nat.le_refl _, .runnable #[], rfl, kept, view, rfl⟩
    | completed result => rw [settled] at view; exact ⟨Nat.le_refl _, .runnable #[parent], rfl, kept, view, rfl⟩
  unfold publishParent
  apply publish_slot.bind
  intro _
  cases settled : Result.settle (children.set! index (some outcome)) with
  | suspended values =>
    simpa only [show Result.settle slots = .suspended values from settled] using last
  | completed result =>
    have cached := cache.weaken (fun _ h => h) (fun _ _ h => h) (fun _ h => h.1)
    simp only [show Result.settle slots = .completed result from settled] at cached
    rw [show Result.settle slots = .completed result from settled] at last
    exact cached.bind (fun _ => last)

theorem notifyParent_spec {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true) :
    Spec (ChildFinished initial expected current outcome) (notifyParent db parent index outcome)
      (fun response journal => ChildFinished initial expected current outcome journal ∧
        JournalDb.get raw parent.key journal =
          (some (toJson (Result.settle (children.set! index (some outcome)))), journal) ∧
        response = completionResponse parent (Result.settle (children.set! index (some outcome))))
      (ChildFinished initial expected current outcome) := by
  let slots := children.set! index (some outcome)
  unfold notifyParent
  apply Spec.bind (load_spec parent (ChildFinished initial expected current outcome)
    (fun record journal => ∃ group, record = some group ∧
      ChildFinished initial expected current outcome journal ∧
      JournalDb.get raw parent.key journal = (some (toJson group), journal) ∧
      (group = .suspended children ∧ journal (childKey parent.key index) = none ∨
        group = Result.settle slots)) (fun journal valid => by
      obtain ⟨group, view, kind⟩ := layout.parent_view journal valid.1
      exact ⟨some group, view, group, rfl, valid, view, kind⟩))
  intro record start h
  rcases h with ⟨group, rfl, kept, view, fresh | already⟩
  · rcases fresh with ⟨rfl, _⟩
    simp only [Result.recordChild_missing children index outcome layout.inside layout.missing, pure_bind]
    exact publishParent_spec layout comparable start kept
  · subst group
    cases settled : Result.settle slots with
    | completed result =>
      rw [settled] at view
      exact ⟨Nat.le_refl _, .runnable #[parent], rfl, kept, view, rfl⟩
    | suspended values =>
      have same := Result.settle_suspended settled
      subst values
      have duplicate := Result.recordChild_existing slots index outcome
        (by simpa [slots] using layout.inside)
        (Array.getElem!_set!_self _ _ _ layout.inside) sameExit
      rw [settled] at duplicate
      simp only [duplicate, pure_bind]
      have repeated : slots.set! index (some outcome) = slots := by
        simp only [slots, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
      rw [repeated]
      have published := publishParent_spec layout comparable
      change Spec _ (publishParent db parent slots (Result.settle slots)) _ _ at published
      rw [settled] at published
      exact published start kept

/-- The actual `finish` is safe at every physical read/write boundary. Normal
return retains the child's completion, records its settled parent view, and
returns exactly the parent work prescribed by that view. Interruption retains
the invariant required to retry, including partially committed publications. -/
theorem finish_child_spec {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (linked : current.parent? = some (parent, index))
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true) :
    Spec (Between initial expected) (finish db current outcome)
      (fun response journal => ChildFinished initial expected current outcome journal ∧
        JournalDb.get raw parent.key journal =
          (some (toJson (Result.settle (children.set! index (some outcome)))), journal) ∧
        response = completionResponse parent (Result.settle (children.set! index (some outcome))))
      (Between initial expected) := by
  have ownAgrees : Agrees (records current.key (.completed outcome)) expected := by
    apply agrees_of_published _ comparable
    intro entry member
    simp only [records, List.mem_singleton] at member
    subst entry
    exact layout.own
  have saved : Spec (Between initial expected) (save db current (.completed outcome))
      (fun _ journal => ChildFinished initial expected current outcome journal)
      (Between initial expected) := by
    apply (save_spec expected initial current (.completed outcome) ownAgrees).weaken (fun _ h => h)
    · intro _ journal h
      exact ⟨⟨h.1, h.2.1⟩, .cached (h.2.2 (resultKey current.key, toJson outcome) (by simp [records]))⟩
    · exact fun _ h => h
  have notify := (notifyParent_spec layout comparable sameExit).weaken
    (fun _ h => h) (fun _ _ h => h) (fun _ h => h.1)
  rw [finish_child_eq db current parent index outcome linked]
  apply (recordResult_spec layout.source layout.own sameExit (fun _ h => h) (fun _ h => h) saved).bind
  exact fun _ => notify

end LeanCloud.Proofs.ReplayRecovery
