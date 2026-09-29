import LeanCloud.Proofs.TreeBranchCompletion
import LeanCloud.Proofs.TreeCausalPublication

/-! Causality through the existing parent-notification code. Its exact local
write interval permits reuse of the completion proof at every crash boundary. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- After the child completes, every possible new record in the notification
interval has its prerequisites. Other siblings are justified by their old slots. -/
theorem ChildLayout.causal_between {tree : ExecutionTree} {root current parent : Location}
    {children result next} {initial expected middle final : Journal} {index : Nat} {outcome : Exit} {slots : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome slots)
    (rootSize : 0 < root.size) (member : (parent, .fork children result next) ∈ tree.nodes root)
    (size : slots.size = children.length)
    (frame : ∀ key, key ≠ resultKey current.key → key ≠ childKey parent.key index → key ≠ resultKey parent.key →
      expected key = initial key)
    (progress : Between initial expected middle) (causal : tree.Causal root middle)
    (own : tree.Requires root (resultKey current.key) middle)
    (child : tree.Requires root (childKey parent.key index) middle)
    (interval : Between middle expected final) : tree.Causal root final := by
  apply causal.between interval
  intro key value recorded absent
  by_cases isOwn : key = resultKey current.key
  · subst key; exact own
  by_cases isChild : key = childKey parent.key index
  · subst key; exact child
  by_cases isParent : key = resultKey parent.key
  · subst key
    rw [layout.cache] at recorded
    cases settled : Result.settle (slots.set! index (some outcome)) with
    | suspended _ => rw [settled] at recorded; cases recorded
    | completed _ =>
      apply tree.requires_cache rootSize member
      intro selected
      obtain ⟨answer, present⟩ := Result.settle_filled settled selected.val (by simp [size])
      by_cases same : selected.val = index
      · exact (child parent children result next member).2 selected (by rw [same])
      · have inside : selected.val < slots.size := by rw [size]; exact selected.isLt
        have oldSlot : slots[selected.val]! = some answer := by
          simpa [getElem!_pos, inside, Ne.symm same] using present
        have old : initial (childKey parent.key selected.val) = some (toJson answer) := by
          simpa only [oldSlot, Option.map_some] using (layout.others selected.val inside same).1
        exact (causal _ _ (progress.1 _ _ old) parent children result next member).2 selected rfl
  · have old : initial key = some value := (frame key isOwn isChild isParent).symm.trans recorded
    have kept := progress.1 _ _ old
    rw [absent] at kept
    cases kept

/-- The actual parent notification preserves causality on success and on
interruption. Its existing proof also supplies the exact settled parent view. -/
theorem ChildLayout.notify_causal {tree : ExecutionTree} {root current parent : Location}
    {children result next} {initial expected middle : Journal} {index : Nat} {outcome : Exit} {slots : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome slots)
    (rootSize : 0 < root.size) (member : (parent, .fork children result next) ∈ tree.nodes root)
    (size : slots.size = children.length)
    (frame : ∀ key, key ≠ resultKey current.key → key ≠ childKey parent.key index → key ≠ resultKey parent.key →
      expected key = initial key)
    (progress : Between initial expected middle) (causal : tree.Causal root middle)
    (own : tree.Requires root (resultKey current.key) middle)
    (child : tree.Requires root (childKey parent.key index) middle)
    (recorded : CompletedAt middle current.key outcome)
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true) :
    Spec (· = middle) (notifyParent db parent index outcome)
      (fun response journal => ChildFinished initial expected current outcome journal ∧ tree.Causal root journal ∧
        JournalDb.get raw parent.key journal =
          (some (toJson (Result.settle (slots.set! index (some outcome)))), journal) ∧
        response = completionResponse parent (Result.settle (slots.set! index (some outcome))))
      (fun journal => ChildFinished initial expected current outcome journal ∧ tree.Causal root journal) := by
  apply (notifyParent_spec (layout.rebase progress) comparable sameExit).weaken
  · intro journal same
    subst journal
    exact ⟨⟨Extends.refl _, progress.2⟩, recorded⟩
  · intro response journal h
    exact ⟨⟨⟨progress.1.trans h.1.1.1, h.1.1.2⟩, h.1.2⟩,
      layout.causal_between rootSize member size frame progress causal own child h.1.1, h.2⟩
  · intro journal h
    exact ⟨⟨⟨progress.1.trans h.1.1, h.1.2⟩, h.2⟩,
      layout.causal_between rootSize member size frame progress causal own child h.1⟩

end LeanCloud.Proofs.ReplayRecovery
