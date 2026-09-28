import LeanCloud.Proofs.SnapshotChildren
import Init.Data.List.Perm

/-! Queue publication laws for one selected branch. Work lists are compared by
permutation, so the environment retains freedom to choose its processing order. -/

namespace LeanCloud.Proofs
open Lean ReplayModel

def BranchEmission (owner : Parent) (status : Option (Except CloudError Json))
    (before : List Location) (target : Location) (response : StepResult) (after : List Location) : Prop :=
  match status with
  | none => ∃ published : Array Location,
      response = .runnable published ∧ after.Perm (published.toList ++ before.erase target)
  | some _ => response = branchResponse owner status [] ∧ before = [target] ∧ after = []

/-- Within a group, a completed child disappears from the child work list.
The enclosing group handles any parent join published by that completion. -/
def ChildrenEmission (owner : Parent) (status : Option (Except CloudError Json))
    (before : List Location) (target : Location) (response : StepResult) (after : List Location) : Prop :=
  match status with
  | none => BranchEmission owner none before target response after
  | some _ => response = branchResponse owner status [] ∧ after.Perm (before.erase target)

theorem BranchEmission.local {journal : Journal} {program : Cloud Id Json}
    {parent branch command status pending}
    (snapshot : ReplaySnapshot journal program parent branch command status pending) (owner : Parent) :
    BranchEmission owner status [commandLocation parent branch command] (commandLocation parent branch command)
      (branchResponse owner status pending) pending := by
  cases status with
  | none => exact ⟨pending.toArray, rfl, by simp⟩
  | some outcome =>
    have empty := snapshot.pending_empty
    have nil : pending = [] := by simpa using empty
    subst pending
    exact ⟨rfl, rfl, rfl⟩

theorem BranchEmission.children {owner status before target response after}
    (emission : BranchEmission owner status before target response after) :
    ChildrenEmission owner status before target response after := by
  cases status with
  | none => exact emission
  | some outcome =>
    obtain ⟨reply, rfl, rfl⟩ := emission
    exact ⟨reply, by simp⟩

theorem ChildrenEmission.append {owner status before target response after}
    (emission : ChildrenEmission owner status before target response after)
    (suffix : List Location) (selected : target ∈ before) :
    ChildrenEmission owner status (before ++ suffix) target response (after ++ suffix) := by
  cases status with
  | none =>
    obtain ⟨published, reply, changed⟩ := emission
    exact ⟨published, reply, by
      simpa only [List.erase_append_left suffix selected, List.append_assoc] using changed.append_right suffix⟩
  | some outcome =>
    exact ⟨emission.1, by simpa only [List.erase_append_left suffix selected] using emission.2.append_right suffix⟩

theorem ChildrenEmission.prepend {owner status before target response after}
    (emission : ChildrenEmission owner status before target response after)
    (leading : List Location) (notSelected : target ∉ leading) :
    ChildrenEmission owner status (leading ++ before) target response (leading ++ after) := by
  cases status with
  | none =>
    obtain ⟨published, reply, changed⟩ := emission
    refine ⟨published, reply, ?_⟩
    rw [List.erase_append_right before notSelected]
    exact (changed.append_left leading).trans (List.perm_append_comm_assoc _ _ _)
  | some outcome =>
    exact ⟨emission.1, by simpa only [List.erase_append_right before notSelected] using emission.2.append_left leading⟩

theorem array_set_missing {items : Array (Option α)} {index : Nat}
    (inside : index < items.size) (missing : items[index]! = none) : items.set! index none = items := by
  rw [← missing, getElem!_pos items index inside]
  simp [Array.set!, Array.setIfInBounds, inside]

private theorem child_reply (codec : Codec α) (parent : Location)
    (outcomes : Array (Option (Except CloudError α))) (index : Nat) (value : Except CloudError α) :
    branchResponse (.child parent index (outcomeSlots codec outcomes)) (some (value.map codec.encode)) [] =
      match (outcomes.set! index (some value)).mapM id with
      | none => .runnable #[]
      | some _ => .runnable #[parent] := by
  have shape : branchResponse (.child parent index (outcomeSlots codec outcomes)) (some (value.map codec.encode)) [] =
      (Parent.child parent index (outcomeSlots codec outcomes)).result (encodeOutcome codec value) := by
    cases value <;> rfl
  have changed := outcomeSlots_update codec outcomes index (some value)
  simp only [Option.map_some] at changed
  rw [shape, Parent.result, ← changed]
  cases collected : (outcomes.set! index (some value)).mapM id with
  | none => rw [outcomeSlots_waits _ _ collected]
  | some values =>
    rw [outcomeSlots_full _ _ _ collected]

/-- The group publishes its join exactly when the last missing child reports.
Otherwise only work internal to the selected child is published. -/
theorem ChildrenEmission.group {journal : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent outcomes index value after before target response}
    (children : ChildSnapshots journal codec branches parent 0 (outcomes.set! index value) after)
    (inside : index < outcomes.size) (missing : outcomes[index]! = none)
    (uncollected : outcomes.mapM id = none)
    (emission : ChildrenEmission (.child parent index (outcomeSlots codec outcomes))
      (value.map (Except.map codec.encode)) before target response after) (owner : Parent) :
    BranchEmission owner none before target response (groupPending parent (outcomes.set! index value) after) := by
  cases value with
  | none =>
    simpa only [Option.map_none, groupPending, array_set_missing inside missing, uncollected, ChildrenEmission, BranchEmission] using emission
  | some value =>
    obtain ⟨reply, changed⟩ := emission
    rw [Option.map_some, child_reply] at reply
    cases collected : (outcomes.set! index (some value)).mapM id with
    | none =>
      exact ⟨#[], by simpa only [collected] using reply,
        by simpa only [groupPending, collected, Array.toList_empty, List.nil_append] using changed⟩
    | some values =>
      have empty := children.pending_empty
      rw [collected] at empty
      have noChildren : after = [] := by simpa using empty
      have noRest : before.erase target = [] := by
        have length := changed.length_eq
        rw [noChildren] at length
        exact List.eq_nil_of_length_eq_zero length.symm
      refine ⟨#[parent], by simpa only [collected] using reply, ?_⟩
      simp only [groupPending, collected, noRest, List.append_nil]
      exact .refl _

end LeanCloud.Proofs
