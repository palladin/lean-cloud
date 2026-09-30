import LeanCloud.Proofs.Freshness

/-! A completion may report to its immediate parent or, after an obsolete-work
redirect, to an enclosing branch. These are relations on existing locations;
the runtime location representation is unchanged. -/

namespace LeanCloud.Location

def ReportsTo (source parent : Location) (index : Nat) : Prop :=
  0 < parent.size ∧ parent.entersChild source = true ∧ source[parent.size]!.1 = index

theorem ReportsTo.of_parent {source parent : Location} {index : Nat}
    (linked : source.parent? = some (parent, index)) : ReportsTo source parent index := by
  have nonempty := (parent_size linked).1
  obtain ⟨command, rfl⟩ := shape_of_parent linked
  exact ⟨nonempty, by simp [entersChild], by simp⟩

theorem ReportsTo.descendant {source middle parent : Location} {index : Nat}
    (report : ReportsTo middle parent index) (enters : middle.entersChild source = true) :
    ReportsTo source parent index := by
  exact ⟨report.1, entersChild_trans report.2.1 enters,
    (congrArg Prod.fst (entersChild_position enters parent.size (entersChild_size report.2.1))).trans report.2.2⟩

theorem ReportsTo.not_root {parent : Location} {index : Nat} : ¬ ReportsTo root parent index := by
  intro report
  have size := entersChild_size report.2.1
  have positive := report.1
  change parent.size < 1 at size
  omega

/-- A child's report is either to this fork at its original child index, or
to an enclosing branch of this fork. -/
theorem ReportsTo.child_cases {source parent : Location} {childIndex index : Nat}
    (report : ReportsTo (source.child childIndex) parent index) :
    (parent = source ∧ index = childIndex) ∨ ReportsTo source parent index := by
  obtain ⟨nonempty, enters, branch⟩ := report
  simp only [entersChild, child, Array.size_push, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at enters
  have bound : parent.size ≤ source.size := by omega
  rw [Array.extract_push_of_le bound] at enters
  by_cases equal : parent.size = source.size
  · have same : parent = source := by simpa [equal] using enters.2
    subst parent
    exact .inl ⟨rfl, by simpa [child] using branch.symm⟩
  · right
    have inside : parent.size < source.size := by omega
    refine ⟨nonempty, ?_, ?_⟩
    · simpa only [entersChild, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using And.intro inside enters.2
    · simpa [child, getElem!_pos, Array.getElem_push, inside, show parent.size < source.size + 1 by omega] using branch

/-- Advancing a command keeps all enclosing fork/child pairs unchanged. -/
theorem ReportsTo.of_next {source parent : Location} {index : Nat}
    (report : ReportsTo source.next parent index) : ReportsTo source parent index := by
  obtain ⟨nonempty, enters, branch⟩ := report
  have size := entersChild_size enters
  have sourceSize : 0 < source.size := by simp only [size_next] at size; omega
  obtain ⟨base, ⟨childIndex, command⟩, rfl⟩ := Array.exists_push_of_size_pos sourceSize
  rw [next_push] at enters branch
  simp only [entersChild, Array.size_push, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at enters
  have bound : parent.size ≤ base.size := by omega
  refine ⟨nonempty, ?_, ?_⟩
  · simpa only [entersChild, Array.size_push, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Array.extract_push_of_le bound] using enters
  · by_cases equal : parent.size = base.size
    · simpa [equal] using branch
    · have inside : parent.size < base.size := by omega
      simpa [getElem!_pos, Array.getElem_push, inside, show parent.size < base.size + 1 by omega] using branch

end LeanCloud.Location
