import LeanCloud.ReplayModel

namespace LeanCloud.ReplayModel

theorem read_then (key : String) (next : Option ReplayRecord → ExceptT CloudError M α)
    (journal : Journal) :
    ((do let value ← store.read key; next value : ExceptT CloudError M α).run journal) =
      (next (journal.lookup key)).run journal := rfl

theorem lift_bind_run (action : M α) (next : α → ExceptT CloudError M β) (journal : Journal) :
    ((do let value ← action; next value : ExceptT CloudError M β).run journal) =
      (next (action.run journal).1).run (action.run journal).2 := rfl

theorem bind_run (action : ExceptT CloudError (StateM σ) α) (next : α → ExceptT CloudError (StateM σ) β)
    (journal : σ) :
    ((action >>= next).run journal) =
      match action.run journal with
      | (.ok value, after) => (next value).run after
      | (.error error, after) => (.error error, after) := by
  change (ExceptT.bindCont next (action journal).1) (action journal).2 = _
  simp only [ExceptT.run]
  cases action journal with
  | mk outcome after => cases outcome <;> rfl

@[simp] theorem pure_run (value : α) (journal : σ) :
    ((pure value : ExceptT CloudError (StateM σ) α).run journal) = (.ok value, journal) := rfl

@[simp] theorem get_run (journal : Journal) :
    ((get : ExceptT CloudError M Journal).run journal) = (.ok journal, journal) := rfl

@[simp] theorem set_run (after journal : Journal) :
    ((set after : ExceptT CloudError M Unit).run journal) = (.ok (), after) := rfl

/-- Every previously committed record retains its value. New keys may appear. -/
def Extends (before after : Journal) : Prop :=
  ∀ key record, before.lookup key = some record → after.lookup key = some record

theorem create_visible (journal : Journal) (key : String) (proposed : ReplayRecord) :
    let result := (store.create key proposed).run journal
    result.2.lookup key = some result.1 := by
  cases found : journal.lookup key <;> simp [store, StateT.run, found]

theorem Extends.refl (journal : Journal) : Extends journal journal := fun _ _ present => present

theorem Extends.trans {first middle last : Journal}
    (earlier : Extends first middle) (later : Extends middle last) : Extends first last :=
  fun key record present => later key record (earlier key record present)

theorem Extends.empty (journal : Journal) : Extends [] journal := by
  intro key record present
  simp at present

/-- Appending disjoint branch journals preserves every recorded value. -/
theorem Extends.append_left (left right : Journal) : Extends left (left ++ right) := by
  intro key record present
  simp [List.lookup_append, present]

theorem Extends.append_right (left right : Journal)
    (separate : ∀ entry ∈ left, ∀ other ∈ right, entry.1 ≠ other.1) :
    Extends right (left ++ right) := by
  intro key record present
  obtain ⟨before, after, contents, _⟩ := List.lookup_eq_some_iff.mp present
  have member : (key, record) ∈ right := by simp [contents]
  have missing : left.lookup key = none := List.lookup_eq_none_iff.mpr (by
    intro entry found
    exact bne_iff_ne.mpr (Ne.symm (separate entry found _ member)))
  simp [List.lookup_append, missing, present]

/-- Finite families with disjoint key regions have a common journal extension.
This is a mathematical union, not a runtime merge operation. -/
theorem merge_family (count : Nat) (journals : Fin count → Journal)
    (region : Fin count → String → Prop)
    (within : ∀ i entry, entry ∈ journals i → region i entry.1)
    (separate : ∀ i j, i ≠ j → ∀ key, region i key → region j key → False) :
    ∃ merged, (∀ i, Extends (journals i) merged) ∧
      ∀ entry ∈ merged, ∃ i, region i entry.1 := by
  induction count with
  | zero => exact ⟨[], fun i => Fin.elim0 i, by simp⟩
  | succ count ih =>
    obtain ⟨tail, grows, covered⟩ := ih (fun i => journals i.succ) (fun i => region i.succ)
      (fun i => within i.succ)
      (fun i j different => separate i.succ j.succ (by simpa using different))
    refine ⟨journals 0 ++ tail, ?_, ?_⟩
    · intro i
      refine Fin.cases (Extends.append_left _ _) (fun j => ?_) i
      apply (grows j).trans (Extends.append_right _ _ ?_)
      intro entry found other member same
      obtain ⟨k, inside⟩ := covered other member
      apply separate 0 k.succ (Ne.symm (Fin.succ_ne_zero k)) entry.1 (within 0 entry found)
      simpa [same] using inside
    · intro entry member
      rcases List.mem_append.mp member with first | rest
      · exact ⟨0, within 0 entry first⟩
      · obtain ⟨i, found⟩ := covered entry rest
        exact ⟨i.succ, found⟩

/-- Atomic create cannot invalidate an existing read, even for a competing key. -/
theorem create_extends (journal : Journal) (key : String) (proposed : ReplayRecord) :
    Extends journal ((store.create key proposed).run journal).2 := by
  intro oldKey record present
  cases found : journal.lookup key with
  | some existing => simpa [store, StateT.run, found] using present
  | none =>
    by_cases same : oldKey = key
    · subst oldKey; simp [found] at present
    · simp [store, StateT.run, found, List.lookup_cons, beq_eq_false_iff_ne.mpr same, present]

/-- A first write or a competing retry accepts the specified record and keeps
every stored entry within the expected journal. -/
theorem create_within (journal expected : Journal) (key : String) (record : ReplayRecord)
    (consistent : Extends journal expected) (known : expected.lookup key = some record) :
    let result := (store.create key record).run journal
    result.1 = record ∧ Extends result.2 expected := by
  cases found : journal.lookup key with
  | some existing =>
    have same : existing = record := Option.some.inj ((consistent key existing found).symm.trans known)
    subst existing
    simpa [store, StateT.run, found] using consistent
  | none =>
    simp only [store, StateT.run, found, true_and]
    intro oldKey oldRecord present
    by_cases same : oldKey = key
    · subst oldKey
      simp only [List.lookup_cons, beq_self_eq_true] at present
      cases present
      exact known
    · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr same] at present
      exact consistent oldKey oldRecord present

end LeanCloud.ReplayModel
