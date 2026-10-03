import LeanCloud.ReplayInterpreter

namespace LeanCloud.Proofs.ReplayModel

/-- A pure model of global replay records. It has no user-effect world, scheduler,
or queue. Proofs run the ordinary replay interpreter against these ports. -/
abbrev Journal := List (String × ReplayRecord)
abbrev M := StateM Journal

/-- The pure reference model has no user blob effects. Pure evaluation never
calls these operations; rejecting them also makes accidental use explicit. -/
def noBlobs : BlobStorage M where
  putBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩
  readBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩
  resolveBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩

def store : ReplayStore M where
  read key := fun journal => (journal.lookup key, journal)
  create key proposed := fun journal =>
    match journal.lookup key with
    | some existing => (existing, journal)
    | none => (proposed, (key, proposed) :: journal)

theorem read_then (key : String) (next : Option ReplayRecord → ExceptT CloudError M α)
    (journal : Journal) :
    ((do let value ← store.read key; next value : ExceptT CloudError M α).run journal) =
      (next (journal.lookup key)).run journal := rfl

theorem lift_bind_run (action : M α) (next : α → ExceptT CloudError M β) (journal : Journal) :
    ((do let value ← action; next value : ExceptT CloudError M β).run journal) =
      (next (action.run journal).1).run (action.run journal).2 := rfl

theorem bind_run (action : ExceptT CloudError M α) (next : α → ExceptT CloudError M β)
    (journal : Journal) :
    ((action >>= next).run journal) =
      match action.run journal with
      | (.ok value, after) => (next value).run after
      | (.error error, after) => (.error error, after) := by
  change (ExceptT.bindCont next (action journal).1) (action journal).2 = _
  simp only [ExceptT.run]
  cases action journal with
  | mk outcome after => cases outcome <;> rfl

@[simp] theorem pure_run (value : α) (journal : Journal) :
    ((pure value : ExceptT CloudError M α).run journal) = (.ok value, journal) := rfl

private theorem list_mapM_readonly (items : List α) (action : α → ExceptT CloudError M β)
    (expected : α → β) (journal : Journal)
    (reads : ∀ item ∈ items, (action item).run journal = (.ok (expected item), journal)) :
    ((items.mapM action).run journal) = (.ok (items.map expected), journal) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.mapM_cons]
    simp only [bind_run, reads item (by simp)]
    rw [ih (fun item member => reads item (by simp [member]))]
    rfl

/-- Reading a collection of existing results leaves the journal unchanged. -/
theorem mapM_readonly (items : Array α) (action : α → ExceptT CloudError M β)
    (expected : α → β) (journal : Journal)
    (reads : ∀ item ∈ items, (action item).run journal = (.ok (expected item), journal)) :
    ((items.mapM action).run journal) = (.ok (items.map expected), journal) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind, bind_run]
  rw [list_mapM_readonly _ _ _ _ (by simpa using reads)]
  simp [← Array.toList_map]

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

end LeanCloud.Proofs.ReplayModel
