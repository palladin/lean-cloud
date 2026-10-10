import LeanCloud.ParallelReplay
import LeanCloud.Proofs.JournalRegion

namespace LeanCloud.Proofs.JournalMerge
open ReplayModel ParallelReplay JournalRegion

/-- An execution only prepends fresh records in its assigned region. The old
journal is an unchanged, shared tail, not part of the worker's returned writes. -/
def Writes (region : String → Prop) (before after : Journal) : Prop :=
  ∃ records, after = records ++ before ∧ (records.map Prod.fst).Nodup ∧
    ∀ entry ∈ records, before.lookup entry.1 = none ∧ region entry.1

theorem Writes.refl (region : String → Prop) (journal : Journal) : Writes region journal journal :=
  ⟨[], rfl, by simp, by simp⟩

theorem Writes.records {region before after} (writes : Writes region before after) :
    after = newRecords before after ++ before ∧
    ((newRecords before after).map Prod.fst).Nodup ∧
    ∀ entry ∈ newRecords before after, before.lookup entry.1 = none ∧ region entry.1 := by
  obtain ⟨records, rfl, unique, valid⟩ := writes
  simp only [newRecords, List.length_append, Nat.add_sub_cancel_right, List.take_left]
  exact ⟨True.intro, unique, valid⟩

theorem Writes.mono {first second before after} (writes : Writes first before after)
    (inside : ∀ key, first key → second key) : Writes second before after := by
  obtain ⟨records, eq, unique, valid⟩ := writes
  exact ⟨records, eq, unique, fun entry member => ⟨(valid entry member).1, inside _ (valid entry member).2⟩⟩

theorem Writes.trans {region before middle after}
    (first : Writes region before middle) (second : Writes region middle after) :
    Writes region before after := by
  obtain ⟨left, rfl, uniqueLeft, validLeft⟩ := first
  obtain ⟨right, rfl, uniqueRight, validRight⟩ := second
  have absent : ∀ entry ∈ right, left.lookup entry.1 = none ∧ before.lookup entry.1 = none := by
    intro entry member
    have missing := (validRight entry member).1
    simpa [List.lookup_append] using missing
  refine ⟨right ++ left, by simp, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨uniqueRight, uniqueLeft, ?_⟩
    intro key member other found same
    obtain ⟨entry, inRight, rfl⟩ := List.mem_map.mp member
    obtain ⟨entry', inLeft, rfl⟩ := List.mem_map.mp found
    have different := List.lookup_eq_none_iff.mp (absent entry inRight).1 entry' inLeft
    simp [same] at different
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact ⟨(absent entry member).2, (validRight entry member).2⟩
    · exact validLeft entry member

theorem Writes.create (region : String → Prop) (journal : Journal) (key : String) (record : ReplayRecord)
    (inside : region key) : Writes region journal ((store.create key record).run journal).2 := by
  cases found : journal.lookup key with
  | some old => simpa [store, StateT.run, found] using Writes.refl region journal
  | none =>
    refine ⟨[(key, record)], by simp [store, StateT.run, found], by simp, ?_⟩
    intro entry member
    have eq := List.mem_singleton.mp member
    subst entry
    exact ⟨found, inside⟩

theorem lookup_member {journal : Journal} {key record}
    (found : journal.lookup key = some record) : (key, record) ∈ journal := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem member_lookup {journal : Journal} (unique : (journal.map Prod.fst).Nodup)
    (entry : String × ReplayRecord) (member : entry ∈ journal) : journal.lookup entry.1 = some entry.2 := by
  induction journal with
  | nil => simp at member
  | cons head tail ih =>
    have clean := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | inTail
    · cases entry; simp
    · have different : entry.1 ≠ head.1 := by
        intro same
        exact clean.1 (same ▸ List.mem_map.mpr ⟨entry, inTail, rfl⟩)
      cases head; cases entry; dsimp only at different; simp [List.lookup_cons, beq_eq_false_iff_ne.mpr different, ih clean.2 inTail]

theorem Writes.extends {region before after} (writes : Writes region before after) : Extends before after := by
  obtain ⟨records, rfl, _, valid⟩ := writes
  apply Extends.append_right
  intro entry member other found same
  have absent := List.lookup_eq_none_iff.mp (valid entry member).1 other found
  simp [same] at absent

/-- Every child supplies only its fresh prefix. Disjoint ownership makes their
concatenation a valid journal and preserves every child's result. -/
theorem children_within (items : List κ) (records : κ → Journal) (region : κ → String → Prop)
    (initial expected : Journal) (consistent : Extends initial expected)
    (valid : ∀ item ∈ items, Extends (records item) expected)
    (writes : ∀ item ∈ items, Writes (region item) initial (records item))
    (separate : items.Pairwise (fun i j => ∀ key, region i key → region j key → False)) :
    ∃ after,
      (mergeChildren (items.map fun item => (.ok (), newRecords initial (records item)))).run initial = (.ok (), after) ∧
      Extends initial after ∧ Extends after expected ∧
      (∀ item ∈ items, Extends (records item) after) ∧
      Writes (fun key => ∃ item ∈ items, region item key) initial after := by
  let additions := fun item => newRecords initial (records item)
  let combined := items.flatMap additions
  have each := fun item member => (writes item member).records
  have unique : (combined.map Prod.fst).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.map_flatMap, List.pairwise_flatMap]
    refine ⟨fun item member => (each item member).2.1, ?_⟩
    apply separate.imp_of_mem
    intro i j hi hj apart key hkey other hother same
    obtain ⟨entry, member, rfl⟩ := List.mem_map.mp hkey
    obtain ⟨entry', member', rfl⟩ := List.mem_map.mp hother
    exact apart entry.1 ((each i hi).2.2 entry member).2 (same ▸ ((each j hj).2.2 entry' member').2)
  have fresh : ∀ entry ∈ combined, initial.lookup entry.1 = none ∧ ∃ item ∈ items, region item entry.1 := by
    intro entry member
    obtain ⟨item, hi, member⟩ := List.mem_flatMap.mp member
    exact ⟨((each item hi).2.2 entry member).1, item, hi, ((each item hi).2.2 entry member).2⟩
  have unionWrites : Writes (fun key => ∃ item ∈ items, region item key) initial (combined ++ initial) :=
    ⟨combined, rfl, unique, fresh⟩
  have present : ∀ item ∈ items, Extends (records item) (combined ++ initial) := by
    intro item hi key record found
    rw [(each item hi).1, List.lookup_append] at found
    cases first : (additions item).lookup key with
    | none => exact unionWrites.extends key record (by simpa [additions, first] using found)
    | some value =>
      have eq : value = record := Option.some.inj (by simpa [additions, first] using found)
      subst value
      have member := lookup_member first
      have all : (key, record) ∈ combined := List.mem_flatMap.mpr ⟨item, hi, member⟩
      simp [List.lookup_append, member_lookup unique _ all]
  have compatible : Extends (combined ++ initial) expected := by
    intro key record found
    cases first : combined.lookup key with
    | none => exact consistent _ _ (by simpa [List.lookup_append, first] using found)
    | some value =>
      have eq : value = record := Option.some.inj (by simpa [List.lookup_append, first] using found)
      subst value
      obtain ⟨item, hi, member⟩ := List.mem_flatMap.mp (lookup_member first)
      have known := member_lookup (each item hi).2.1 (key, record) member
      apply valid item hi key record
      rw [(each item hi).1]
      simp [List.lookup_append, known]
  refine ⟨combined ++ initial, ?_, unionWrites.extends, compatible, present, unionWrites⟩
  have merged : merge initial combined = .ok (combined ++ initial) := by
    unfold merge
    rw [ite_eq_left ⟨unique, fun entry member => (fresh entry member).1⟩]
  have noErrors (xs : List κ) :
      (xs.map fun item => ((Except.ok () : Except CloudError Unit), additions item)).forM
        (fun pair => (liftExcept pair.1 : ExceptT CloudError M Unit)) = pure () := by
    induction xs with
    | nil => rfl
    | cons item rest ih =>
      change (do liftExcept (.ok ());
                 (rest.map fun item => ((Except.ok () : Except CloudError Unit), additions item)).forM
                   (fun pair => (liftExcept pair.1 : ExceptT CloudError M Unit))) = _
      rw [ih]
      rfl
  simp only [mergeChildren, bind_run, get_run, List.flatMap_map]
  rw [merged]
  change ((items.map fun item => ((Except.ok () : Except CloudError Unit), additions item)).forM
    (fun pair => (liftExcept pair.1 : ExceptT CloudError M Unit))).run (combined ++ initial) = _
  rw [noErrors]
  rfl

end LeanCloud.Proofs.JournalMerge

