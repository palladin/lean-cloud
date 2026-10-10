import LeanCloud.Proofs.RecoveryStep

namespace LeanCloud.Proofs.RecoveryReads
open Lean ReplayFaults ReplayModel ReplayInterpreter WorkerRecovery

/-- Faulted reads of a valid return record have the ordinary lookup meaning. -/
theorem outcome (expected : Journal) (branch : Location) (value : Exit)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, value⟩)
    (valid : ∀ journal, pre journal → invariant journal ∧ Extends journal expected) :
    Ensures invariant pre (ReplayFaults.store.outcome branch)
      (fun found journal => pre journal ∧ found = (journal.lookup (ReplayStore.returnKey branch)).map (·.outcome)) := by
  unfold ReplayStore.outcome
  apply Ensures.read_bind _ _ (fun j h => (valid j h).1)
  intro found saved h
  cases found with
  | none => exact ⟨(valid _ h.1).1, Nat.le_refl _, h.1, by simp [← h.2]⟩
  | some record =>
    have same := Option.some.inj (((valid _ h.1).2 _ _ h.2.symm).symm.trans known)
    subst record
    simp only [beq_self_eq_true, ↓reduceIte]
    exact ⟨(valid _ h.1).1, Nat.le_refl _, h.1, by simp [← h.2]⟩

theorem children (expected : Journal) (location : Location) (indices : List Nat)
    (known : ∀ index ∈ indices, ∃ value,
      expected.lookup (ReplayStore.returnKey (location.child index)) = some ⟨ReplayStore.returnRequest, value⟩)
    (valid : ∀ journal, pre journal → invariant journal ∧ Extends journal expected) :
    Ensures invariant pre (Internal.readChildren ReplayFaults.store location indices)
      (fun found journal => pre journal ∧ found = indices.mapM
        (fun index => (journal.lookup (ReplayStore.returnKey (location.child index))).map (·.outcome))) := by
  induction indices generalizing pre with
  | nil => exact Ensures.pure (some []) (fun j h => ⟨(valid j h).1, h, rfl⟩)
  | cons index rest ih =>
    obtain ⟨value, present⟩ := known index (by simp)
    unfold Internal.readChildren
    apply (outcome expected (location.child index) value present valid).bind
    intro found
    cases found with
    | none =>
      apply Ensures.pure none
      intro journal ⟨valid', h, missing⟩
      exact ⟨valid', h, by simp [List.mapM_cons, ← missing]⟩
    | some value =>
      apply (ih (fun i hi => known i (by simp [hi]))
        (fun j (h : invariant j ∧ pre j ∧ some value = (j.lookup (ReplayStore.returnKey (location.child index))).map (·.outcome)) =>
          ⟨h.1, (valid j h.2.1).2⟩)).bind
      intro remaining
      apply Ensures.pure (remaining.map (value :: ·))
      intro journal ⟨valid', ⟨_, h, head⟩, got⟩
      refine ⟨valid', h, ?_⟩
      rw [List.mapM_cons, ← head, ← got]
      cases remaining <;> rfl

private theorem sequence_known (items : List κ) (found : κ → Option β) (expected : κ → β)
    (compatible : ∀ item ∈ items, ∀ value, found item = some value → value = expected item) :
    match items.mapM found with
    | none => ∃ item ∈ items, found item = none
    | some values => values = items.map expected := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have tail := ih (fun i hi => compatible i (by simp [hi]))
    simp only [List.mapM_cons]
    cases head : found item with
    | none => exact ⟨item, by simp, head⟩
    | some value =>
      have same := compatible item (by simp) value head
      subst value
      cases remaining : rest.mapM found with
      | none =>
        obtain ⟨i, hi, absent⟩ := (show ∃ i ∈ rest, found i = none from by simpa [remaining] using tail)
        exact ⟨i, by simp [hi], absent⟩
      | some values =>
        have same : values = rest.map expected := by simpa [remaining] using tail
        simp [same]

/-- A join either has the exact pure group outcome or names a missing child.
Crashes in these reads leave the caller's precondition intact. -/
theorem join (expected : Journal) (location : Location) (codec : Codec β) (count : Nat)
    (outcomes : Fin count → Except CloudError β)
    (known : ∀ index : Fin count, expected.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
    (valid : ∀ journal, pre journal → invariant journal ∧ Extends journal expected) :
    Ensures invariant pre (Internal.tryJoin ReplayFaults.store location count)
      (fun result journal => pre journal ∧ match result with
        | none => ∃ index : Fin count, journal.lookup (ReplayStore.returnKey (location.child index)) = none
        | some value => value = Parallel.recorded (fun values => Json.arr (values.map codec.encode))
            ((Array.ofFn outcomes).mapM id)) := by
  unfold Internal.tryJoin
  apply (children expected location (List.range count)
    (fun i hi => ⟨_, known ⟨i, List.mem_range.mp hi⟩⟩) valid).bind
  intro found
  apply Ensures.pure (found.map (fun values => collect values.toArray))
  intro journal ⟨invariant', h, reads⟩
  refine ⟨invariant', h, ?_⟩
  let values (i : Nat) : Exit := if inside : i < count then Parallel.recorded codec.encode (outcomes ⟨i, inside⟩) else .success Json.null
  have certified := sequence_known (List.range count)
    (fun i => (journal.lookup (ReplayStore.returnKey (location.child i))).map (·.outcome)) values (by
      intro i hi value got
      cases present : journal.lookup (ReplayStore.returnKey (location.child i)) with
      | none => simp [present] at got
      | some record =>
        have same := Option.some.inj (((valid journal h).2 _ _ present).symm.trans (known ⟨i, List.mem_range.mp hi⟩))
        subst record
        simpa [present, values, List.mem_range.mp hi] using (Option.some.inj (by simpa [present] using got)).symm)
  rw [← reads] at certified
  cases found with
  | none =>
    obtain ⟨i, hi, absent⟩ := certified
    refine ⟨⟨i, List.mem_range.mp hi⟩, ?_⟩
    simpa using absent
  | some results =>
    dsimp only [Option.map_some]
    rw [certified]
    have ordered : ((List.range count).map values).toArray = (Array.ofFn outcomes).map (Parallel.recorded codec.encode) := by
      apply Array.ext
      · simp
      · intro i left right
        have inside : i < count := by simpa using left
        simp [values, inside]
    rw [ordered, Parallel.collect_matches_direct]

end LeanCloud.Proofs.RecoveryReads
