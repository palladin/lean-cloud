import LeanCloud.Proofs.RecoveryProgress

namespace LeanCloud.Proofs.RecoveryDriver
open ReplayFaults ReplayModel JournalMerge JournalRegion RecoveryStep RecoveryBatch RecoveryProgress

structure Invariant (expected : Journal) (faults : Nat) (saved : Saved) : Prop where
  unique : Unique saved.journal
  consistent : Extends saved.journal expected
  bounded : FaultBound faults saved.workers

/-- Combine report handlers without losing records produced by earlier handlers. -/
private theorem collect {expected faults region} (reports : List (Assignment × ReplayFaults.Report))
    (handle : Assignment × ReplayFaults.Report → Backend (List Exit)) (initial : Saved)
    (valid : Invariant expected faults initial)
    (each : ∀ entry ∈ reports, ∀ saved, Writes region initial.journal saved.journal →
      Invariant expected faults saved → ∃ value after,
        (handle entry).run saved = (.ok [value], after) ∧
        Writes region saved.journal after.journal ∧ Invariant expected faults after ∧
        after.journal.lookup (ReplayStore.returnKey entry.1.branchStart) = some ⟨ReplayStore.returnRequest, value⟩ ∧
        expected.lookup (ReplayStore.returnKey entry.1.branchStart) = some ⟨ReplayStore.returnRequest, value⟩) :
    ∃ values after, (reports.mapM handle).run initial = (.ok (values.map List.singleton), after) ∧
      Writes region initial.journal after.journal ∧ Invariant expected faults after ∧
      Returned expected after.journal (reports.map Prod.fst) values := by
  induction reports generalizing initial with
  | nil => exact ⟨[], initial, rfl, .refl _ _, valid, .nil⟩
  | cons entry rest ih =>
    obtain ⟨value, middle, head, written, validMiddle, present, known⟩ :=
      each entry (by simp) initial (.refl _ _) valid
    obtain ⟨values, after, tail, restWrites, validAfter, returned⟩ := ih middle validMiddle
      (fun e he saved grows inv => each e (by simp [he]) saved (written.trans grows) inv)
    refine ⟨value :: values, after, ?_, written.trans restWrites, validAfter,
      .cons (restWrites.extends _ _ present) known returned⟩
    rw [List.mapM_cons]
    simp only [bind_run, head, tail, pure_run, List.map_cons]
    rfl

variable [Codec α] (source : Cloud WorkerM α)

/-- The coordinator terminates by descending to children or by consuming a
missing return record. Faults are consumed entirely inside the worker batches. -/
theorem run_correct {expected budget faults} (fuel : Nat) :
    ∀ (saved : Saved) (assignments : List Assignment) (depth : Nat),
      Invariant expected faults saved → Separate assignments →
      (∀ a ∈ assignments, Ready source expected budget saved.journal a.branchStart) →
      (∀ a ∈ assignments, depth ≤ a.branchStart.size) →
      budget + faults + rank expected saved.journal budget depth + 2 ≤ fuel →
      ∃ outcomes after, (RestartingParallelReplay.run source fuel assignments).run saved = (.ok outcomes, after) ∧
        Writes (Region assignments) saved.journal after.journal ∧ Invariant expected faults after ∧
        Returned expected after.journal assignments outcomes := by
  induction fuel with
  | zero => intro saved assignments depth valid separate ready depths enough; omega
  | succ fuel ih =>
    intro saved assignments depth valid separate ready depths enough
    obtain ⟨reports, merged, batch, written, consistent, bounded, order, correct⟩ :=
      workers_correct source (fuel := fuel + 1) ready separate valid.consistent valid.bounded (by omega) (by omega)
    have mergedValid : Invariant expected faults merged := ⟨unique_after written valid.unique, consistent, bounded⟩
    let handle : Assignment × ReplayFaults.Report → Backend (List Exit) := fun (assignment, report) => do
      match report with
      | .done outcome => return [outcome]
      | .fork location count =>
        let _ ← RestartingParallelReplay.run source fuel (children location count)
        RestartingParallelReplay.run source fuel [assignment]
    have handles : ∀ entry ∈ reports, ∀ state, Writes (Region assignments) merged.journal state.journal →
        Invariant expected faults state → ∃ value after,
          (handle entry).run state = (.ok [value], after) ∧
          Writes (Region assignments) state.journal after.journal ∧ Invariant expected faults after ∧
          after.journal.lookup (ReplayStore.returnKey entry.1.branchStart) = some ⟨ReplayStore.returnRequest, value⟩ ∧
          expected.lookup (ReplayStore.returnKey entry.1.branchStart) = some ⟨ReplayStore.returnRequest, value⟩ := by
      intro ⟨assignment, report⟩ member state grows inv
      have memberAssignment : assignment ∈ assignments := order ▸ List.mem_map.mpr ⟨(assignment, report), member, rfl⟩
      have active := (ready assignment memberAssignment).extend (written.trans grows).extends
      have described := reported_extend (correct (assignment, report) member) grows.extends
      have accumulated := written.trans grows
      cases report with
      | done value => exact ⟨value, state, rfl, .refl _ _, inv, described⟩
      | fork location count =>
        obtain ⟨same, childReady, index, missing⟩ := described
        change assignment.branchStart = Proofs.Location.branchStart location at same
        have parentDepth : depth ≤ location.size := by simpa [same] using depths assignment memberAssignment
        have childDepth (a) (ha : a ∈ children location count) : depth + 1 ≤ a.branchStart.size := by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
          simp only [LeanCloud.Location.child, Array.size_push]
          omega
        have readyChildren (a) (ha : a ∈ children location count) :
            Ready source expected budget state.journal a.branchStart := by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
          exact childReady ⟨i, List.mem_range.mp hi⟩
        have lower := (childReady index).depth
        simp only [LeanCloud.Location.child, Array.size_push] at lower
        have descends := descend (expected := expected) (length_le accumulated) (show depth < budget + 1 by omega)
        obtain ⟨childValues, joined, childrenRun, childWrites, joinedValid, childrenReturned⟩ :=
          ih state (children location count) (depth + 1) inv (children_separate location count)
            readyChildren childDepth (by omega)
        have childRegion : ∀ key, Region (children location count) key → Region assignments key :=
          fun key owned => ⟨assignment, memberAssignment, children_region same owned⟩
        have joinedWrites := accumulated.trans (childWrites.mono childRegion)
        have indexMember : (⟨0, location.child index⟩ : Assignment) ∈ children location count :=
          List.mem_map.mpr ⟨index.val, List.mem_range.mpr index.isLt, rfl⟩
        obtain ⟨value, present⟩ := childrenReturned.present indexMember
        have progressed := length_lt joinedWrites missing present
        have resumes := advanced (budget := budget) (depth := depth) progressed
          (size_bound joinedValid.unique joinedValid.consistent)
        obtain ⟨values, after, parentRun, parentWrites, afterValid, parentReturned⟩ :=
          ih joined [assignment] depth joinedValid (by simp [Separate])
            (by intro a ha; rw [List.mem_singleton.mp ha]; exact active.extend childWrites.extends)
            (by intro a ha; rw [List.mem_singleton.mp ha]; exact depths assignment memberAssignment)
            (by omega)
        cases parentReturned with
        | cons returned known rest =>
          cases rest
          refine ⟨_, after, ?_, (childWrites.mono childRegion).trans
            (parentWrites.mono (fun key ⟨a, ha, owned⟩ => ⟨a, (List.mem_singleton.mp ha).symm ▸ memberAssignment, owned⟩)),
            afterValid, returned, known⟩
          simp only [handle, bind_run, childrenRun, parentRun]
    obtain ⟨values, after, handled, restWrites, afterValid, returned⟩ := collect reports handle merged mergedValid handles
    refine ⟨values, after, ?_, written.trans restWrites, afterValid, order ▸ returned⟩
    rw [RestartingParallelReplay.run]
    change ((do let reports ← ReplayFaults.workers source (fuel + 1) assignments
                let values ← reports.mapM handle
                pure values.flatten : Backend (List Exit)).run saved) = _
    simp only [bind_run, batch]
    rw [handled]
    simp only [pure_run]
    exact congrArg (fun values => (Except.ok values, after)) (List.flatMap_singleton' values)

end LeanCloud.Proofs.RecoveryDriver
