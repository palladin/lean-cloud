import LeanCloud.Proofs.RecoveryWorker

namespace LeanCloud.Proofs.RecoveryBatch
open ReplayFaults ReplayModel JournalMerge JournalRegion RecoveryStep

/-- Retry scripts can only shrink, including scripts stored for idle branches. -/
def FaultBound (limit : Nat) (workers : List (Location × Faults)) : Prop :=
  ∀ entry ∈ workers, entry.2.remaining.length ≤ limit

theorem FaultBound.lookup {limit workers} (bounded : FaultBound limit workers) (branch : Location) :
    ((workers.lookup branch).getD {}).remaining.length ≤ limit := by
  cases found : workers.lookup branch with
  | none => simp
  | some faults =>
    obtain ⟨before, after, contents, _⟩ := List.lookup_eq_some_iff.mp found
    exact bounded (branch, faults) (by simp [contents])

theorem FaultBound.save {limit workers} (bounded : FaultBound limit workers) (reply : WorkerResult)
    (enough : reply.faults.remaining.length ≤ limit) : FaultBound limit (saveFaults workers reply) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | rest
  · exact enough
  · exact bounded entry (List.mem_filter.mp rest).1

theorem FaultBound.collect {limit workers} (bounded : FaultBound limit workers) (replies : List WorkerResult)
    (each : ∀ reply ∈ replies, reply.faults.remaining.length ≤ limit) :
    FaultBound limit (replies.foldl saveFaults workers) := by
  induction replies generalizing workers with
  | nil => exact bounded
  | cons reply rest ih =>
    exact ih (bounded.save reply (each reply (by simp))) (fun r hr => each r (by simp [hr]))

variable [Codec α] (source : Cloud WorkerM α)

/-- A worker's exported journal contains only its additions to the shared base. -/
theorem runWorker_correct {expected saved assignment budget fuel}
    (ready : Ready source expected budget saved.journal assignment.branchStart)
    (consistent : Extends saved.journal expected) (enoughFuel : budget ≤ fuel)
    (enoughRetries : ((saved.workers.lookup assignment.branchStart).getD {}).remaining.length < fuel) :
    let reply := runWorker source fuel saved assignment
    let after := reply.records ++ saved.journal
    reply.assignment = assignment ∧ Writes (Owns assignment.branchStart) saved.journal after ∧
      Extends after expected ∧ reply.faults.remaining.length ≤ ((saved.workers.lookup assignment.branchStart).getD {}).remaining.length ∧
      ∃ report, reply.result = .ok report ∧ ReportValid source expected budget assignment.branchStart report after := by
  have recovered := worker_recovers source ready consistent ((saved.workers.lookup assignment.branchStart).getD {}) enoughFuel enoughRetries
  have ignoresAttempt : worker fuel fuel (fun _ : Unit => source) () assignment =
      worker fuel fuel (fun _ : Unit => source) () ⟨0, assignment.branchStart⟩ := rfl
  unfold runWorker
  rw [ignoresAttempt]
  generalize executed : (worker fuel fuel (fun _ : Unit => source) () ⟨0, assignment.branchStart⟩).run
    ⟨saved.journal, (saved.workers.lookup assignment.branchStart).getD {}⟩ = result at recovered ⊢
  rcases result with ⟨result, finished⟩
  obtain ⟨writes, consistent, bounded, report, returned, valid⟩ := recovered
  simp only
  rw [executed]
  rw [← writes.records.1]
  exact ⟨rfl, writes, consistent, bounded, report, returned, valid⟩

/-- Sibling regions are disjoint, so all of their new records can be retained. -/
abbrev Separate (assignments : List Assignment) : Prop :=
  assignments.Pairwise (fun a b => ∀ key, Owns a.branchStart key → Owns b.branchStart key → False)

def Region (assignments : List Assignment) (key : String) : Prop :=
  ∃ assignment ∈ assignments, Owns assignment.branchStart key

/-- A fork was incomplete when this batch started. Child cursors and completed
results remain valid in the merged journal. -/
def Reported (expected : Journal) (budget : Nat) (before after : Journal)
    (assignment : Assignment) : ReplayFaults.Report → Prop
  | .done value => ReportValid source expected budget assignment.branchStart (.done value) after
  | .fork location count => assignment.branchStart = Proofs.Location.branchStart location ∧
      (∀ index : Fin count, Ready source expected budget after (location.child index)) ∧
      ∃ index : Fin count, before.lookup (ReplayStore.returnKey (location.child index)) = none

private theorem merge_only (items : List κ) (records : κ → Journal) (before : Journal) :
    (ParallelReplay.mergeChildren (items.map fun item => (.ok (), records item))).run before =
      match ReplayModel.merge before (items.flatMap records) with
      | .error error => (.error error, before)
      | .ok after => (.ok (), after) := by
  have noErrors (items : List κ) : (items.map fun item => ((Except.ok () : Except CloudError Unit), records item)).forM
      (fun pair => (liftExcept pair.1 : ExceptT CloudError ReplayModel.M Unit)) = pure () := by
    induction items with
    | nil => rfl
    | cons item rest ih =>
      change (do
        liftExcept (.ok ())
        (rest.map fun item => ((Except.ok () : Except CloudError Unit), records item)).forM
          (fun pair => (liftExcept pair.1 : ExceptT CloudError ReplayModel.M Unit))) = _
      rw [ih]
      rfl
  simp only [ParallelReplay.mergeChildren, bind_run, get_run, List.flatMap_map]
  cases merged : ReplayModel.merge before (items.flatMap records) with
  | error error => rfl
  | ok after =>
    change ((items.map fun item => ((Except.ok () : Except CloudError Unit), records item)).forM
      (fun pair => (liftExcept pair.1 : ExceptT CloudError ReplayModel.M Unit))).run after = _
    rw [noErrors]
    rfl

private theorem mapM_ok (items : List κ) (action : κ → Except ε β) (values : κ → β)
    (each : ∀ item ∈ items, action item = .ok (values item)) :
    items.mapM action = .ok (items.map values) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, each item (by simp), ih (fun i hi => each i (by simp [hi]))]
    rfl

theorem workers_correct {expected saved assignments budget faults fuel}
    (ready : ∀ assignment ∈ assignments, Ready source expected budget saved.journal assignment.branchStart)
    (separate : Separate assignments) (consistent : Extends saved.journal expected)
    (bounded : FaultBound faults saved.workers) (enoughFuel : budget ≤ fuel) (enoughRetries : faults < fuel) :
    ∃ reports after, (ReplayFaults.workers source fuel assignments).run saved = (.ok reports, after) ∧
      Writes (Region assignments) saved.journal after.journal ∧ Extends after.journal expected ∧
      FaultBound faults after.workers ∧ reports.map Prod.fst = assignments ∧
      ∀ entry ∈ reports, Reported source expected budget saved.journal after.journal entry.1 entry.2 := by
  let replies := runWorker source fuel saved
  let journals := fun assignment => (replies assignment).records ++ saved.journal
  let report := fun assignment => (replies assignment).result.toOption.getD (.done (.success Lean.Json.null))
  have each := fun assignment member => runWorker_correct source (ready assignment member) consistent enoughFuel
    (Nat.lt_of_le_of_lt (bounded.lookup assignment.branchStart) enoughRetries)
  have correct : ∀ assignment ∈ assignments,
      (replies assignment).result = .ok (report assignment) ∧
      ReportValid source expected budget assignment.branchStart (report assignment) (journals assignment) := by
    intro assignment member
    obtain ⟨_, _, _, _, value, result, valid⟩ := each assignment member
    simpa only [report, replies, result, Except.toOption, Option.getD_some] using And.intro result valid
  have apart : Separate assignments.reverse := by
    rw [Separate, List.pairwise_reverse]
    exact separate.imp (fun {a b} different key hb ha => different key ha hb)
  obtain ⟨merged, merges, grows, compatible, retained, writes⟩ := children_within assignments.reverse journals
    (fun a => Owns a.branchStart) saved.journal expected consistent
    (fun a ha => (each a (by simpa using ha)).2.2.1)
    (fun a ha => (each a (by simpa using ha)).2.1) apart
  have additions : ∀ a, newRecords saved.journal (journals a) = (replies a).records := by
    intro a
    simp [newRecords, journals]
  rw [merge_only] at merges
  simp only [additions] at merges
  have mergedEq : ReplayModel.merge saved.journal (assignments.reverse.flatMap fun a => (replies a).records) = .ok merged := by
    cases result : ReplayModel.merge saved.journal (assignments.reverse.flatMap fun a => (replies a).records) with
    | error error =>
      simp only [result] at merges
      have impossible := congrArg Prod.fst merges
      cases impossible
    | ok journal =>
      have same : journal = merged := congrArg Prod.snd (by simpa only [result] using merges)
      simp [same]
  let results := assignments.map fun a => (a, report a)
  let after : Saved := ⟨merged, (assignments.map replies).foldl saveFaults saved.workers⟩
  have succeeds : (assignments.map replies).mapM (fun r => r.result.map (r.assignment, ·)) = .ok results := by
    rw [List.mapM_map]
    apply mapM_ok
    intro a ha
    have assigned : (replies a).assignment = a := (each a ha).1
    simp only [Function.comp_def, (correct a ha).1, Except.map, assigned]
  refine ⟨results, after, ?_, ?_, compatible, ?_, ?_, ?_⟩
  · simp only [ReplayFaults.workers, ExceptT.run, List.map_map, Task.spawn, Function.comp_def]
    change collectWorkers saved (assignments.map replies) = _
    simp only [collectWorkers, ← List.map_reverse, List.flatMap_map, mergedEq, succeeds]
    rfl
  · exact writes.mono (fun key ⟨a, ha, owned⟩ => ⟨a, by simpa using ha, owned⟩)
  · apply bounded.collect
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact Nat.le_trans (each a ha).2.2.2.1 (bounded.lookup a.branchStart)
  · simp [results, Function.comp_def]
  · intro entry member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    have valid := (correct a ha).2
    have extension := retained a (by simpa using ha)
    cases value : report a with
    | done outcome =>
      simp only [value, ReportValid] at valid
      exact ⟨extension _ _ valid.1, valid.2⟩
    | fork location count =>
      simp only [value, ReportValid, ProgressValid] at valid
      refine ⟨valid.1, fun i => (valid.2.1 i).extend extension, ?_⟩
      obtain ⟨index, missing⟩ := valid.2.2
      refine ⟨index, ?_⟩
      cases found : saved.journal.lookup (ReplayStore.returnKey (location.child index)) with
      | none => rfl
      | some record =>
        have present := (each a ha).2.1.extends _ _ found
        rw [missing] at present
        contradiction

end LeanCloud.Proofs.RecoveryBatch

