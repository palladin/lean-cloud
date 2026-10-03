import LeanCloud.Proofs.Specification
import LeanCloud.Proofs.Recording
import LeanCloud.Proofs.Resumption

namespace LeanCloud.Proofs.Segment
open Lean LeanEff ReplayModel ReplayInterpreter CachedReplay

/-- A worker only adds records from its pure specification. If it reports done,
its durable branch result is already present. Fuel exhaustion and suspension
also preserve all existing records. A fork names a specified parallel group
within the assigned branch. -/
structure Safe (expected : Journal) (branch : Location) (outcome : Exit)
    (before : Journal) (result : Except CloudError Progress × Journal) : Prop where
  grows : Extends before result.2
  consistent : Extends result.2 expected
  completed : result.1 = .ok .done → result.2.lookup (ReplayStore.returnKey branch) =
    some ⟨ReplayStore.returnRequest, outcome⟩
  forked : ∀ location count, result.1 = .ok (.fork location count) →
    branch = Location.branchStart location ∧ Specification.Group expected location count

private theorem finish_safe (journal expected : Journal) (branch : Location)
    (outcome : Exit) (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey branch) =
      some ⟨ReplayStore.returnRequest, outcome⟩) :
    Safe expected branch outcome journal
      ((Internal.finish store branch outcome).run journal) := by
  obtain ⟨after, grows, remains, present, finished⟩ := Recording.finish_within journal expected branch
    outcome consistent known
  rw [finished]
  exact ⟨grows, remains, (fun _ => present), by intro location count impossible; cases impossible⟩

/-- An assignment executes missing pure operations and replays existing records.
An authorized join additionally requires its completed children. Every write
agrees with the pure specification, even when execution runs out of fuel. -/
theorem segment_preserves_results (expected : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (encode : α → Json)
    (journal : Journal) (consistent : Extends journal expected) (fuel : Nat)
    (ready : assignment.joining = true → Recording.JoinReady expected journal assignment.location)
    {current : Location} {program : Cloud M α} {outcome}
    (meaning : Specification.Complete expected current program outcome)
    (branch : assignment.branch = Location.branchStart current)
    (known : expected.lookup (ReplayStore.returnKey assignment.branch) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩) :
    Safe expected assignment.branch (Parallel.recorded encode outcome) journal
      ((walk store blobs assignment fuel encode program current true).run journal) := by
  cases fuel with
  | zero =>
    exact ⟨.refl _, consistent, (by intro impossible; cases impossible), by intro location count impossible; cases impossible⟩
  | succ fuel =>
    cases meaning with
    | pure value =>
      simpa [walk, Parallel.recorded] using finish_safe journal expected assignment.branch (.success (encode value)) consistent known
    | fail error next =>
      simpa [walk, Parallel.recorded] using finish_safe journal expected assignment.branch (.failure error) consistent known
    | delay next rest =>
      simpa [walk] using segment_preserves_results expected blobs assignment encode journal consistent fuel ready rest branch known
    | exec codec label body next roundtrip present rest =>
      obtain ⟨after, grows, remains, recorded, continues⟩ :=
        Recording.exec_within encode journal expected blobs assignment current fuel codec label body next roundtrip consistent present
      rw [continues]
      have ih := segment_preserves_results expected blobs assignment encode after remains fuel
        (fun joining => (ready joining).extend grows) rest (by simpa using branch) known
      exact ⟨grows.trans ih.grows, ih.consistent, ih.completed, ih.forked⟩
    | parallelOk codec count branches next outcomes roundtrip children returned collected present rest =>
      rcases Recording.group_record_or_suspend encode journal expected blobs assignment current fuel codec count branches next _
          consistent present ready with suspended | ⟨after, grows, remains, recorded, continues⟩
      · rw [suspended]
        refine ⟨.refl _, consistent, (by intro impossible; cases impossible), ?_⟩
        intro location size same
        cases same
        exact ⟨branch, ⟨_, codec, outcomes, by simpa [collected, Parallel.recorded] using present, returned⟩⟩
      · rw [continues, Recording.group_success encode after blobs assignment current fuel codec count branches next _
          roundtrip (by simpa using Parallel.sequence_size _ _ collected) recorded]
        have ih := segment_preserves_results expected blobs assignment encode after remains fuel
          (fun joining => (ready joining).extend grows) rest (by simpa using branch) known
        exact ⟨grows.trans ih.grows, ih.consistent, ih.completed, ih.forked⟩
    | parallelError codec count branches next outcomes roundtrip children returned collected present =>
      rcases Recording.group_record_or_suspend encode journal expected blobs assignment current fuel codec count branches next _
          consistent present ready with suspended | ⟨after, grows, remains, recorded, continues⟩
      · rw [suspended]
        refine ⟨.refl _, consistent, (by intro impossible; cases impossible), ?_⟩
        intro location size same
        cases same
        exact ⟨branch, ⟨_, codec, outcomes, by simpa [collected, Parallel.recorded] using present, returned⟩⟩
      · rw [continues, Recording.group_failure encode after blobs assignment current fuel codec count branches next _ recorded]
        have finished := finish_safe after expected assignment.branch _ remains known
        exact ⟨grows.trans finished.grows, finished.consistent, finished.completed, finished.forked⟩
termination_by fuel

/-- Fresh assignments need no completed-child assumption: an unrecorded group
suspends for the scheduler instead of attempting to join. -/
theorem fresh_segment_preserves_results (expected : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (encode : α → Json) (fresh : assignment.joining = false)
    (journal : Journal) (consistent : Extends journal expected) (fuel : Nat)
    {current : Location} {program : Cloud M α} {outcome}
    (meaning : Specification.Complete expected current program outcome)
    (branch : assignment.branch = Location.branchStart current)
    (known : expected.lookup (ReplayStore.returnKey assignment.branch) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩) :
    Safe expected assignment.branch (Parallel.recorded encode outcome) journal
      ((walk store blobs assignment fuel encode program current true).run journal) :=
  segment_preserves_results expected blobs assignment encode journal consistent fuel
    (by intro joining; simp [fresh] at joining) meaning branch known

/-- The deployed worker entry point preserves correct records through prefix
reconstruction and new execution. A completed branch is safely reused, including
when another attempt persisted it before this worker began. -/
private theorem resumed_worker_preserves_results [Codec α] (expected journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (program : ι → Cloud M α) (input : ι) (fuel : Nat)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud M β} {prefixSteps outcome}
    (consistent : Extends journal expected)
    (valid : (!assignment.location.isEmpty && assignment.location[0]!.1 == 0) = true)
    (witness : Reconstruction.Prefix journal assignment.location Codec.encode (program input)
      Location.root prefixSteps remainingEncode remaining)
    (meaning : Specification.Complete expected assignment.location remaining outcome)
    (branch : assignment.branch = Location.branchStart assignment.location)
    (known : expected.lookup (ReplayStore.returnKey assignment.branch) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded remainingEncode outcome⟩)
    (ready : assignment.joining = true → Recording.JoinReady expected journal assignment.location) :
    let result := (step store blobs (prefixSteps + fuel) program input assignment).run journal
    Safe expected assignment.branch (Parallel.recorded remainingEncode outcome) journal result := by
  dsimp only
  cases found : journal.lookup (ReplayStore.returnKey assignment.branch) with
  | none =>
    rw [Reconstruction.step_resumes_at_location journal blobs assignment program input fuel valid found witness,
      Reconstruction.walk_at_assignment]
    exact segment_preserves_results expected blobs assignment remainingEncode journal consistent fuel ready meaning branch known
  | some record =>
    have same := Option.some.inj ((consistent _ _ found).symm.trans known)
    subst record
    rw [Reconstruction.completed_step_reuses_record journal blobs assignment program input
      (prefixSteps + fuel) _ valid found (by simp)]
    exact ⟨.refl _, consistent, (fun _ => found), by intro location count impossible; cases impossible⟩

/-- A worker assigned a recorded path in the original workflow preserves its
specified branch result. The continuation's meaning and return value follow
from the root specification; callers do not supply them separately. -/
theorem worker_preserves_results [codec : Codec α] (expected journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (program : ι → Cloud M α) (input : ι) (fuel : Nat)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud M β} {prefixSteps outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (consistent : Extends journal expected)
    (branch : assignment.branch = Location.branchStart assignment.location)
    (witness : Reconstruction.Prefix journal assignment.location codec.encode (program input)
      Location.root prefixSteps remainingEncode remaining)
    (ready : assignment.joining = true → Recording.JoinReady expected journal assignment.location) :
    ∃ expectedReturn,
      expected.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, expectedReturn⟩ ∧
      Safe expected assignment.branch expectedReturn journal
        ((step store blobs (prefixSteps + fuel) program input assignment).run journal) := by
  obtain ⟨result, resumed, returned⟩ := meaning.resume (by simpa using known) witness consistent
  rw [← branch] at returned
  have resumable : Reconstruction.Resumable journal codec.encode (program input) Location.root assignment.location :=
    ⟨β, remainingEncode, remaining, prefixSteps, witness⟩
  exact ⟨_, returned, resumed_worker_preserves_results expected journal blobs assignment program input fuel
    consistent resumable.valid_root witness resumed branch returned ready⟩

/-- The final result is a property of the global record, independent of which
worker completed it. No equality of external worlds is required. -/
theorem root_record_matches_direct [codec : Codec α] (expected journal : Journal) (blobs : BlobStorage M)
    (program : ι → Cloud M α) (input : ι) {outcome steps} (record : ReplayRecord)
    (meaning : Cached expected Location.root (program input) outcome steps)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (consistent : Extends journal expected)
    (completed : journal.lookup (ReplayStore.returnKey Location.root) = some record)
    (roundtrip : Pure.RoundTrips codec) :
    let expectedResult := ((DirectInterpreter.interpret blobs program input).run []).1
    (result (m := Id) (α := α) record.outcome).run = expectedResult := by
  have same := Option.some.inj ((consistent _ _ completed).symm.trans known)
  subst record
  have direct : ((DirectInterpreter.interpret blobs program input).run []).1 = outcome :=
    congrArg Prod.fst (congrFun (Pure.evaluation_matches_direct blobs meaning.evaluation) [])
  dsimp only
  rw [direct]
  exact Worker.decode_recorded roundtrip _

/-- Starting the actual worker at the root needs no assumed expected journal:
one exists for the pure program, and execution from any compatible storage
(including empty storage) preserves it. This is safety of one assignment;
scheduler progress and crash recovery are separate obligations. -/
theorem pure_root_preserves_results [codec : Codec α]
    (program : ι → Cloud M α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome) :
    ∃ expected,
      Specification.Complete expected Location.root (program input) outcome ∧
      expected.lookup (ReplayStore.returnKey Location.root) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩ ∧
      ∀ (blobs : BlobStorage M) journal fuel, Extends journal expected →
        Safe expected Location.root (Parallel.recorded codec.encode outcome) journal
          ((step store blobs fuel program input ⟨0, Location.root, Location.root, false⟩).run journal) := by
  obtain ⟨expected, complete, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  refine ⟨expected, complete, known, ?_⟩
  intro blobs journal fuel consistent
  obtain ⟨stored, returned, safe⟩ := worker_preserves_results expected journal blobs
    ⟨0, Location.root, Location.root, false⟩ program input fuel complete known consistent
    (by simp) (.here codec.encode _) (by simp)
  have same : stored = Parallel.recorded codec.encode outcome :=
    congrArg ReplayRecord.outcome (Option.some.inj (returned.symm.trans known))
  simpa only [same, Nat.zero_add] using safe

end LeanCloud.Proofs.Segment
