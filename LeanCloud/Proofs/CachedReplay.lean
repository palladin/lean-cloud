import LeanCloud.Proofs.Worker
import LeanCloud.Proofs.Reconstruction

namespace LeanCloud.Proofs.CachedReplay
open Lean LeanEff ReplayModel ReplayInterpreter LeanCloud.Proofs.Pure

/-- All sequential and joined results on this evaluated path are already stored.
Child execution order is irrelevant: a recorded join permits skipping its children.
Branch completion itself is not assumed to exist. -/
inductive Cached {m : Type → Type u} [Monad m] (journal : Journal) :
    {α : Type} → Location → Cloud m α → Except CloudError α → Nat → Prop where
  | pure (value : α) : Cached journal current (EffF.pure value) (.ok value) 1
  | fail (error : CloudError) (next : ArrsF (Control m) α β) :
      Cached journal current (.impure (.fail error) next) (.error error) 1
  | delay (next : ArrsF (Control m) Unit α)
      (rest : Cached journal current (next.apply ()) outcome steps) :
      Cached journal current (.impure .delay next) outcome (steps + 1)
  | exec (codec : Codec α) (label : String) (body : Unit → α) (next : ArrsF (Control m) α β)
      (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ()))
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → m _)),
          .success (codec.encode (body ()))⟩)
      (rest : Cached journal current.next (next.apply (body ())) outcome steps) :
      Cached journal current
        (.impure (.sequential codec (.exec label (fun _ => pure (body ())))) next) outcome (steps + 1)
  | parallelOk (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : RoundTrips codec) (children : ∀ index, Evaluation (branches index) (outcomes index))
      (collected : (Array.ofFn outcomes).mapM id = .ok values)
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
          .success (Json.arr (values.map codec.encode))⟩)
      (rest : Cached journal current.next (next.apply values) outcome steps) :
      Cached journal current (.impure (.parallel codec count branches) next) outcome (steps + 1)
  | parallelError (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : RoundTrips codec) (children : ∀ index, Evaluation (branches index) (outcomes index))
      (collected : (Array.ofFn outcomes).mapM id = .error error)
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩) :
      Cached journal current (.impure (.parallel codec count branches) next) (.error error) 1

theorem Cached.evaluation {m : Type → Type u} [Monad m] {α : Type}
    {journal current} {program : Cloud m α} {outcome steps}
    (cached : Cached (m := m) journal current program outcome steps) : Evaluation program outcome := by
  induction cached with
  | pure value => exact .pure value
  | fail error next => exact .fail error next
  | delay next rest ih => exact .delay next ih
  | exec codec label body next roundtrip present rest ih => exact .exec codec label body next roundtrip ih
  | parallelOk codec count branches next outcomes roundtrip children collected present rest ih =>
    exact .parallelOk codec count branches next outcomes roundtrip children collected ih
  | parallelError codec count branches next outcomes roundtrip children collected present =>
    exact .parallelError codec count branches next outcomes roundtrip children collected

theorem Cached.extend {m : Type → Type u} [Monad m] {α : Type}
    {before after current} {program : Cloud m α} {outcome steps}
    (cached : Cached before current program outcome steps) (extension : Extends before after) :
    Cached after current program outcome steps := by
  induction cached with
  | pure value => exact .pure value
  | fail error next => exact .fail error next
  | delay next rest ih => exact .delay next ih
  | exec codec label body next roundtrip present rest ih =>
    exact .exec codec label body next roundtrip (extension _ _ present) ih
  | parallelOk codec count branches next outcomes roundtrip children collected present rest ih =>
    exact .parallelOk codec count branches next outcomes roundtrip children collected (extension _ _ present) ih
  | parallelError codec count branches next outcomes roundtrip children collected present =>
    exact .parallelError codec count branches next outcomes roundtrip children collected (extension _ _ present)

/-- A cached branch runs to completion and persists its witnessed pure result.
Only its return record is added; earlier effects and children are never repeated. -/
theorem cached_branch_completes (journal : Journal) (blobs : BlobStorage M) (assignment : Assignment)
    (encode : α → Json) {current : Location} {program : Cloud M α} {outcome steps}
    (cached : Cached journal current program outcome steps)
    (unfinished : journal.lookup (ReplayStore.returnKey assignment.branch) = none) (spare : Nat) :
    (walk store blobs assignment (steps + spare) encode program current true).run journal =
      (.ok .done, (ReplayStore.returnKey assignment.branch,
        ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩) :: journal) := by
  cases cached with
  | pure value =>
    simp [Nat.add_comm 1 spare, walk, Parallel.recorded, Worker.finish_records_result, unfinished]
  | fail error next =>
    simp [Nat.add_comm 1 spare, walk, Parallel.recorded, Worker.finish_records_result, unfinished]
  | delay next rest =>
    rw [Nat.add_right_comm _ 1 spare, walk]
    simpa using cached_branch_completes journal blobs assignment encode rest unfinished spare
  | exec codec label body next roundtrip present rest =>
    rw [Nat.add_right_comm _ 1 spare, walk]
    simp only [Bool.true_or]
    erw [read_then]
    simp [present, Internal.check, Internal.decode, roundtrip]
    exact cached_branch_completes journal blobs assignment encode rest unfinished spare
  | parallelOk codec count branches next outcomes roundtrip children collected present rest =>
    rw [Nat.add_right_comm _ 1 spare, walk]
    simp only [Bool.true_or]
    erw [read_then]
    have size := Parallel.sequence_size _ _ collected
    simp only [Array.size_ofFn] at size
    have decoded := roundtrip.array codec
    change ∀ values, (@instCodecArray _ codec).decode (Json.arr (values.map codec.encode)) = .ok values
      at decoded
    simp [present, Internal.check, Internal.decodeGroup, Internal.decode, decoded, size]
    exact cached_branch_completes journal blobs assignment encode rest unfinished spare
  | parallelError codec count branches next outcomes roundtrip children collected present =>
    rw [Nat.add_comm 1 spare, walk]
    simp only [Bool.true_or]
    erw [read_then]
    simp [present, Internal.check, Parallel.recorded, Worker.finish_records_result, unfinished]
termination_by steps

/-- Cached replay writes the same outcome as the direct interpreter. Direct
evaluation starts with an empty journal: no shared initial state is required.
The cache hypothesis concerns intermediate values, not the final return record. -/
theorem cached_branch_matches_direct (journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (encode : α → Json) {current : Location} {program : Cloud M α} {outcome steps}
    (cached : Cached journal current program outcome steps)
    (unfinished : journal.lookup (ReplayStore.returnKey assignment.branch) = none) (spare : Nat) :
    let expected := ((DirectInterpreter.interpret blobs (fun _ : Unit => program) ()).run []).1
    let (progress, after) := (walk store blobs assignment (steps + spare) encode program current true).run journal
    progress = .ok .done ∧ after.lookup (ReplayStore.returnKey assignment.branch) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded encode expected⟩ := by
  have direct := congrFun (evaluation_matches_direct blobs cached.evaluation) []
  change (DirectInterpreter.interpret blobs (fun _ : Unit => program) ()).run [] = (outcome, []) at direct
  dsimp only
  rw [direct, cached_branch_completes journal blobs assignment encode cached unfinished spare]
  simp

/-- The worker entry point reconstructs its assigned location, then completes the
cached branch with the direct result of that branch's remaining computation. -/
theorem resumed_branch_matches_direct [Codec α] (journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (program : ι → Cloud M α) (input : ι)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud M β} {prefixSteps steps outcome} (spare : Nat)
    (valid : (!assignment.location.isEmpty && assignment.location[0]!.1 == 0) = true)
    (unfinished : journal.lookup (ReplayStore.returnKey assignment.branch) = none)
    (witness : Reconstruction.Prefix journal assignment.location Codec.encode (program input)
      Location.root prefixSteps remainingEncode remaining)
    (cached : Cached journal assignment.location remaining outcome steps) :
    let expected := ((DirectInterpreter.Internal.eval blobs remaining).run []).1
    let fuel := prefixSteps + (steps + spare)
    let (progress, after) := (step store blobs fuel program input assignment).run journal
    progress = .ok .done ∧ after.lookup (ReplayStore.returnKey assignment.branch) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded remainingEncode expected⟩ := by
  dsimp only
  rw [Reconstruction.step_resumes_at_location journal blobs assignment program input
    (steps + spare) valid unfinished witness, Reconstruction.walk_at_assignment]
  exact cached_branch_matches_direct journal blobs assignment remainingEncode cached unfinished spare

/-- A whole workflow can be replayed from its cached intermediate results. Its
new root completion record contains exactly the direct interpreter's outcome. -/
theorem cached_replay_matches_direct [codec : Codec α] (journal : Journal) (blobs : BlobStorage M)
    (program : ι → Cloud M α) (input : ι) {outcome steps} (spare : Nat)
    (unfinished : journal.lookup (ReplayStore.returnKey Location.root) = none)
    (cached : Cached journal Location.root (program input) outcome steps) :
    let expected := ((DirectInterpreter.interpret blobs program input).run []).1
    let assignment : Assignment := ⟨0, Location.root, Location.root, false⟩
    let (progress, after) := (step store blobs (steps + spare) program input assignment).run journal
    progress = .ok .done ∧ after.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode expected⟩ := by
  have replay := resumed_branch_matches_direct journal blobs
    ⟨0, Location.root, Location.root, false⟩ program input spare
    (by decide) unfinished (.here codec.encode _) cached
  simpa only [Nat.zero_add, DirectInterpreter.interpret] using replay

end LeanCloud.Proofs.CachedReplay
