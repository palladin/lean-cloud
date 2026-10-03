import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Pure
import LeanCloud.Proofs.ReplayModel

namespace LeanCloud.Proofs.Worker
open Lean ReplayModel ReplayInterpreter

/-- Reading a correctly encoded final record returns the original typed result. -/
theorem decode_recorded [codec : Codec α] (roundtrip : Pure.RoundTrips codec) (outcome : Except CloudError α) :
    (result (m := Id) (Parallel.recorded codec.encode outcome)).run = outcome := by
  dsimp only [Pure.RoundTrips] at roundtrip
  cases outcome <;> simp [result, Parallel.recorded, Internal.decode, roundtrip] <;> rfl

/-- Completing an unfinished branch persists its result before reporting done. -/
theorem finish_records_result (journal : Journal) (branch : Location) (outcome : Exit)
    (unfinished : journal.lookup (ReplayStore.returnKey branch) = none) :
    ((Internal.finish store branch outcome).run journal) =
      (.ok .done, (ReplayStore.returnKey branch, ⟨ReplayStore.returnRequest, outcome⟩) :: journal) := by
  simp only [Internal.finish, ReplayStore.finish, bind_assoc]
  erw [lift_bind_run]
  simp [store, StateT.run, unfinished]

theorem read_completed (journal : Journal) (branch : Location) (outcome : Exit)
    (present : journal.lookup (ReplayStore.returnKey branch) =
      some ⟨ReplayStore.returnRequest, outcome⟩) :
    ((store.outcome branch).run journal) = (.ok (some outcome), journal) := by
  simp only [ReplayStore.outcome]
  erw [read_then]
  simp [present]

/-- A join reads exactly the completed child records, in source order. It neither
executes a child again nor changes any global record. -/
theorem join_reads_children (journal : Journal) (location : Location) (count : Nat)
    (outcomes : Nat → Exit)
    (completed : ∀ index, index < count →
      journal.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    ((Internal.join store location count).run journal) =
      (.ok (collect ((Array.range count).map outcomes)), journal) := by
  simp only [Internal.join, bind_run]
  erw [mapM_readonly (Array.range count) _ outcomes journal (by
    intro index member
    rw [bind_run, read_completed journal _ _ (completed index (Array.mem_range.mp member))]
    rfl)]
  rfl

/-- Once the stored children agree with direct evaluation, the actual replay
join returns precisely its encoded result, including source-ordered failures. -/
theorem join_matches_direct (journal : Journal) (location : Location)
    (blobs : BlobStorage Id) (codec : Codec α) (count : Nat) (branches : Fin count → Cloud Id α)
    (completed : ∀ index : Fin count,
      journal.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest,
          Parallel.recorded codec.encode (DirectInterpreter.Internal.eval blobs (branches index)).run⟩) :
    let expected := (DirectInterpreter.Internal.evalControl blobs (.parallel codec count branches)).run
    ((Internal.join store location count).run journal) =
      (.ok (Parallel.recorded (fun values => Json.arr (values.map codec.encode)) expected), journal) := by
  let outcomes (index : Nat) : Exit :=
    if inside : index < count then
      Parallel.recorded codec.encode (DirectInterpreter.Internal.eval blobs (branches ⟨index, inside⟩)).run
    else .success Json.null
  have ready : ∀ index, index < count →
      journal.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest, outcomes index⟩ := by
    intro index inside
    simpa [outcomes, inside] using completed ⟨index, inside⟩
  rw [join_reads_children journal location count outcomes ready]
  have ordered : (Array.range count).map outcomes =
      (Array.ofFnM fun index => (DirectInterpreter.Internal.eval blobs (branches index)).run : Id _).map
        (Parallel.recorded codec.encode) := by
    have gathered : (Array.ofFnM fun index =>
        (DirectInterpreter.Internal.eval blobs (branches index)).run : Id _) =
        Array.ofFn (fun index => (DirectInterpreter.Internal.eval blobs (branches index)).run) :=
      Array.idRun_ofFnM
    rw [gathered]
    ext index inside
    · simp
    · have bound : index < count := by simpa using inside
      simp [outcomes, bound]
  rw [ordered, Parallel.parallel_join_matches_direct]

end LeanCloud.Proofs.Worker
