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

end LeanCloud.Proofs.Worker
