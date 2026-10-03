import LeanCloud.Proofs.Reconstruction
import LeanCloud.Proofs.CachedReplay
import LeanCloud.SimulationBackend

namespace LeanCloud.Proofs
open ReplayModel Reconstruction SimulationBackend

/-- Sim's global record creation preserves every previously committed record. -/
theorem simulated_create_extends (world : World) (key : String) (proposed : ReplayRecord) :
    Extends world.records (create key proposed world).2.records := by
  have same : (create key proposed world).2.records =
      ((store.create key proposed).run world.records).2 := by
    cases found : world.records.lookup key <;> simp [create, store, StateT.run, found]
  rw [same]
  exact create_extends world.records key proposed

/-- The same correctness invariant holds for one atomic Sim write, including a
competing attempt or an orphan committing after its worker has crashed. -/
theorem simulated_create_within (world : World) (expected : Journal) (key : String) (proposed : ReplayRecord)
    (consistent : Extends world.records expected) (known : expected.lookup key = some proposed) :
    let result := create key proposed world
    result.1 = proposed ∧ Extends result.2.records expected := by
  have accepted := create_within world.records expected key proposed consistent known
  cases found : world.records.lookup key <;>
    simpa [create, store, StateT.run, found] using accepted

/-- A write by any worker, including a late write from a crashed attempt, cannot
invalidate a prefix already available to another worker running the same program. -/
theorem simulated_write_preserves_prefix (world : World) (key : String) (proposed : ReplayRecord)
    {target current steps} {encode : α → Lean.Json} {program : Cloud (SimM World) α}
    {remainingEncode : β → Lean.Json} {remaining : Cloud (SimM World) β}
    (witness : Prefix world.records target encode program current steps remainingEncode remaining) :
    Prefix (create key proposed world).2.records target encode program current steps remainingEncode remaining :=
  witness.extend (simulated_create_extends world key proposed)

/-- A concurrent or late write also preserves a branch's cached intermediate
results, including the successful values needed by its continuation. -/
theorem simulated_write_preserves_cached_branch (world : World) (key : String) (proposed : ReplayRecord)
    {current steps outcome} {program : Cloud (SimM World) α}
    (cached : CachedReplay.Cached world.records current program outcome steps) :
    CachedReplay.Cached (create key proposed world).2.records current program outcome steps :=
  cached.extend (simulated_create_extends world key proposed)

/-- Retrying a record creation cannot replace a committed outcome. -/
theorem create_preserves_existing (world : World) (key : String)
    (existing proposed : ReplayRecord) (present : world.records.lookup key = some existing) :
    create key proposed world = (existing, world) := by
  simp [create, present]

/-- A successful create returns precisely the value visible at its key. -/
theorem create_is_visible (world : World) (key : String) (proposed : ReplayRecord) :
    let (accepted, after) := create key proposed world
    after.records.lookup key = some accepted := by
  cases h : world.records.lookup key with
  | none => simp [create, h]
  | some existing => simp [create, h]

/-- Repeating a committed create has no further effect on storage. -/
theorem create_is_idempotent (world : World) (key : String) (proposed retry : ReplayRecord) :
    let (accepted, after) := create key proposed world
    create key retry after = (accepted, after) := by
  exact create_preserves_existing _ _ _ _ (create_is_visible world key proposed)

end LeanCloud.Proofs
