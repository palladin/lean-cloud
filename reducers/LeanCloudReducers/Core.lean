import LeanCloud.Core
import LeanReducers

namespace LeanCloud
open LeanReducers

namespace ReducerCloud

structure Config where
  /-- More than one batch per worker helps balance uneven inputs. -/
  batchesPerWorker : Nat := 2
  maxBatchItems : Nat := 64
  /-- Source-defined units; blob sources use bytes. -/
  maxBatchWeight : Nat := 64 * 1024 * 1024
  localConfig : LeanReducers.Config := {}
  label : String := "reduce partition"

/-- Contiguous, bounded batches preserve source order. The caller's recorded
planning environment makes these boundaries stable across replay. -/
def batches (values : Array σ) (weight : σ → Nat) (env : Environment)
    (cfg : Config) : Array (Array σ) := Id.run do
  let total := values.foldl (fun n value => n + max 1 (weight value)) 0
  let jobs := max 1 env.workers.size * max 1 cfg.batchesPerWorker
  let target := max 1 (min cfg.maxBatchWeight ((total + jobs - 1) / jobs))
  let mut result := #[]
  let mut batch := #[]
  let mut used := 0
  for value in values do
    let size := max 1 (weight value)
    if !batch.isEmpty && (used + size > target || batch.size ≥ max 1 cfg.maxBatchItems) then
      result := result.push batch
      batch := #[]
      used := 0
    batch := batch.push value
    used := used + size
  if !batch.isEmpty then result := result.push batch
  return result

end ReducerCloud

/-- A fused distributed producer. Only finalized partition results need a
codec; accumulators and input elements stay inside workers. `finish` can store
a large accumulator in blobs and return its small immutable reference. -/
structure ReducerCloudM (m : Type → Type) (α : Type) where
  run : {ρ β : Type} → [Codec β] → ReducerCloud.Config → FoldSpec α ρ →
    (Environment → ρ → m β) → Cloud m (Array β)

abbrev ReducerCloudIO := ReducerCloudM IO

namespace ReducerCloud

def ofPartitions [Monad m] [MonadCloudExec m] (values : Array σ)
    (read : Environment → Array σ → ReducerParM m α)
    (weight : σ → Nat := fun _ => 1) : ReducerCloudM m α where
  run := fun cfg fold finish => Cloud.parallel fun planning =>
    (batches values weight planning cfg).map fun batch =>
      Cloud.exec (fun actual => do
        let value ← (read actual batch).run (LeanReducers.Config.forCPUs actual.currentWorker.cpus cfg.localConfig) fold
        finish actual value) cfg.label

def ofArray [Monad m] [MonadCloudExec m] (values : Array α) : ReducerCloudM m α :=
  ofPartitions values fun _ batch => ReducerPar.ofArrayM (pure batch)

/-- Independent IO work over bounded batches, using the executing worker's CPU
budget. Each operation owns its resources; no IO exception triggers crash retry. -/
def ofArrayIO (values : Array σ) (read : Environment → σ → IO α)
    (weight : σ → Nat := fun _ => 1) : ReducerCloudIO α :=
  ofPartitions values (fun env batch => ReducerPar.ofArrayIO batch (read env)) weight

end ReducerCloud

namespace ReducerCloudM

def map (xs : ReducerCloudM m α) (f : α → β) : ReducerCloudM m β where
  run := fun cfg q finish => xs.run cfg
    { unit := q.unit, combine := q.combine, step := fun a rest => q.step (f a) rest } finish

def filter (xs : ReducerCloudM m α) (p : α → Bool) : ReducerCloudM m α where
  run := fun cfg q finish => xs.run cfg
    { q with step := fun a rest => if p a then q.step a rest else rest } finish

def flatMap (xs : ReducerCloudM m α) (f : α → ReducerSeq β) : ReducerCloudM m β where
  run := fun cfg q finish => xs.run cfg
    { unit := q.unit, combine := q.combine, step := fun a rest => (f a).run rest q.step } finish

/-- Low-level optimized fold. The caller must ensure that `combine` is a monoid
and `step a rest = combine (step a unit) rest`. Finalization runs in the same
recorded effect as the local fold; only its result enters the journal. -/
@[cloud_func (descr := "Reduce partitions") (opaque := true)]
def foldPartitions [Codec β] (xs : ReducerCloudM m α) (q : FoldSpec α ρ)
    (finish : Environment → ρ → m β) (cfg : ReducerCloud.Config := {}) : Cloud m (Array β) :=
  xs.run cfg q finish

/-- Low-level fold with the same compatibility requirement as `foldPartitions`.
Prefer `reduceMap` when no specialized accumulator update is needed. -/
@[cloud_func (descr := "Reduce") (opaque := true)]
def fold [Monad m] [Codec ρ] (xs : ReducerCloudM m α) (q : FoldSpec α ρ)
    (cfg : ReducerCloud.Config := {}) : Cloud m ρ := do
  let parts ← xs.run cfg q (fun _ value => pure value)
  return parts.foldl q.combine q.unit

@[cloud_func (descr := "Map and reduce") (opaque := true)]
def reduceMap [Monad m] [Codec ρ] (xs : ReducerCloudM m α) (spec : MonoidSpec ρ)
    (f : α → ρ) (cfg : ReducerCloud.Config := {}) : Cloud m ρ :=
  xs.fold (FoldSpec.ofMonoid spec (fun a rest => spec.combine (f a) rest)) cfg

@[cloud_func (descr := "Sum") (opaque := true)]
def sum [Monad m] [Codec α] [Add α] [OfNat α 0] [LawfulAddMonoid α]
    (xs : ReducerCloudM m α) (cfg : ReducerCloud.Config := {}) : Cloud m α :=
  xs.reduceMap (MonoidSpec.additive α) id cfg

@[cloud_func (descr := "Count") (opaque := true)]
def length [Monad m] (xs : ReducerCloudM m α)
    (cfg : ReducerCloud.Config := {}) : Cloud m Nat :=
  (xs.map fun _ => (1 : Nat)).sum cfg

/-- Collect only bounded outputs such as manifests. Use `foldPartitions` to
write large results to blobs instead of collecting them into the journal. -/
@[cloud_func (descr := "Collect") (opaque := true)]
def toArray [Monad m] [Codec α] (xs : ReducerCloudM m α)
    (cfg : ReducerCloud.Config := {}) : Cloud m (Array α) := do
  let parts ← xs.run cfg { unit := ([] : List α), combine := (· ++ ·), step := (· :: ·) }
    (fun _ values => pure values.toArray)
  return parts.flatten

end ReducerCloudM

namespace ReducerCloudIO

def tryMap (xs : ReducerCloudIO α) (f : α → Except String β) : ReducerCloudIO β where
  run := fun cfg q finish => xs.run cfg {
    unit := Except.ok q.unit
    combine := fun left right => do return q.combine (← left) (← right)
    step := fun a rest => do return q.step (← f a) (← rest) }
    (fun env result => do finish env (← IO.ofExcept result))

end ReducerCloudIO
end LeanCloud
