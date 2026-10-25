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
  combineLabel : String := "combine partitions"

/-- Contiguous, bounded batches preserve source order. The caller's recorded
worker count makes these boundaries stable across replay. -/
def batches (values : Array σ) (weight : σ → Nat) (workerCount : Nat)
    (cfg : Config) : Array (Array σ) := Id.run do
  let total := values.foldl (fun n value => n + max 1 (weight value)) 0
  let jobs := max 1 workerCount * max 1 cfg.batchesPerWorker
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

/- Each subtree returns one aggregate. Branches cover contiguous batch ranges;
the combiner always receives the left result before the right result. -/
private def tree [Codec β] (leaf : Array σ → Cloud m β)
    (combine : β → β → Cloud m β) (parts : Array (Array σ))
    (start count : Nat) : Cloud m β := Cloud.delay fun _ =>
  if count ≤ 1 then
    leaf (parts[start]?.getD #[])
  else do
    let half := count / 2
    let (left, right) ← Cloud.both
      (tree leaf combine parts start half)
      (tree leaf combine parts (start + half) (count - half))
    combine left right
termination_by count
decreasing_by all_goals omega

/-- Plan once using a recorded worker count, then reduce through binary forks.
Every leaf and internal combiner is a worker effect with a durable result. -/
private def reduce [Monad m] [MonadCloudExec m] [Codec β]
    (values : Array σ) (weight : σ → Nat) (cfg : Config)
    (leaf : Environment m → Array σ → m β)
    (combine : Environment m → β → β → m β) : Cloud m β := do
  let planning ← Cloud.exec (fun env => pure env.workers.size) "plan reduction"
  let parts := batches values weight planning cfg
  tree
    (fun batch => Cloud.exec (fun env => leaf env batch) cfg.label)
    (fun left right => Cloud.exec (fun env => combine env left right) cfg.combineLabel)
    parts 0 parts.size

end ReducerCloud

/-- A fused distributed producer. Leaves fold locally and finalize their
accumulators; parent workers combine the finalized results through a tree.
Only those results need a codec, so large accumulators can stay in blobs. -/
structure ReducerCloudM (m : Type → Type) (α : Type) where
  run : {ρ β : Type} → [Codec β] → ReducerCloud.Config → FoldSpec α ρ →
    (Environment m → ρ → m β) → (Environment m → β → β → m β) → Cloud m β

abbrev ReducerCloudIO := ReducerCloudM IO

namespace ReducerCloud

def ofPartitions [Monad m] [MonadCloudExec m] (values : Array σ)
    (read : Environment m → Array σ → ReducerParM m α)
    (weight : σ → Nat := fun _ => 1) : ReducerCloudM m α where
  run := fun cfg fold finish combine =>
    reduce values weight cfg (fun actual batch => do
      let value ← if batch.isEmpty then pure fold.unit else
        (read actual batch).run
          (LeanReducers.Config.forCPUs actual.currentWorker.cpus cfg.localConfig) fold
      finish actual value) combine

def ofArray [Monad m] [MonadCloudExec m] (values : Array α) : ReducerCloudM m α :=
  ofPartitions values fun _ batch => ReducerPar.ofArrayM (pure batch)

/-- Independent IO work over bounded batches, using the executing worker's CPU
budget. Each operation owns its resources; no IO exception triggers crash retry. -/
def ofArrayIO (values : Array σ) (read : Environment IO → σ → IO α)
    (weight : σ → Nat := fun _ => 1) : ReducerCloudIO α :=
  ofPartitions values (fun env batch => ReducerPar.ofArrayIO batch (read env)) weight

end ReducerCloud

namespace ReducerCloudM

def map (xs : ReducerCloudM m α) (f : α → β) : ReducerCloudM m β where
  run := fun cfg q finish combine => xs.run cfg
    { unit := q.unit, combine := q.combine, step := fun a rest => q.step (f a) rest } finish combine

def filter (xs : ReducerCloudM m α) (p : α → Bool) : ReducerCloudM m α where
  run := fun cfg q finish combine => xs.run cfg
    { q with step := fun a rest => if p a then q.step a rest else rest } finish combine

def flatMap (xs : ReducerCloudM m α) (f : α → ReducerSeq β) : ReducerCloudM m β where
  run := fun cfg q finish combine => xs.run cfg
    { unit := q.unit, combine := q.combine, step := fun a rest => (f a).run rest q.step } finish combine

/-- Fold leaves locally, finalize them, then combine pairs on cloud workers.
For grouping-independent results, `q` must be a compatible monoid fold and
`combine (finish a) (finish b)` must represent `finish (q.combine a b)`.
`finish q.unit` represents empty input. Both callbacks receive the executing
worker's environment and run as recorded effects; only `β` enters the journal. -/
@[cloud_func (descr := "Reduce tree") (opaque := true)]
def foldWith [Codec β] (xs : ReducerCloudM m α) (q : FoldSpec α ρ)
    (finish : Environment m → ρ → m β) (combine : Environment m → β → β → m β)
    (cfg : ReducerCloud.Config := {}) : Cloud m β :=
  xs.run cfg q finish combine

/-- Low-level monoid fold: `q.combine` must be associative with identity `q.unit`,
and `q.step a rest = q.combine (q.step a q.unit) rest`.
Prefer `reduceMap` when no specialized accumulator update is needed. -/
@[cloud_func (descr := "Reduce") (opaque := true)]
def fold [Monad m] [Codec ρ] (xs : ReducerCloudM m α) (q : FoldSpec α ρ)
    (cfg : ReducerCloud.Config := {}) : Cloud m ρ :=
  xs.run cfg q (fun _ value => pure value) (fun _ left right => pure (q.combine left right))

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

/-- Collect only bounded outputs such as manifests. Use `foldWith` to combine
large results through blob references instead of collecting them in the journal. -/
@[cloud_func (descr := "Collect") (opaque := true)]
def toArray [Monad m] [Codec α] (xs : ReducerCloudM m α)
    (cfg : ReducerCloud.Config := {}) : Cloud m (Array α) :=
  xs.run cfg { unit := ([] : List α), combine := (· ++ ·), step := (· :: ·) }
    (fun _ values => pure values.toArray)
    (fun _ left right => pure (left ++ right))

end ReducerCloudM

namespace ReducerCloudIO

def tryMap (xs : ReducerCloudIO α) (f : α → Except String β) : ReducerCloudIO β where
  run := fun cfg q finish combine => xs.run cfg {
    unit := Except.ok q.unit
    combine := fun left right => do return q.combine (← left) (← right)
    step := fun a rest => do return q.step (← f a) (← rest) }
    (fun env result => do finish env (← IO.ofExcept result)) combine

end ReducerCloudIO
end LeanCloud
