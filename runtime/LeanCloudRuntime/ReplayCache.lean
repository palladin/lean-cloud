import LeanCloud.ReplayStore
import Std.Sync.Mutex
import Init.Data.Queue

namespace LeanCloudRuntime.ReplayCache
open Lean LeanCloud

private abbrev Key := String × String

private structure Entry where
  encoded : String
  bytes : Nat

private structure State where
  entries : Std.HashMap Key Entry := {}
  order : Std.Queue Key := .empty
  bytes : Nat := 0
  generation : Nat := 0

/-- Disposable, per-node cache. Limits cover encoded records and keys, with a
separate entry bound for container overhead. FIFO eviction needs no hit bookkeeping.
Only confirmed immutable values are cached; missing records and storage errors are not. -/
structure Cache where
  private state : Std.Mutex State
  maxBytes : Nat
  maxEntries : Nat

def create (maxBytes := 64 * 1024 * 1024) (maxEntries := 4096) : IO Cache :=
  return ⟨← Std.Mutex.new {}, maxBytes, maxEntries⟩

def Cache.usage (cache : Cache) : IO (Nat × Nat) := cache.state.atomically do
  let state ← get
  return (state.entries.size, state.bytes)

private def remember (cache : Cache) (generation : Nat) (key : Key) (record : ReplayRecord) : IO Unit := do
  if cache.maxEntries == 0 || cache.maxBytes == 0 then return
  let encoded := (toJson record).compress
  let bytes := key.1.utf8ByteSize + key.2.utf8ByteSize + encoded.utf8ByteSize
  if bytes > cache.maxBytes then return
  cache.state.atomically do
    let mut state ← get
    -- An in-flight read/create must not refill a cache cleared by run removal.
    if state.generation != generation || state.entries.contains key then return
    while state.bytes + bytes > cache.maxBytes || state.entries.size ≥ cache.maxEntries do
      let some (old, order) := state.order.dequeue? | break
      if let some entry := state.entries[old]? then
        state := { state with entries := state.entries.erase old, bytes := state.bytes - entry.bytes }
      state := { state with order }
    set { state with
      entries := state.entries.insert key ⟨encoded, bytes⟩
      bytes := state.bytes + bytes
      order := state.order.enqueue key }

def Cache.remove (cache : Cache) (run : String) : IO Unit := cache.state.atomically do
  let mut state ← get
  for (key, entry) in state.entries do
    if key.1 == run then
      state := { state with entries := state.entries.erase key, bytes := state.bytes - entry.bytes }
  set { state with
    generation := state.generation + 1
    order := { eList := state.order.eList.filter (·.1 != run), dList := state.order.dList.filter (·.1 != run) } }

/-- Guard every operation, including hits. Writes always reach the durable store;
only its returned canonical value enters the cache after successful publication.
The cache belongs to one deployed node; run IDs isolate records within that node. -/
def Cache.records (cache : Cache) (run : String) (store : ReplayStore IO)
    (check : IO Unit) : ReplayStore IO where
  read key := do
    let (found, generation) ← cache.state.atomically do
      let state ← get
      return (state.entries[(run, key)]?, state.generation)
    check
    if let some entry := found then
      return some (← IO.ofExcept (Json.parse entry.encoded >>= fromJson?))
    let value ← store.read key
    if let some record := value then remember cache generation (run, key) record
    return value
  create key record := do
    let generation ← cache.state.atomically do return (← get).generation
    check
    let canonical ← store.create key record
    remember cache generation (run, key) canonical
    return canonical

end LeanCloudRuntime.ReplayCache
