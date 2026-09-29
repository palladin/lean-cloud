import LeanCloudTests.Support

namespace LeanCloudTests.ImmutableJournal
open Lean LeanCloud

structure Store where
  records : List (String × Json) := []
  writes : Array (String × Json) := #[]

/-- Each raw operation is atomic. The hook yields to another worker BEFORE a
put commits, giving reproducible interleavings without threads or timing races. -/
def raw (store : IO.Ref Store) (beforePut : String → IO Unit := fun _ => pure ()) : Db Unit IO where
  get key handle := return ((← store.get).records.lookup key, handle)
  put key value handle := do
    beforePut key
    store.modify fun state => {
      records := (key, value) :: state.records.filter (·.1 != key)
      writes := state.writes.push (key, value) }
    return (true, handle)

def put (db : Db Unit IO) (key : String) (value : Result) : IO Unit := do
  assertTrue (← db.put key (toJson value) ()).1 "Journal write rejected"

def read (db : Db Unit IO) (key : String) : IO Result := do
  let some value := (← db.get key ()).1 | throw (IO.userError "Journal record missing")
  match fromJson? value with
  | .ok result => return result
  | .error error => throw (IO.userError error)

def finish (db : Db Unit IO) (index : Nat) (outcome : Exit) : IO StepResult := do
  let (result, _) ← (ReplayInterpreter.Internal.finish db (Location.root.child index) outcome).run ()
  match result with
  | .ok result => return result
  | .error error => throw (IO.userError (reprStr error))

def runnable (result : StepResult) (locations : Array Location) : IO Unit :=
  match result with
  | .runnable actual => assertEq actual locations
  | .done _ => throw (IO.userError "Child reported root completion")

def left : Exit := .success (toJson (11 : Nat))
def right : Exit := .success (toJson (22 : Nat))
def complete : Result := Result.settle #[some left, some right]
def empty : Result := .suspended #[none, none]

def cases : Array TestCase := #[
  ⟨"journal/independent-stale-snapshots", do
    let store ← IO.mkRef ({} : Store)
    let db := JournalDb.ofDb (raw store)
    put db Location.root.key empty
    let first ← read db Location.root.key
    let second ← read db Location.root.key
    assertEq first second
    put db Location.root.key (.suspended #[some left, none])
    put db Location.root.key (.suspended #[none, some right])
    assertEq (← read db Location.root.key) complete
    let records := (← store.get).records
    assertEq (records.lookup Location.root.key) none "A shared parent array was stored"
    assertEq (records.lookup (JournalDb.childKey Location.root.key 0)) (some (toJson left))
    assertEq (records.lookup (JournalDb.childKey Location.root.key 1)) (some (toJson right))⟩,
  ⟨"journal/interleaved-child-completions", do
    for first in [0, 1] do
      let store ← IO.mkRef ({} : Store)
      let hook ← IO.mkRef (fun _ : String => pure () : String → IO Unit)
      let db := JournalDb.ofDb (raw store (fun key => do (← hook.get) key))
      put db Location.root.key empty
      let second := 1 - first
      let outcome (index : Nat) := if index == 0 then left else right
      let other ← IO.mkRef (none : Option StepResult)
      hook.set fun key => do
        if key == JournalDb.childKey Location.root.key first then
          hook.set (fun _ => pure ())
          other.set (some (← finish db second (outcome second)))
      let result ← finish db first (outcome first)
      let some other := (← other.get) | throw (IO.userError "Interleaving was not reached")
      runnable other #[]
      runnable result #[Location.root]
      assertEq (← read db Location.root.key) complete
      assertEq ((← store.get).records.lookup (JournalDb.childKey Location.root.key 0))
        (some (toJson left))
      assertEq ((← store.get).records.lookup (JournalDb.childKey Location.root.key 1))
        (some (toJson right))⟩,
  ⟨"journal/stale-fork-after-completion", do
    let store ← IO.mkRef ({} : Store)
    let hook ← IO.mkRef (fun _ : String => pure () : String → IO Unit)
    let db := JournalDb.ofDb (raw store (fun key => do (← hook.get) key))
    hook.set fun key => do
      if key == JournalDb.forkKey Location.root.key then
        hook.set (fun _ => pure ())
        put db Location.root.key empty
        runnable (← finish db 0 left) #[]
        runnable (← finish db 1 right) #[Location.root]
    -- This initialization read "absent" before the other worker completed.
    put db Location.root.key empty
    assertEq (← read db Location.root.key) complete
    assertTrue ((← store.get).records.lookup (JournalDb.resultKey Location.root.key)).isSome
      "Late fork initialization erased the completed result"⟩,
  ⟨"journal/all-children-have-physical-records", do
    let store ← IO.mkRef ({} : Store)
    let db := JournalDb.ofDb (raw store)
    put db Location.root.key empty
    runnable (← finish db 0 left) #[]
    runnable (← finish db 1 right) #[Location.root]
    let records := (← store.get).records
    assertEq (records.lookup (JournalDb.childKey Location.root.key 0)) (some (toJson left))
    assertEq (records.lookup (JournalDb.childKey Location.root.key 1)) (some (toJson right))
    assertTrue (records.lookup (JournalDb.resultKey Location.root.key)).isSome
      "Group completion was not cached after the final child record"
    let writes := (← store.get).writes.size
    runnable (← finish db 1 right) #[Location.root]
    assertEq (← store.get).writes.size writes "Duplicate completion rewrote physical records"⟩,
  ⟨"journal/conflicting-slot-and-arity", do
    let store ← IO.mkRef ({} : Store)
    let db := JournalDb.ofDb (raw store)
    put db Location.root.key (.suspended #[some left, none])
    let before := (← store.get).records
    assertEq (← db.put Location.root.key (toJson (Result.suspended #[some right, none])) ()).1 false
    assertEq (← store.get).records before
    assertEq (← db.put Location.root.key (toJson (Result.suspended #[none])) ()).1 false
    assertEq (← store.get).records before⟩,
  ⟨"journal/completed-value-is-stable", do
    let store ← IO.mkRef ({} : Store)
    let db := JournalDb.ofDb (raw store)
    put db "0:1" (.completed left)
    let before := (← store.get).records
    assertEq (← db.put "0:1" (toJson (Result.completed right)) ()).1 false
    assertEq (← store.get).records before
    assertEq (← read db "0:1") (.completed left)⟩,
  ⟨"journal/malformed-records", do
    for key in [JournalDb.forkKey Location.root.key, JournalDb.resultKey Location.root.key,
        JournalDb.childKey Location.root.key 0] do
      let store ← IO.mkRef ({} : Store)
      let underlying := raw store
      let db := JournalDb.ofDb underlying
      put db Location.root.key empty
      let _ ← underlying.put key (Json.str "bad") ()
      let (result, _) ← (ReplayInterpreter.Internal.load db Location.root).run ()
      assertError result .codec⟩
]

end LeanCloudTests.ImmutableJournal
