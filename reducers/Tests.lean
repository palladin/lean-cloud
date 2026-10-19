import LeanCloudReducers
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay

open Lean LeanCloud LeanCloudRuntime LeanReducers
deriving instance BEq for Except

private def check (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try discard action; pure false catch _ => pure true
  check failed message

private def objects (data : Std.Mutex (Std.HashMap String ByteArray))
    (reads : Std.Mutex (Array String)) : ObjectStore where
  ensureContainer := pure ()
  read key := do
    reads.atomically (modify (·.push key))
    data.atomically do return (← get)[key]?
  create key bytes := data.atomically do
    if let some old := (← get)[key]? then return old
    modify (·.insert key bytes)
    return bytes
  erase key := data.atomically (modify (·.erase key))
  list _ := pure #[]

private def environment (cpus workers : Nat) : LeanCloud.Environment := {
  currentWorker := { id := "executing", cpus }
  workers := (Array.range workers).map fun i => { id := s!"worker{i}", cpus } }

private def direct (store : ObjectStore) (program : Cloud IO α)
    (env : LeanCloud.Environment := environment 4 3) : IO α := do
  let value ← (DirectInterpreter.Internal.eval store.storage program env).run
  IO.ofExcept (value.mapError (·.message))

private def journal (state : IO.Ref (List (String × ReplayRecord))) : ReplayStore IO where
  read key := return (← state.get).lookup key
  create key value := state.modifyGet fun records =>
    if let some old := records.lookup key then (old, records)
    else (value, (key, value) :: records)

private def generated (store : ObjectStore) : IO Unit := do
  for seed in [:40] do
    let values := (Array.range (seed * 3)).map fun i => (i * 7 + seed) % 29
    for width in [1, 7, 64] do
      let cfg : ReducerCloud.Config := { maxBatchItems := width, maxBatchWeight := width }
      let xs := (ReducerCloud.ofArray (m := IO) values).filter (fun n => n % 3 != 0)
        |>.flatMap (fun n => ReducerSeq.ofArray #[n, n + 1]) |>.map (· * 2)
      let expected := (values.filter (fun n => n % 3 != 0)).flatMap (fun n => #[n*2, (n+1)*2])
      check ((← direct store (xs.toArray cfg)) == expected) "Cloud fusion/order differs from sequential model"
      check ((← direct store (xs.sum cfg)) == expected.foldl (· + ·) 0) "Cloud sum differs from model"
  let calls ← Std.Mutex.new (0 : Nat)
  let source := ReducerCloud.ofArrayIO (Array.range 30) fun _ n => do
    calls.atomically (modify (· + 1))
    return n + 1
  check ((← calls.atomically get) == 0) "Reducer was eager"
  check ((← direct store source.toArray) == (Array.range 30).map (· + 1)) "IO producer order"
  IO.println "PASS generated sequential/multicore/cloud pipelines and ordered IO"

private def replay (store : ObjectStore) : IO Unit := do
  let calls ← Std.Mutex.new (0 : Nat)
  let program (_ : Unit) := (ReducerCloud.ofArrayIO (Array.range 9) fun env n => do
    calls.atomically (modify (· + 1))
    return (n, env.currentWorker.cpus)).toArray
  let log ← IO.mkRef []
  let records := journal log
  let step location env := (ReplayInterpreter.step records store.storage 10000 program ()
    ⟨0, location⟩ (environment := env)).run
  let .ok (.fork fork count) ← step Location.root (environment 2 3)
    | throw (IO.userError "Expected a partition fork")
  check (count > 1) "Cloud reducer did not distribute work"
  for i in [:count] do
    let .ok .done ← step (fork.child i) (environment 4 9)
      | throw (IO.userError "Partition failed")
  let .ok .done ← step Location.root (environment 8 1)
    | throw (IO.userError "Join failed after environment change")
  let before ← calls.atomically get
  let .ok .done ← step Location.root (environment 1 1)
    | throw (IO.userError "Completed replay failed")
  check ((← calls.atomically get) == before && before == 9) "Replay repeated recorded inputs"
  let .ok (some outcome) ← records.outcome.run | throw (IO.userError "No result")
  let actual := Id.run ((ReplayInterpreter.result (m := Id) (α := Array (Nat × Nat)) outcome).run)
  check (actual == .ok ((Array.range 9).map (fun n => (n, 4)))) "Planning/executing environments confused"
  let failedCalls ← Std.Mutex.new (0 : Nat)
  let failing (_ : Unit) := (ReducerCloud.ofArrayIO #[1, 2, 3] fun _ (_ : Nat) => do
    failedCalls.atomically (modify (· + 1))
    throw (IO.userError "valid application failure") : ReducerCloudIO Nat).sum
  let log ← IO.mkRef []
  let run := (SequentialReplay.interpret (journal log) store.storage 10000 failing ()).run
  let first ← run
  let before ← failedCalls.atomically get
  let second ← run
  check (first == .error ⟨.application, "valid application failure"⟩ && second == first &&
    (← failedCalls.atomically get) == before) "IO exception was treated as a node crash"
  IO.println "PASS stable partitions, replacement CPU budgets, replay and recorded failures"

private def blobs (store : ObjectStore) (reads : Std.Mutex (Array String)) : IO Unit := do
  -- More than two physical blob chunks, with a long line crossing a boundary.
  let long := String.ofList (List.replicate (Files.chunkSize + 17) 'x')
  let text := "α\n" ++ long ++ "\n" ++ String.ofList (List.replicate Files.chunkSize 'y') ++ "\n終\n"
  let file ← Files.putText store text
  let reader ← Files.openReader store file
  reads.atomically (set (#[] : Array String))
  let selected ← reader.read (Files.chunkSize - 3) 10
  check (selected == text.toUTF8.extract (Files.chunkSize - 3) (Files.chunkSize + 7)) "Cross-chunk seek"
  check ((← reads.atomically get).size == 2) "Seek downloaded unrelated chunks or entire file"
  check ((← reader.read (file.size + 1) 100).isEmpty) "Read beyond EOF"
  let expected := (text.splitOn "\n").foldl (fun n line => n + line.utf8ByteSize) 0
  let lines := ReducerCloud.readLines (pure store) #[file] (1024 * 1024)
  let cfg : ReducerCloud.Config := { maxBatchWeight := 2 * 1024 * 1024 }
  check ((← direct store (lines.map String.utf8ByteSize |>.sum cfg)) == expected) "Blob byte ranges lost or duplicated lines"
  let tiny ← Files.putText store "one\nβ\n\nlast\n"
  for size in [1, 3, 7, 64] do
    let lines := ReducerCloud.readLines (pure store) #[tiny] size
    check ((← direct store lines.toArray) == #["one", "β", "", "last", ""]) "Ordered UTF-8 line boundaries"
  let bad ← Files.putText store "1\ninvalid\n2\n"
  let parsed := (ReducerCloud.readLines (pure store) #[bad] 2 false).tryMap fun line =>
    match line.toNat? with | some n => .ok n | none => .error "invalid integer"
  rejects (direct store parsed.sum) "Invalid line was silently skipped"
  let reader ← Files.openReader store tiny
  reads.atomically (set (#[] : Array String))
  discard (reader.read 0 1)
  let some key := (← reads.atomically get)[0]? | throw (IO.userError "Missing chunk read")
  let corrupt := { store with read := fun k => if k == key then pure (some "bad".toUTF8) else store.read k }
  rejects (direct corrupt (ReducerCloud.readLines (pure corrupt) #[tiny]).toArray) "Corrupt range accepted"
  IO.println "PASS large blob seeks, authenticated chunks, distributed boundaries and parsing"

def main : IO Unit := do
  let reads ← Std.Mutex.new #[]
  let store := objects (← Std.Mutex.new {}) reads
  generated store
  replay store
  blobs store reads
