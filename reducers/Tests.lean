import LeanCloudReducers
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay
import LeanCloud.Scheduler

open Lean LeanCloud LeanCloudRuntime LeanReducers
deriving instance BEq for Except
private instance : Codec FileRef := jsonCodec _ "lean-cloud/file-ref/v1"

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
  putContent key bytes := data.atomically do
    unless (← get).contains key do modify (·.insert key bytes)
  size key := data.atomically do return (← get)[key]?.map (·.size)
  erase key := data.atomically (modify (·.erase key))
  list _ := pure #[]

private def environment (store : ObjectStore) (cpus workers : Nat) : ExecContext IO := {
  store.executionContext with
  currentWorker := { id := "executing", cpus }
  workers := (Array.range workers).map fun i => { id := s!"worker{i}", cpus } }

private def direct (store : ObjectStore) (program : Cloud IO α)
    (env : ExecContext IO := environment store 4 3) : IO α := do
  let value ← (DirectInterpreter.Internal.eval env program).run
  IO.ofExcept (value.mapError (·.message))

private def journal (state : Std.Mutex (List (String × ReplayRecord))) : ReplayStore IO where
  read key := state.atomically do return (← get).lookup key
  create key value := state.atomically do
    if let some old := (← get).lookup key then return old
    modify ((key, value) :: ·)
    return value

/-- Drive the actual scheduler and worker step with four concurrent workers.
Join every started IO task before a storage exception escapes; restarting this
driver discards scheduling callbacks but retains the caller's journal. -/
private def resume (step : Location → IO (Except CloudError Progress))
    (fuel : Nat) (location : Location) : IO Unit := do
  let mut state := Scheduler.Internal.advance { started := true, jobs := #[] } none
    (Scheduler.suspend (Scheduler.run #[location]))
  for _ in [:fuel] do
    let mut jobs : Array (String × Assignment) := #[]
    for i in [:4] do
      let worker := s!"worker{i}"
      let (next, deliveries) := Scheduler.handle 100 state (.ready worker)
      state := next
      for delivery in deliveries do
        match delivery.message with
        | .execute assignment => jobs := jobs.push (worker, assignment)
        | .failed error => throw (IO.userError error.message)
        | .idle | .finished => pure ()
        | _ => throw (IO.userError "Unexpected scheduler reply")
    if state.finished then return
    check (!jobs.isEmpty) "Scheduler stalled with unfinished callbacks"
    let reports ← mapTasks 4 jobs fun (worker, assignment) => do
      let progress ← step assignment.branchStart
      if let .ok (.fork _ count) := progress then
        check (count ≤ 2) "Reducer produced a flat fork instead of a binary tree"
      return (⟨worker, assignment.attempt, progress, #[]⟩ : Report)
    for report in reports.reverse do
      state := (Scheduler.handle 100 state (.report report)).1
  throw (IO.userError "Test driver fuel exhausted")

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
  let log ← Std.Mutex.new []
  let records := journal log
  let step location env := (ReplayInterpreter.step records env 10000 program () ⟨0, location⟩).run
  let .ok (.fork fork count) ← step Location.root (environment store 2 3)
    | throw (IO.userError "Expected a partition fork")
  check (count > 1) "Cloud reducer did not distribute work"
  discard <| mapTasks count (Array.range count) fun i =>
    resume (fun location => step location (environment store 4 9)) 100 (fork.child i)
  let .ok .done ← step Location.root (environment store 8 1)
    | throw (IO.userError "Join failed after environment change")
  let before ← calls.atomically get
  let .ok .done ← step Location.root (environment store 1 1)
    | throw (IO.userError "Completed replay failed")
  check ((← calls.atomically get) == before && before == 9) "Replay repeated recorded inputs"
  let .ok (some outcome) ← records.outcome.run | throw (IO.userError "No result")
  let actual := Id.run ((ReplayInterpreter.result (m := Id) (α := Array (Nat × Nat)) outcome).run)
  check (actual == .ok ((Array.range 9).map (fun n => (n, 4)))) "Planning/executing environments confused"
  let failedCalls ← Std.Mutex.new (0 : Nat)
  let failing (_ : Unit) := (ReducerCloud.ofArrayIO #[1, 2, 3] fun _ (_ : Nat) => do
    failedCalls.atomically (modify (· + 1))
    throw (IO.userError "valid application failure") : ReducerCloudIO Nat).sum
  let log ← Std.Mutex.new []
  let run := (SequentialReplay.interpret (journal log) store.executionContext 10000 failing ()).run
  let first ← run
  let before ← failedCalls.atomically get
  let second ← run
  check (first == .error ⟨.application, "valid application failure"⟩ && second == first &&
    (← failedCalls.atomically get) == before) "IO exception was treated as a node crash"
  IO.println "PASS stable partitions, replacement CPU budgets, replay and recorded failures"

private def treeReduction (store : ObjectStore) : IO Unit := do
  let q : FoldSpec Nat (List Nat) := { unit := [], combine := (· ++ ·), step := (· :: ·) }
  -- Noncommutative aggregates in blobs: local accumulators need no codec.
  for size in [0, 1, 3, 8, 17] do
    let leaves ← Std.Mutex.new (0 : Nat)
    let merges ← Std.Mutex.new (0 : Nat)
    let combined ← Std.Mutex.new (#[] : Array (Nat × Nat))
    let source := ReducerCloud.ofArray (m := IO) (Array.range size)
    let program (_ : Unit) := source.foldWith q
      (fun _ values => do
        leaves.atomically (modify (· + 1))
        Files.putJson store values.toArray)
      (fun env left right => do
        check (env.currentWorker.cpus == 4) "Combiner did not receive the executing worker's environment"
        let left : Array Nat ← IO.ofExcept (Json.parse (← Files.readText store left) >>= fromJson?)
        let right : Array Nat ← IO.ofExcept (Json.parse (← Files.readText store right) >>= fromJson?)
        merges.atomically (modify (· + 1))
        combined.atomically (modify (·.push (left.size, right.size)))
        Files.putJson store (left ++ right))
      { maxBatchItems := 1, maxBatchWeight := 1 }
    let log ← Std.Mutex.new []
    let records := journal log
    -- Lose the acknowledgement of the first recorded combiner, after its blob
    -- output and journal result are durable. The restarted tree must reuse it.
    let armed ← Std.Mutex.new (decide (size > 1))
    let crashStore := { records with create := fun key value => do
      let stored ← records.create key value
      if value.request == ⟨"exec", (inferInstance : Codec FileRef).schema, toJson "combine partitions"⟩ then
        let crash ← armed.atomically do let old ← get; set false; return old
        if crash then throw (IO.userError "node stopped after recording combiner")
      return stored }
    let run records := resume (fun location =>
      (ReplayInterpreter.step records (environment store 4 3) 10000 program () ⟨0, location⟩).run) 100 Location.root
    if size > 1 then rejects (run crashStore) "Combiner crash injection did not fire"
    run records
    let .ok (some outcome) ← records.outcome.run | throw (IO.userError "Missing tree result")
    let result ← IO.ofExcept ((← (ReplayInterpreter.result outcome : ExceptT CloudError IO FileRef).run).mapError (·.message))
    let actual : Array Nat ← IO.ofExcept (Json.parse (← Files.readText store result) >>= fromJson?)
    check (actual == Array.range size) "Tree changed noncommutative source order"
    check ((← leaves.atomically get) == max 1 size) "Restart repeated a recorded leaf"
    check ((← merges.atomically get) == size - 1) "Restart repeated a recorded combiner"
    for (left, right) in ← combined.atomically get do
      check (left > 0 && right > 0 && right - left ≤ 1 && left ≤ right)
        "Reducer did not combine balanced adjacent subtrees"
    let before ← log.atomically get
    run records
    check ((← log.atomically get).length == before.length &&
      (← leaves.atomically get) == max 1 size && (← merges.atomically get) == size - 1)
      "Completed tree replay performed more work"
  -- Combiner exceptions are application results, not worker crashes.
  let calls ← Std.Mutex.new (0 : Nat)
  let failing (_ : Unit) := (ReducerCloud.ofArray (m := IO) #[1, 2, 3, 4]).foldWith q
    (fun _ xs => pure xs.toArray)
    (fun _ _ _ => do
      calls.atomically (modify (· + 1))
      throw (IO.userError "combiner failed") : LeanCloud.Environment IO → Array Nat → Array Nat → IO (Array Nat))
    { maxBatchItems := 1 }
  let log ← Std.Mutex.new []
  let run := (SequentialReplay.interpret (journal log) store.executionContext 10000 failing ()).run
  let first ← run
  let before ← calls.atomically get
  let second ← run
  check (before > 0 && first == .error ⟨.application, "combiner failed"⟩ &&
    second == first && (← calls.atomically get) == before) "Combiner failure was retried or lost"
  IO.println "PASS binary tree combines, ordered blob aggregates, local restart and combiner failures"

private def emptyAndFailingTrees (store : ObjectStore) : IO Unit := do
  let empty : ReducerCloudIO Nat := ReducerCloud.ofPartitions (#[] : Array Nat)
    fun _ _ => { run := fun _ _ => throw (IO.userError "Empty source was read") }
  check ((← direct store empty.sum) == 0) "Empty fold did not return its identity"
  let calls ← Std.Mutex.new (#[] : Array Nat)
  let program (_ : Unit) := (ReducerCloud.ofArrayIO (Array.range 7) fun _ n => do
    calls.atomically (modify (·.push n))
    if n == 1 then throw (IO.userError "first branch error")
    if n == 5 then throw (IO.userError "later branch error")
    return n).sum { maxBatchItems := 1, maxBatchWeight := 1 }
  let expected ← (DirectInterpreter.Internal.eval store.executionContext (program ())).run
  check (expected == .error ⟨.application, "first branch error"⟩) "Direct tree selected the wrong failure"
  calls.atomically (set (#[] : Array Nat))
  let log ← Std.Mutex.new []
  let records := journal log
  let step location := (ReplayInterpreter.step records store.executionContext 10000 program () ⟨0, location⟩).run
  resume step 100 Location.root
  let .ok (some outcome) ← records.outcome.run | throw (IO.userError "Missing failed tree result")
  let actual ← (ReplayInterpreter.result outcome : ExceptT CloudError IO Nat).run
  check (actual == expected) "Concurrent tree selected a different failure"
  let executed ← calls.atomically get
  check (executed.size == 7 && (Array.range 7).all executed.contains)
    "A failed subtree skipped or repeated sibling work"
  resume step 100 Location.root
  check ((← calls.atomically get) == executed) "Failed tree replay repeated leaf effects"
  IO.println "PASS empty source isolation and source-ordered failures across concurrent subtrees"

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
  treeReduction store
  emptyAndFailingTrees store
  blobs store reads
