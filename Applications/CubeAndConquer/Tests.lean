import CubeAndConquer
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay

open Lean LeanCloud CubeAndConquer

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (value : Except String α) : IO α := IO.ofExcept value

private def same [BEq α] : Except CloudError α → Except CloudError α → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def noBlobs : ExecContext IO where
  cancellation := .never
  progress := .ignore
  queues := .unsupported
  blobs := {
    putBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
    readBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
    resolveBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩ }

private def assignment (variables bits : Nat) : Array Bool :=
  (Array.range variables).map fun i => (bits / 2 ^ i) % 2 == 1

private def oracle (cnf : CNF) (cube : Cube := []) : Option (Array Bool) :=
  (List.range (2 ^ cnf.variables)).findSome? (fun bits =>
      let model := assignment cnf.variables bits
      if cnf.checkModel model && cube.all (literalHolds model) then some model else none)

private def splitCubes : Nat → Array Cube
  | 0 => #[[]]
  | n + 1 => (splitCubes n).flatMap fun cube => #[cube ++ [Int.ofNat (n+1)], cube ++ [-Int.ofNat (n+1)]]

private def formula (seed : Nat) : CNF := Id.run do
  let mut state := seed + 1
  let variables := 1 + seed % 4
  let mut clauses := #[]
  for _ in [:seed % 11] do
    let mut clause := #[]
    for _ in [:1 + seed % 3] do
      state := (state * 1664525 + 1013904223) % 4294967296
      let lit := Int.ofNat (1 + (state / 8) % variables)
      clause := clause.push (if state % 2 == 0 then lit else -lit)
    clauses := clauses.push clause
  return ⟨variables, clauses⟩

private def pigeonhole (pigeons holes : Nat) : CNF := Id.run do
  let lit p h := Int.ofNat (1 + p * holes + h)
  let mut clauses := #[]
  for p in [:pigeons] do
    clauses := clauses.push ((Array.range holes).map (lit p))
  for h in [:holes] do
    for p in [:pigeons] do
      for q in [p+1:pigeons] do
        clauses := clauses.push #[-lit p h, -lit q h]
  return ⟨pigeons * holes, clauses⟩

private def modelTests : IO Unit := do
  for invalid in ["", "1 0\np cnf 1 1", "p cnf 1 1\n2 0", "p cnf 1 1\n1", "p cnf 1 0\n0",
      "p cnf 1 1\np cnf 1 1\n1 0", "p cnf 1 2\n1 0"] do
    check (!(parseCNF invalid).isOk) s!"Accepted invalid DIMACS: {invalid}"
  let cnf ← get (parseCNF "c test\np cnf 2 2\n1\t-2\n0 2 0\n")
  check (cnf.clauses == #[#[1, -2], #[2]]) "Multiline DIMACS parsing failed"
  check (parseModel cnf "v 1 2 0\n").isOk "Rejected valid model"
  for invalid in ["v -1 -2 0", "v 1 -1 2 0", "v 3 0", "v 1 2", "v 1 2 0 1"] do
    check (!(parseModel cnf invalid).isOk) s!"Accepted invalid model: {invalid}"
  check (parseCubes 2 8 "a 1 0\na -1 2 0\na -1 -2 0").isOk "Rejected irregular complete cover"
  for invalid in ["", "a 1 0", "a 1 0\na 1 0", "a 0\na 1 0", "a 3 0", "a 1 -1 0", "a 1", "a 0 0"] do
    check (!(parseCubes 2 8 invalid).isOk) s!"Accepted invalid cube file: {invalid}"
  check (parseCubes 0 1 "a 0\n").isOk "Empty cube should cover zero variables"
  check (aggregate 0 #[] != .unsat) "No results must not imply UNSAT"
  for variables in [1:7] do
    let cubes := splitCubes variables
    discard <| get (validateCubes variables cubes)
    for bits in [:2 ^ variables] do
      let model := assignment variables bits
      check ((cubes.filter (fun cube => cube.all (literalHolds model))).size == 1) "Cover is not a partition"
    for index in [:cubes.size] do
      check (!(validateCubes variables (cubes.extract 0 index ++ cubes.extract (index + 1) cubes.size)).isOk)
        "Missing leaf was accepted"
  for seed in [:100] do
    let cnf := formula seed
    check ((← get (parseCNF cnf.dimacs)) == cnf) "DIMACS round trip changed a formula"
  IO.println "PASS parsers, witnesses and complete-cover properties"

private def fakeRef (value : String := "fixture") : FileRef :=
  let hash := String.ofList (List.replicate 64 'a')
  ⟨⟨"objects/" ++ hash, value.length, modelChecksum value.toUTF8⟩, 0, hash⟩

private def modelBackend (cnf : CNF) (calls : IO.Ref Nat) : Backend IO where
  cube request parent := do
    calls.modify (· + 1)
    let count := min request.splitDepth (min (request.depth - parent.length) (cnf.variables - parent.length))
    if count == 0 then return .leaf
    let children := (splitCubes count).map fun child => child.map fun literal =>
      let value := Int.ofNat (parent.length + literal.natAbs)
      if literal > 0 then value else -value
    return .split children
  conquer _ _ cubes := cubes.mapM fun cube => do
    calls.modify (· + 1)
    let answer := match oracle cnf cube with
      | some model => Answer.sat (fakeRef (toJson model).compress)
      | none => Answer.unsat (fakeRef "cnf") (fakeRef "proof") (fakeRef "verified")
    return { cube, answer, log := fakeRef "log" }
  verify _ _ results := do calls.modify (· + 1); return results
  finish request results := do
    calls.modify (· + 1)
    IO.ofExcept (validateCubes cnf.variables (results.map (·.cube)))
    check (results.all (fun result => result.cube.length ≤ request.depth)) "Exceeded total decision budget"
    let count := results.size
    return { outcome := aggregate count results, bundle := fakeRef (toJson results).compress
             totalCubes := count, solvedCubes := results.size }

private def memoryStore (saved : IO.Ref (List (String × ReplayRecord)))
    (crashAfter : Option Nat := none) (writes : IO.Ref Nat) : ReplayStore IO where
  read key := return (← saved.get).lookup key
  create key proposed := do
    let value ← saved.modifyGet fun records => match records.lookup key with
      | some existing => (existing, records)
      | none => (proposed, (key, proposed) :: records)
    let call ← writes.modifyGet fun n => (n, n + 1)
    if crashAfter == some call then throw (IO.userError "Injected stop after durable write")
    return value

private def replayTests : IO Unit := do
  for seed in [:40] do
    let request : CubeAndConquer.Request := {
      cnf := fakeRef "input", depth := seed % 6
      splitDepth := 1 + seed % 3, cubesPerJob := 1 + seed % 5 }
    let calls ← IO.mkRef 0
    let run := workflow (modelBackend (formula seed) calls)
    let expected ← (DirectInterpreter.interpret noBlobs run request).run
    let .ok report := expected | throw (IO.userError "Generated workflow failed")
    match oracle (formula seed), report.outcome with
    | some _, .sat _ | none, .unsat => pure ()
    | _, _ => throw (IO.userError "Generated workflow disagrees with exhaustive search")
    check (report.totalCubes == 2 ^ min request.depth (formula seed).variables) "Wrong depth-limited leaf count"
    let saved ← IO.mkRef []
    let writes ← IO.mkRef 0
    let store := memoryStore saved none writes
    let actual ← (SequentialReplay.interpret store noBlobs 10000 run request).run
    check (same expected actual) s!"Direct/replay mismatch, seed {seed}"
    let before ← calls.get
    let again ← (SequentialReplay.interpret store noBlobs 10000 run request).run
    check (same again actual && (← calls.get) == before) "Completed replay reran a tool"
  -- Stop after every durable write in a nested all-UNSAT workflow. Recovery
  -- uses the same saved journal, but no local execution state or tool workspace.
  let request : CubeAndConquer.Request := { cnf := fakeRef "input", depth := 3, splitDepth := 1 }
  let calls ← IO.mkRef 0
  let run := workflow (modelBackend ⟨3, #[#[1], #[-1]]⟩ calls)
  let expected ← (DirectInterpreter.interpret noBlobs run request).run
  let baseline ← IO.mkRef []
  let count ← IO.mkRef 0
  discard <| (SequentialReplay.interpret (memoryStore baseline none count) noBlobs 10000 run request).run
  for stop in [:← count.get] do
    let saved ← IO.mkRef []
    let writes ← IO.mkRef 0
    let store := memoryStore saved (some stop) writes
    try
      discard <| (SequentialReplay.interpret store noBlobs 10000 run request).run
      throw (IO.userError "Fault injection did not stop execution")
    catch error => check (error.toString == "Injected stop after durable write") "Unexpected recovery exception"
    let recovered ← (SequentialReplay.interpret store noBlobs 10000 run request).run
    check (same recovered expected) s!"Recovery mismatch after write {stop}"
  IO.println "PASS 40 differential programs, cached replay and every-write recovery"

private def exceptionTests : IO Unit := do
  let calls ← IO.mkRef 0
  let checks ← IO.mkRef 0
  let reliable := modelBackend ⟨1, #[#[1], #[-1]]⟩ calls
  let failing := { reliable with
    verify := fun env request result => do
      let attempt ← checks.modifyGet fun n => (n, n + 1)
      if attempt == 0 then throw (IO.userError "Checker IO failed")
      reliable.verify env request result }
  let journal ← IO.mkRef []
  let writes ← IO.mkRef 0
  let request : CubeAndConquer.Request := { cnf := fakeRef "input", depth := 0 }
  let replay := SequentialReplay.interpret (memoryStore journal none writes) noBlobs 10000
    (workflow failing) request
  -- This checker would succeed on a second invocation. Its first exception
  -- is a durable execution failure, so replay must never make that invocation.
  for _ in [:2] do
    let .error error ← replay.run | throw (IO.userError "Checker exception did not fail the workflow")
    check (error == ⟨.application, "Checker IO failed"⟩) "Wrong checker execution failure"
  check ((← checks.get) == 1 && (← calls.get) == 1)
    "Replay retried the checker or repeated the solver"
  IO.println "PASS checker IO exceptions are recorded failures, never worker crashes"

private def depthTests : IO Unit := do
  let request : CubeAndConquer.Request := { cnf := fakeRef "input", depth := 3, splitDepth := 2 }
  for invalid in [{ request with splitDepth := 0 }, { request with splitDepth := 9 },
      { request with depth := 65 }, { request with maxCubes := 7 },
      { request with cubesPerJob := 0 }, { request with cubesPerJob := 257 }] do
    check (!invalid.validate.isOk) "Accepted invalid depth/split/leaf budget"
  check ({ request with depth := 0, maxCubes := 1 }.validate.isOk) "Rejected depth zero"
  check (validateSplit [1] 2 #[[2], [-2, 3], [-2, -3]]).isOk "Rejected uneven split"
  for invalid in [#[], #[[]], #[[2]], #[[1], [-1]], #[[2, 3], [-2, 3]],
      #[[2, 3, 4], [2, 3, -4], [2, -3], [-2]]] do
    check (!(validateSplit [1] 2 invalid).isOk) "Accepted malformed or over-depth split"
  let calls ← IO.mkRef 0
  let leaves ← IO.mkRef (#[] : Array Cube)
  let basic := modelBackend ⟨5, #[#[1], #[-1]]⟩ calls
  let uneven := { basic with
    cube := fun request parent => do
      let v := Int.ofNat (parent.length + 1)
      if request.depth - parent.length ≥ 2 then
        return .split #[[v], [-v, v + 1], [-v, -(v + 1)]]
      else return .split #[[v], [-v]]
    conquer := fun env request cubes => do
      leaves.modify (· ++ cubes)
      basic.conquer env request cubes }
  let .ok report ← (DirectInterpreter.interpret noBlobs (workflow uneven) request).run
    | throw (IO.userError "Uneven recursive split failed")
  check (report.outcome == .unsat && report.totalCubes == 8 &&
    (← leaves.get).all (fun cube => cube.length == 3)) "Did not consume actual child depths"
  -- Stalled cubing, early SAT, and timeouts terminate the current subtree.
  let stalled := { basic with cube := fun _ _ => pure .leaf }
  let .ok report ← (DirectInterpreter.interpret noBlobs (workflow stalled) request).run
    | throw (IO.userError "Stalled cuber failed")
  check (report.totalCubes == 1 && report.outcome == .unsat) "Stalled cuber did not conquer its parent"
  for answer in [Answer.sat (fakeRef "model"), .unknown "timeout", .error "malformed output"] do
    let early := { basic with cube := fun _ parent => do
      return .finished { cube := parent, answer, log := fakeRef "log" } }
    let .ok report ← (DirectInterpreter.interpret noBlobs (workflow early) request).run
      | throw (IO.userError "Early cuber outcome failed")
    let expected := match answer with | .sat model => Conclusion.sat model | _ => .inconclusive
    check (report.totalCubes == 1 && report.outcome == expected) "Wrong early cuber outcome"
  for result in [Cubing.split #[[1]], .split #[[]],
      .finished { cube := [1], answer := .unknown "wrong cube", log := fakeRef "log" }] do
    let invalid := { basic with cube := fun _ _ => pure result }
    let actual ← (DirectInterpreter.interpret noBlobs (workflow invalid) request).run
    check (!actual.isOk) "Workflow accepted malformed cubing output"
  IO.println "PASS total/split depth, leaf limits, uneven recursion and stalled/terminal cubing"

private def batchWorkflowTests : IO Unit := do
  let cubes := splitCubes 4
  for size in [1:20] do
    let groups := batches cubes size
    check (groups.flatten == cubes && groups.all (fun group => !group.isEmpty && group.size ≤ size))
      "Batching lost, reordered or exceeded its cube budget"
  let calls ← IO.mkRef 0
  let sizes ← IO.mkRef (#[] : Array Nat)
  let reliable := modelBackend ⟨4, #[#[1], #[-1]]⟩ calls
  let grouped := { reliable with conquer := fun env request cubes => do
    check (env.currentWorker.cpus == 3) "Worker CPU budget was not passed to the batch"
    sizes.modify (·.push cubes.size)
    reliable.conquer env request cubes }
  let context := { noBlobs with currentWorker := { id := "batch-worker", cpus := 3 } }
  let request : CubeAndConquer.Request := {
    cnf := fakeRef "input", depth := 4, splitDepth := 2, cubesPerJob := 3 }
  let .ok report ← (DirectInterpreter.interpret context (workflow grouped) request).run
    | throw (IO.userError "Batched workflow failed")
  check (report.totalCubes == 16 && (← sizes.get) == #[3, 1, 3, 1, 3, 1, 3, 1])
    "Expected eight cloud solver batches for sixteen leaves"
  for invalid in [
      { reliable with conquer := fun _ _ _ => pure #[] },
      { reliable with verify := fun _ _ _ => pure #[] }] do
    let result ← (DirectInterpreter.interpret noBlobs (workflow invalid) request).run
    check (!result.isOk) "Missing batch results were accepted"
  IO.println "PASS bounded cloud batches, worker environment and batch result identity"

private def processTests : IO Unit := IO.FS.withTempDir fun directory => do
  let output := directory / "stdout"
  let errors := directory / "stderr"
  let before ← IO.monoMsNow
  let out ← CubeAndConquer.Process.runFiles { cmd := "/bin/sh", args := #["-c", "sleep 10 & wait"] }
    50 output errors 1024
  check (out.stopped && (← IO.monoMsNow) - before < 3000) "Deadline did not terminate the process group"
  let noisy ← CubeAndConquer.Process.runFiles {
    cmd := "/bin/sh", args := #["-c", "while :; do printf '0123456789'; done"] } 3000 output errors 100
  check (noisy.stopped && (← output.metadata).byteSize ≤ 100) "Output file limit failed"
  let artifact := directory / "proof"
  let oversized ← CubeAndConquer.Process.runFiles {
    cmd := "/bin/sh", args := #["-c", "while :; do printf '0123456789' >> proof; done"]
    cwd := some directory } 3000 output errors 100 #[(artifact, 100)]
  check oversized.stopped "Proof artifact size was not monitored"
  IO.println "PASS streamed subprocess output, file limits and process-group termination"

private initialize objectsLock : Std.Mutex Unit ← Std.Mutex.new ()

private def memoryObjects (saved : IO.Ref (Std.HashMap String ByteArray)) : LeanCloudRuntime.ObjectStore where
  ensureContainer := pure ()
  read key := objectsLock.atomically do return (← saved.get)[key]?
  create key bytes := objectsLock.atomically do saved.modifyGet fun records =>
    match records[key]? with
    | some existing => (existing, records)
    | none => (bytes, records.insert key bytes)
  list _ := return #[]
  erase key := objectsLock.atomically do saved.modify (·.erase key)

private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try discard action; pure false catch _ => pure true
  check failed message

private def fileTests : IO Unit := IO.FS.withTempDir fun directory => do
  let saved ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let store := memoryObjects saved
  let source := directory / "large.bin"
  let dest := directory / "download.bin"
  let handle ← IO.FS.Handle.mk source .write
  for index in [:10] do handle.write (ByteArray.mk (Array.replicate 1048576 index.toUInt8))
  handle.flush
  let ref ← Files.upload store source (16 * 1048576)
  let count := (← saved.get).size
  check (ref.size == 10 * 1048576 && count == 4) "Expected three chunks and a manifest"
  Files.download store ref dest ref.size
  check ((← Files.digest dest) == ref.sha256) "Large artifact round trip failed"
  check ((← Files.upload store source ref.size) == ref && (← saved.get).size == count) "Retry did not reuse artifacts"
  rejects (Files.download store { ref with size := ref.size + 1 } dest (ref.size+1)) "Accepted forged file length"
  rejects (Files.download store { ref with sha256 := "bad" } dest ref.size) "Accepted forged file digest"
  rejects (Files.upload store source 100) "Ignored upload limit"
  let before ← saved.get
  let some record := before.toArray.find? (fun (key, _) => key != ref.manifest.key)
    | throw (IO.userError "Missing chunk")
  saved.modify (·.insert record.1 "corrupt".toUTF8)
  rejects (Files.download store ref dest ref.size) "Accepted corrupt blob chunk"
  saved.set before
  saved.modify (·.erase record.1)
  rejects (Files.download store ref dest ref.size) "Accepted missing blob chunk"
  saved.set before
  -- No complete file reference is produced if publication fails midway.
  let attempts ← IO.mkRef 0
  let interrupted := { store with create := fun key bytes => do
    let n ← attempts.modifyGet fun n => (n, n+1)
    if n == 1 then throw (IO.userError "Upload interrupted")
    store.create key bytes }
  rejects (Files.upload interrupted source ref.size) "Upload fault did not fire"
  check ((← Files.upload store source ref.size) == ref) "Interrupted upload changed artifact identity"
  IO.println "PASS 10 MiB chunked files, retry, limits, corruption and missing artifacts"

private def inputCacheTests : IO Unit := IO.FS.withTempDir fun directory => do
  let saved ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let store := memoryObjects saved
  let ref ← Files.putText store "p cnf 2 1\n1 2 0\n"
  let reads ← IO.mkRef 0
  let counted := { store with read := fun key => do
    reads.modify (· + 1)
    store.read key }
  let use (ref : FileRef) (limit : Nat) := Input.withFile counted (some directory) ref limit 2 fun path => do
    check ((← Files.digest path) == ref.sha256) "Invalid cached input"
    discard <| Dimacs.scan path
  use ref 1024
  let before ← reads.get
  use ref 1024
  check ((← reads.get) == before) "Cached CNF was downloaded twice"
  rejects (use ref 1) "Cache hit bypassed the input byte limit"
  -- A corrupt hit and an interrupted fill must both be recoverable.
  IO.FS.writeFile (directory / "original.cnf") "corrupt"
  use ref 1024
  check ((← reads.get) > before) "Corrupt input was not downloaded again"
  let other ← Files.putText store "p cnf 1 1\n-1 0\n"
  let broken := { counted with read := fun _ => throw (IO.userError "Interrupted download") }
  rejects (Input.withFile broken (some directory) other 1024 2 fun _ => pure ())
    "Cache download interruption did not fire"
  check (!(← (directory / "original.cnf").pathExists) && !(← (directory / "original.pending").pathExists))
    "Interrupted cache entry was published"
  use other 1024
  check ((← directory.readDir).size == 1) "CNF cache accumulated old inputs"
  IO.println "PASS shared CNF cache reuse, limits, corruption, interrupted fills and eviction"

/-- Exercise the actual batch backend with rendezvousing subprocess fixtures.
No certificate claims depend on these fixtures; real tools are tested below. -/
private def poolTests : IO Unit := do
  let script ← IO.FS.readFile "tests/pool-tool.sh"
  for cpus in [0, 1, 2] do
    IO.FS.withTempDir fun directory => do
      let saved ← IO.mkRef ({} : Std.HashMap String ByteArray)
      let store := memoryObjects saved
      let request : CubeAndConquer.Request := {
        cnf := ← Files.putText store "p cnf 2 2\n1 0\n-1 0\n", seconds := 5, verifySeconds := 5 }
      for tool in ["kissat", "drat-trim"] do
        let path := directory / tool
        IO.FS.writeFile path script
        let out ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
        check (out.exitCode == 0) "Cannot prepare test tool"
      IO.FS.writeFile (directory / "width") (toString (max 1 cpus))
      let tools : Tools := { directory, identity := { binaries := "test fixture" }, cache := some (directory / "cache") }
      let env : Environment IO := { store.executionContext.map MonadCloudExec.restore with
        currentWorker := { cpus } }
      let cubes := splitCubes 2
      let solved ← tools.conquerBatch store env request cubes
      check (solved.map (·.cube) == cubes && solved.all (fun result =>
        match result.answer with | .unverified .. => true | _ => false)) "Local solver pool failed"
      let checked ← tools.verifyBatch store env request solved
      check (checked.map (·.cube) == cubes && checked.all (fun result =>
        match result.answer with | .unsat .. => true | _ => false)) "Local checker pool failed"
      for tool in ["kissat", "drat-trim"] do
        let changes := words (← IO.FS.readFile (directory / s!"{tool}.events"))
        let mut active : Int := 0
        let mut peak : Int := 0
        for change in changes do
          let some delta := change.toInt? | throw (IO.userError "Invalid pool event")
          active := active + delta
          peak := max peak active
          check (0 ≤ active && active ≤ Int.ofNat (max 1 cpus)) "Tool pool exceeded its CPU budget"
        check (active == 0 && peak == Int.ofNat (max 1 cpus) && changes.size == 8)
          "Pool did not run all cubes, overlap processes or join every child"
  IO.println "PASS actual solver/checker pools overlap work and respect 0/1/2 CPU budgets"

private def realTools : IO Unit := IO.FS.withTempDir fun cache => do
  let tools := { (← Tools.fromEnvironment) with cache := some cache }
  let saved ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let store := memoryObjects saved
  for seed in [:15] do
    let cnf := formula seed
    let input ← Files.putText store cnf.dimacs
    let request : CubeAndConquer.Request := { cnf := input, seconds := 20, verifySeconds := 20 }
    let solved ← tools.conquer store request []
    let result ← tools.verify store request solved
    match oracle cnf, result.answer with
    | some _, .sat model =>
      check ((← get (parseModel cnf (← Files.readText store model))).size == cnf.variables) "Bad model"
    | none, .unsat _ _ _ => pure ()
    | _, actual => throw (IO.userError s!"Kissat/oracle mismatch: {repr actual}")
  let cnf := pigeonhole 7 6
  let request : CubeAndConquer.Request := {
    cnf := ← Files.putText store cnf.dimacs, depth := 3, splitDepth := 1, seconds := 20, verifySeconds := 20 }
  let .split children ← tools.cube store request [] | throw (IO.userError "Expected march cubes")
  check (children.size == 2) "Real cuber did not split at depth 1"
  for parent in children do
    let .split grandchildren ← tools.cube store request parent | throw (IO.userError "Expected parallel recubing")
    discard <| get (validateSplit parent 1 grandchildren)
  let count := 2 ^ request.depth
  let context := { noBlobs with currentWorker := { cpus := 2 } }
  let report ← (DirectInterpreter.interpret context (workflow (backend tools store)) request).run
  let .ok report := report | throw (IO.userError "Workflow failed")
  check (report.outcome == .unsat && report.totalCubes == count) "Split/conquer failed"
  check ((← tools.verifyBundle store report.bundle) == .unsat) "Independent bundle recheck failed"
  let bundle : Bundle ← Files.readJson store report.bundle
  let some first := bundle.results[0]? | throw (IO.userError "No certificates")
  let .unsat formula proof verification := first.answer | throw (IO.userError "No proof")
  check (proof.size > 0) "Expected nontrivial proof"
  let corrupted := { first with answer := .unsat formula (← Files.putText store "") verification }
  let bad ← Files.putJson store { bundle with results := bundle.results.set! 0 corrupted }
  rejects (tools.verifyBundle store bad) "Accepted missing proof steps"
  let corrupted := { first with answer := .unsat request.cnf proof verification }
  let bad ← Files.putJson store { bundle with results := bundle.results.set! 0 corrupted }
  rejects (tools.verifyBundle store bad) "Accepted proof for a different cube CNF"
  let missing ← Files.putJson store { bundle with results := bundle.results.pop }
  check ((← tools.verifyBundle store missing) == .inconclusive) "Missing cube established UNSAT"
  let duplicate ← Files.putJson store { bundle with results := bundle.results.push first }
  rejects (tools.verifyBundle store duplicate) "Accepted duplicate cube result"
  for text in ["p cnf 2 1\n1 2 0\n", "p cnf 1 2\n1 0\n-1 0\n", "p cnf 0 0\n", "p cnf 0 1\n0\n", "p cnf 3 0\n"] do
    let cnf ← get (parseCNF text)
    let request : CubeAndConquer.Request := { cnf := ← Files.putText store text }
    let .ok report ← (DirectInterpreter.interpret noBlobs (workflow (backend tools store)) request).run
      | throw (IO.userError "Early cuber failure")
    match oracle cnf, report.outcome with
    | some _, .sat _ | none, .unsat => pure ()
    | _, _ => throw (IO.userError s!"Wrong early cuber result for {text}: {repr report.outcome}; {← Files.readText store report.bundle}")
    check ((← tools.verifyBundle store report.bundle) == report.outcome) "Early bundle recheck failed"
  let directRequest := { request with depth := 0 }
  let directBackend := { backend tools store with cube := fun _ _ => throw (IO.userError "Depth zero invoked march") }
  let .ok direct ← (DirectInterpreter.interpret noBlobs (workflow directBackend) directRequest).run
    | throw (IO.userError "Depth-zero solving failed")
  check (direct.outcome == .unsat && direct.totalCubes == 1) "Depth-zero result was not one verified leaf"
  check ((← tools.verifyBundle store direct.bundle) == .unsat) "Depth-zero bundle recheck failed"
  -- Crash outside user IO, immediately before/after the checker result's
  -- journal commit. A committed result replays; an uncommitted one runs again.
  let request : CubeAndConquer.Request := {
    cnf := ← Files.putText store cnf.dimacs, depth := 2, splitDepth := 2, cubesPerJob := 4 }
  for afterCommit in [false, true] do
    let solves ← IO.mkRef 0
    let checks ← IO.mkRef 0
    let reliable := { backend tools store with cube := fun _ _ => pure (.split (splitCubes 2)) }
    let counted := { reliable with
      conquer := fun env request cube => do
        solves.modify (· + 1)
        reliable.conquer env request cube
      verify := fun env request result => do
        checks.modify (· + 1)
        reliable.verify env request result }
    let journal ← IO.mkRef []
    let writes ← IO.mkRef 0
    let pending ← IO.mkRef true
    let base := memoryStore journal none writes
    let interrupted : ReplayStore IO := { base with
      create := fun key record => do
        if record.request.kind == "exec" && record.request.payload.getStr?.toOption == some "verify" then
          if ← pending.modifyGet (fun was => (was, false)) then
            if afterCommit then discard (base.create key record)
            throw (IO.userError "Worker stopped at checker journal commit")
        base.create key record }
    let replay := SequentialReplay.interpret interrupted context 10000 (workflow counted) request
    try
      discard replay.run
      throw (IO.userError "Worker crash did not fire")
    catch error =>
      check (error.toString == "Worker stopped at checker journal commit") "Unexpected recovery exception"
    check (!(← pending.get) && (← solves.get) == 1 && (← checks.get) == 1) "Missed the checker commit"
    for _ in [:2] do
      let .ok recovered ← replay.run | throw (IO.userError "Checker recovery failed")
      check (recovered.outcome == .unsat && recovered.totalCubes == 4 && (← solves.get) == 1 &&
        (← checks.get) == (if afterCommit then 1 else 2))
        "Recovery repeated a committed action or lost an uncommitted check"
    for (_, record) in ← journal.get do
      check (((toJson record).compress.splitOn "p cnf").length == 1) "CNF contents entered replay journal"
  IO.println "PASS worker crashes before/after checker commit reuse the solver certificate"
  IO.println s!"PASS real solver/checker, {count}-cube UNSAT bundle, independent recheck and forged evidence rejection"

def main (args : List String) : IO UInt32 := do
  try
    modelTests
    depthTests
    batchWorkflowTests
    replayTests
    exceptionTests
    processTests
    fileTests
    inputCacheTests
    poolTests
    if args == ["--tools"] then realTools
    else unless args.isEmpty do throw (IO.userError "Usage: sat_tests [--tools]")
    return 0
  catch error => IO.eprintln s!"FAIL {error}"; return 1
