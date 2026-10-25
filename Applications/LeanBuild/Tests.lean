import LeanBuild
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay

open Lean LeanCloud LeanCloudRuntime LeanBuild

private def check (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def noBlobs : ExecContext IO where
  blobs := {
    putBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
    readBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
    resolveBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩ }

private def journal (ref : IO.Ref (List (String × ReplayRecord))) : ReplayStore IO where
  read key := return (← ref.get).lookup key
  create key value := ref.modifyGet fun saved =>
    match saved.lookup key with
    | some old => (old, saved)
    | none => (value, (key, value) :: saved)

private def objects (ref : IO.Ref (Std.HashMap String ByteArray)) : ObjectStore where
  ensureContainer := pure ()
  read key := return (← ref.get)[key]?
  create key bytes := ref.modifyGet fun saved => match saved[key]? with
    | some old => (old, saved)
    | none => (bytes, saved.insert key bytes)
  erase key := ref.modify (·.erase key)
  list _ := return #[]

private def request : LeanBuild.Request := {
  repository := "https://github.com/palladin/lean-cloud"
  revision := "main", targets := #["+Fixture.Final"] }

private def fixturePlan : Plan := {
  commit := "fixture", toolchain := "fixture", platform := "fixture", source := default
  modules := #[⟨"Base", #[]⟩, ⟨"Final", #["Base"]⟩] }

private def stub : Backend IO := {
  prepare := fun _ _ => pure { plan := some fixturePlan }
  build := fun _ _ _ group _ => pure (group.map fun m => { name := m.name, status := .built })
  finish := fun _ _ _ _ => pure { name := "targets", status := .built }
  check := fun _ r _ _ => pure { mode := r.check.mode, success := true } }

private def pool (cpus : Array Nat) : ExecContext IO :=
  let workers := cpus.mapIdx fun i n => { id := s!"worker{i}", cpus := n : WorkerCapacity }
  { noBlobs with workers, currentWorker := workers[0]?.getD {} }

/-- Resume with a supplied execution environment, including after a restart. -/
private def replayAt (store : ReplayStore IO) (source : Cloud IO LeanBuild.Report)
    (environment : ExecContext IO) : Nat → Assignment → ExceptT CloudError IO Unit
  | 0, _ => throw ⟨.protocol, "Test fuel exhausted"⟩
  | fuel + 1, assignment => do
      let progress ← ReplayInterpreter.step store environment (fuel + 1) (fun _ : Unit => source) () assignment
      SequentialReplay.follow (replayAt store source environment fuel) assignment.branchStart progress

private def replayReport (store : ReplayStore IO) (source : Cloud IO LeanBuild.Report)
    (environment : ExecContext IO) : ExceptT CloudError IO LeanBuild.Report := do
  replayAt store source environment 10000 ⟨0, Location.root⟩
  let some outcome ← store.outcome | throw ⟨.protocol, "Missing test outcome"⟩
  ReplayInterpreter.result outcome

/-- Independent unit-cost list scheduler for comparing planned compute time.
Imports outside this job are already committed. Transfers are not modeled. -/
private def modelTicks (modules : Array LeanBuild.Module) (cpus : Nat) : Nat := Id.run do
  let members := modules.foldl (fun set m => set.insert m.name) ({} : Std.HashSet String)
  let mut done : Std.HashSet String := {}
  let mut pending := modules
  let mut ticks := 0
  for _ in [:modules.size] do
    if pending.isEmpty then break
    let ready := (pending.filter fun m => m.imports.all fun dep =>
      !members.contains dep || done.contains dep).extract 0 (max 1 cpus)
    for m in ready do done := done.insert m.name
    pending := pending.filter (!done.contains ·.name)
    ticks := ticks + 1
  return ticks

private structure PlanStats where
  rounds : Nat := 0
  jobs : Nat := 0
  ticks : Nat := 0
  deriving BEq, Repr

private def checkPartition (modules : Array LeanBuild.Module) (environment : ExecContext IO)
    (limit : Nat := 0) : IO PlanStats := do
  let mut pending := modules
  let mut done : Array BuildResult := #[]
  let mut stats : PlanStats := {}
  let cpus := environment.workers.map (max 1 ·.cpus)
  let ordered := criticalOrder modules
  for _ in [:modules.size] do
    if pending.isEmpty then break
    let groups := partition pending done cpus limit
    check (groups.any (!·.isEmpty) && groups.size == cpus.size) "No progress or mismatched CPU slots"
    for group in groups do
      check (limit == 0 || group.size ≤ limit) "Job exceeds explicit cap"
      let mut available := done.foldl (fun set r => set.insert r.name) ({} : Std.HashSet String)
      for m in group do
        check (m.imports.all available.contains) "Cross-job dependency inside a round"
        available := available.insert m.name
    let names := groups.flatten.map (·.name)
    let selected := names.foldl (fun set name => set.insert name) ({} : Std.HashSet String)
    check (selected.size == names.size) "Duplicate module ownership"
    let times := groups.mapIdx fun i group =>
      let members := group.foldl (fun set m => set.insert m.name) ({} : Std.HashSet String)
      modelTicks (ordered.filter fun m => members.contains m.name) cpus[i]!
    stats := {
      rounds := stats.rounds + 1
      jobs := stats.jobs + (groups.filter (!·.isEmpty)).size
      ticks := stats.ticks + times.foldl max 0 }
    done := done ++ names.map fun name => { name, status := .built }
    pending := pending.filter fun m => !selected.contains m.name
  check (pending.isEmpty && done.size == modules.size) "Incomplete DAG coverage"
  return stats

private def partitionTests : IO Unit := do
  let wide := (Array.range 1024).map fun i => { name := s!"M{i}", imports := #[] : LeanBuild.Module }
  check ((← checkPartition wide (pool #[8, 8, 8, 8])) == ⟨1, 4, 32⟩) "Independent modules lost CPUs or gained barriers"
  check ((← checkPartition wide (pool #[8, 8, 8, 8]) 64) == ⟨4, 16, 32⟩) "Explicit job cap ignored"
  let shared := #[⟨"Base", #[]⟩] ++ wide.map fun m => { m with imports := #["Base"] }
  check ((partition shared #[] #[8, 8, 8, 8] 0).flatten.map (·.name) == #["Base"])
    "Shared prerequisite trapped parallel work on its worker"
  check ((← checkPartition shared (pool #[8, 8, 8, 8])) == ⟨2, 5, 33⟩)
    "Wide fan-out did not use all CPUs after publishing the shared prerequisite"
  let chains := (Array.range 4).flatMap fun c => (Array.range 256).map fun i => {
    name := s!"C{c}_{i}", imports := if i == 0 then #[] else #[s!"C{c}_{i - 1}"] : LeanBuild.Module }
  check ((← checkPartition chains (pool #[8, 8, 8, 8])) == ⟨1, 4, 256⟩) "Dependency chains fragmented"
  check ((partition (wide.extract 0 10) #[] #[1, 4] 0).map (·.size) == #[2, 8]) "CPU weighting ignored"
  check ((partition (wide.extract 0 2) #[] #[1, 16] 0).map (·.size) == #[1, 1]) "Small frontier lost parallelism"
  let fork : Array LeanBuild.Module := #[⟨"A", #[]⟩, ⟨"B", #["A"]⟩, ⟨"C", #["A"]⟩]
  check ((partition fork #[] #[4, 4] 0).flatten.map (·.name) == #["A", "B", "C"])
    "Small fan-out introduced an unnecessary cloud barrier"
  let diamond : Array LeanBuild.Module := #[⟨"A", #[]⟩, ⟨"B", #[]⟩, ⟨"C", #["A", "B"]⟩, ⟨"D", #["C"]⟩]
  check ((← checkPartition diamond (pool #[4, 4])) == ⟨1, 1, 3⟩) "Shared consumers were split despite free local CPUs"
  check ((← checkPartition diamond (pool #[1, 1]) 1) == ⟨3, 4, 3⟩) "Capped join crossed job dependencies"
  let joined : Array LeanBuild.Module := #[⟨"T0", #[]⟩, ⟨"T1", #["T0"]⟩, ⟨"T2", #["T1"]⟩,
    ⟨"A", #[]⟩, ⟨"B", #[]⟩, ⟨"C", #[]⟩, ⟨"D", #[]⟩, ⟨"Join", #["A", "B", "C", "D"]⟩]
  check ((← checkPartition joined (pool #[2, 2])) == ⟨1, 2, 3⟩)
    "A removable join barrier survived despite unchanged compute time"
  let smallJoin := diamond.extract 0 3
  check ((partition smallJoin #[] #[1, 4] 0).map (·.size) == #[0, 3])
    "Repacked component lost the faster worker's CPU slot"
  check ((← checkPartition smallJoin (pool #[1, 4])) == ⟨1, 1, 2⟩) "Repacking increased the join's compute span"
  let priority : Array LeanBuild.Module := #[⟨"short", #[]⟩, ⟨"base", #[]⟩,
    ⟨"middle", #["base"]⟩, ⟨"tip", #["middle"]⟩]
  check ((partition priority #[] #[1] 1).flatten.map (·.name) == #["base"])
    "Short independent work displaced the critical path"
  let mixed := shared ++ chains
  let result ← checkPartition mixed (pool #[8, 8, 8, 8])
  check (result.ticks < 290) "Independent chains prevented useful work during the wide fan-out"
  let emptyPool : Array Nat := #[]
  check ((partition wide #[] emptyPool 5).map (·.size) == #[5]) "Empty pool/zero CPU fallback"
  for seed in [:100] do
    let modules := (Array.range 80).map fun i => {
      name := s!"G{i}", imports := ((Array.range i).filter fun j =>
        (i * 31 + j * 17 + seed) % 19 == 0).map (s!"G{·}") : LeanBuild.Module }
    discard <| checkPartition modules (pool #[1 + seed % 7, 1, 4]) (if seed % 2 == 0 then 0 else 7)
  IO.println "PASS DAG planning: critical paths, local joins, barrier merging, CPU weighting, caps and progress"

private def generatedTests : IO Unit := do
  check (progressLabel 200 9031 == "200/9,031 · 2%") "Wrong short progress label"
  check (progressLabel 9031 9031 == "9,031/9,031 · 100%") "Wrong completed progress label"
  let saved ← IO.mkRef ([] : List (String × ReplayRecord))
  let labels ← IO.mkRef (#[] : Array String)
  let observer : ReplayInterpreter.Observer IO := fun _ _ label =>
    if let some label := label then labels.modify (·.push label) else pure ()
  let step (location : Location) := (ReplayInterpreter.step (journal saved) noBlobs 1000
    (workflow stub) { request with modulesPerJob := 1 } ⟨0, location⟩ (some observer)).run
  for expected in ["0/2 · 0%", "1/2 · 50%"] do
    let .ok (.fork location 1) ← step Location.root | throw (IO.userError "Expected one-module round")
    check ((← labels.get).back? == some expected) "Round label is not the completed-module count"
    let .ok .done ← step (location.child 0) | throw (IO.userError "Child did not complete")
  let .ok .done ← step Location.root | throw (IO.userError "Labeled workflow did not finish")
  partitionTests
  for version in ["4.35.0", "4.35.1", "4.36.0", "5.0.0"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption == some version) "Supported release rejected"
  for version in ["3.99.0", "4.34.99", "4.35", "04.35.0", "4.35.0-rc1", "nightly"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption.isNone) "Unsupported release accepted"
  let minimal : LeanBuild.Request ← IO.ofExcept (fromJson? (Json.mkObj [
    ("repository", toJson request.repository), ("revision", toJson "main")]))
  check (minimal.targets.isEmpty && minimal.check.mode == .none && minimal.cache == .rebuild &&
    minimal.options.isEmpty && minimal.subdirectory == "." && minimal.modulesPerJob == 0) "Wrong request defaults"
  let encoded ← IO.ofExcept (Json.parse "{\"repository\":\"https://github.com/a/b\",\"revision\":\"main\",\"options\":{\"greeting\":\"42\"},\"check\":{\"mode\":\"kernel\"}}")
  let decoded : LeanBuild.Request ← IO.ofExcept (fromJson? encoded)
  check (decoded.options["greeting"]? == some "42" && decoded.check.mode == .kernel) "JSON options/check mode"
  for seed in [:80] do
    let modules := (Array.range (4 + seed % 12)).map fun i => {
      name := s!"M{i}"
      imports := ((Array.range i).filter fun j => (i * 37 + j * 7 + seed) % 3 == 0).map (s!"M{·}") : LeanBuild.Module }
    IO.ofExcept (validateModules modules)
    let calls ← IO.mkRef (#[] : Array String)
    let plan := { fixturePlan with modules }
    let backend := { stub with
      prepare := fun _ _ => pure { plan := some plan }
      build := fun _ _ _ group done => do
        check (!group.isEmpty) "Unused CPU slot launched an empty cloud job"
        let mut completed := done
        let mut results := #[]
        for m in group do
          check (m.imports.all fun name => completed.any (·.name == name)) "Missing local/external prerequisite"
          let blocked := m.imports.any fun name => completed.any fun r => r.name == name && r.status != .built
          let result : BuildResult := {
            name := m.name
            status := if blocked then .blocked else if seed % 2 == 0 && m.name == "M1" then .failed else .built }
          calls.modify (·.push m.name)
          completed := completed.push result
          results := results.push result
        return results
      finish := fun _ _ _ done => do
        check (done.size == modules.size && done.all (·.status == .built)) "Premature target completion"
        calls.modify (·.push "finish")
        return { name := "targets", status := .built }
      check := fun _ r _ _ => do
        calls.modify (·.push "check")
        return { mode := r.check.mode, success := true } }
    let req := { request with
      modulesPerJob := if seed % 3 == 0 then 0 else 1 + seed % 7
      check := { mode := if seed % 3 == 0 then .kernel else .none } }
    let environment := pool ((Array.range (1 + seed % 4)).map fun i => 1 + (seed + i) % 8)
    let direct ← (DirectInterpreter.interpret environment (workflow backend) req).run
    let saved ← IO.mkRef []
    let run := (replayReport (journal saved) (workflow backend req) environment).run
    let actual ← run
    check ((toJson direct).compress == (toJson actual).compress) "Direct/replay reports differ"
    let .ok report := actual | throw (IO.userError "Generated graph failed")
    let mut expected : Array BuildResult := #[]
    for m in modules do
      let blocked := m.imports.any fun dep => expected.any fun r => r.name == dep && r.status != .built
      expected := expected.push { name := m.name, status :=
        if blocked then .blocked else if seed % 2 == 0 && m.name == "M1" then .failed else .built }
    check (report.modules.map (fun r => (r.name, r.status)) == expected.map (fun r => (r.name, r.status)))
      "Batched results differ from sequential dependency evaluation"
    let before ← calls.get
    discard <| (replayReport (journal saved) (workflow backend req) (pool #[2])).run
    check ((← calls.get) == before) "Replay reran recorded jobs"
    if req.check.mode == .none then check (!before.contains "check") "Build-only invoked proof checker"
  -- Stop after recording the partition, then resume on a differently sized
  -- worker. Planning stays stable; native execution gets the replacement budget.
  let planned := pool #[1, 3]
  let replacement := pool #[6]
  let modules := (Array.range 12).map fun i => ⟨s!"R{i}", #[]⟩
  let groups ← IO.mkRef (#[] : Array (Array String))
  let backend := { stub with
    prepare := fun env _ => do
      check (env.workers == planned.workers && env.currentWorker == planned.currentWorker) "Wrong planning context"
      return { plan := some { fixturePlan with modules } }
    build := fun env _ _ group _ => do
      check (env.workers == replacement.workers && env.currentWorker == replacement.currentWorker) "Stale execution CPU budget after restart"
      groups.modify (·.push (group.map (·.name)))
      return group.map fun m => { name := m.name, status := .built }
    finish := fun env _ _ _ => do
      check (env.workers == replacement.workers && env.currentWorker == replacement.currentWorker) "Target build lost the execution environment"
      return { name := "targets", status := .built } }
  let saved ← IO.mkRef []
  let source := workflow backend request
  let .ok (.fork _ count) ← (ReplayInterpreter.step (journal saved) planned 10000
      (fun _ : Unit => source) () ⟨0, Location.root⟩).run
    | throw (IO.userError "Expected a recorded batch before restart")
  check (count == 2) "Wrong planned worker count"
  let .ok report ← (replayReport (journal saved) source replacement).run
    | throw (IO.userError "Could not resume batch on replacement worker")
  check (report.success && (← groups.get) ==
    ((partition modules #[] (planned.workers.map (·.cpus)) 0).filter (!·.isEmpty)).map (·.map (·.name)))
    "Replay repartitioned an existing batch using the replacement pool"
  for stage in ["prepare", "build", "finish", "check"] do
    let calls ← IO.mkRef (0 : Nat)
    let fail : IO Unit := do calls.modify (· + 1); throw (IO.userError "Job exception")
    let backend := { stub with
      prepare := fun env r => do
        if stage == "prepare" then fail
        stub.prepare env r
      build := fun env r p m done => do
        if stage == "build" then fail
        stub.build env r p m done
      finish := fun env r p done => do
        if stage == "finish" then fail
        stub.finish env r p done
      check := fun env r p b => do
        if stage == "check" then fail
        stub.check env r p b }
    let saved ← IO.mkRef []
    let req := { request with check := { mode := .kernel } }
    for _ in [:2] do
      let .error error ← (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) req).run
        | throw (IO.userError s!"{stage} exception not propagated")
      check (error == ⟨.application, "Job exception"⟩) "Wrong exception outcome"
    check ((← calls.get) == 1) s!"{stage} exception retried as a crash"
  for req in [
      { request with repository := "https://github.com/a/../b" },
      { request with revision := "--upload-pack=evil" },
      { request with subdirectory := "../escape" },
      { request with targets := #["--run=evil"] },
      { request with modulesPerJob := 100001 },
      { request with check := { mode := .kernel, allowedAxioms := #["sorryAx"] } }] do
    check req.validate.toOption.isNone "Invalid request accepted"
  for path in ["/etc/passwd", "../escape", "a/../../escape", "a//b"] do
    check (!Bundle.safePath path) "Unsafe artifact path accepted"
  check ((validateModules #[⟨"A", #["B"]⟩, ⟨"B", #["A"]⟩]).toOption.isNone) "Cycle accepted"
  check ((validateModules #[⟨"A", #[]⟩, ⟨"A", #[]⟩]).toOption.isNone) "Duplicate accepted"
  IO.println "PASS 80 generated DAGs: dependencies, direct/replay agreement, optional checking, durable exceptions"

private def copyFixture (source destination : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "cp", args := #["-R", source.toString ++ "/.", destination.toString] }
  check (out.exitCode == 0) "Fixture copy failed"
  if ← (destination / ".lake").pathExists then IO.FS.removeDirAll (destination / ".lake")
  if ← (destination / "Generated.lean").pathExists then IO.FS.removeFile (destination / "Generated.lean")

private def nativeTest (tools : Tools) (store : ObjectStore) (fixture : System.FilePath)
    (change : System.FilePath → IO Unit := fun _ => pure ())
    (req : LeanBuild.Request := request)
    (environment : ExecContext IO := pool #[2]) : IO LeanBuild.Report :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    let cwd := if req.subdirectory == "." then directory else directory / req.subdirectory
    IO.FS.createDirAll cwd
    copyFixture fixture cwd
    change cwd
    let prepared ← tools.prepareDirectory store req directory "fixture-commit"
    let backend := { tools.backend store with prepare := fun _ _ => pure prepared }
    let result ← (DirectInterpreter.interpret environment (workflow backend) req).run
    let .ok report := result | throw (IO.userError s!"Native workflow failed: {repr result}")
    return report

private def requireSuccess (store : ObjectStore) (report : LeanBuild.Report) : IO Unit := do
  if !report.success then
    let refs := ((report.modules.push report.build).filterMap (·.diagnostics)).toList.eraseDups
    for ref in refs do IO.eprintln (← Files.readText store ref)
  check report.success s!"Build failed: {repr report}"

private def helperFailureTests (tools : Tools) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    let policy := root / "policy.json"
    let input := root / "modules.json"
    let output := root / "results.json"
    IO.FS.writeFile policy (toJson request).pretty
    let library := tools.toolchain / "lib/lean" /
      (if System.Platform.isOSX then "libLake_shared.dylib" else "libLake_shared.so")
    let run := IO.Process.output {
      cmd := (tools.toolchain / "bin/lake").toString, cwd := directory
      env := #[("LEAN_NUM_THREADS", some "2")]
      args := #["--no-cache", "env", "lean", "--load-dynlib", library.toString, "--run",
        tools.helper.toString, "modules", policy.toString, input.toString, output.toString] }
    IO.FS.writeFile input (toJson #["Missing.Module"]).compress
    IO.FS.writeFile output "[]"
    check ((← run).exitCode != 0) "A stale result file hid a Lake fetch failure"
    IO.FS.removeFile output
    IO.FS.createDir output
    IO.FS.writeFile input (toJson #["Fixture.Base"]).compress
    check ((← run).exitCode != 0) "The helper swallowed a result-publication IO exception"

private def failedJobTests (tools : Tools) (store : ObjectStore) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    IO.FS.writeFile (directory / "Fixture/Base.lean")
      "import Lean\nrun_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile \"partial-output\" \"unused\")\nexample : False := True.intro\n"
    let req := { request with targets := #["+Fixture.Base"] }
    let prepared ← tools.prepareDirectory store req directory "fixture"
    let some plan := prepared.plan | throw (IO.userError "Could not prepare failed-job fixture")
    let created ← IO.mkRef (#[] : Array String)
    let tracking := { store with create := fun key bytes => do
      created.modify (·.push key)
      store.create key bytes }
    let results ← tools.build tracking req plan plan.modules #[]
    let [result] := results.toList | throw (IO.userError "Missing failed module result")
    check (result.status == .failed && result.artifacts.isNone) "Wrong failed-job outcome"
    let some diagnostics := result.diagnostics | throw (IO.userError "Lost failed-job diagnostics")
    let some manifest ← store.read diagnostics.manifest.key | throw (IO.userError "Missing diagnostics")
    let some text := String.fromUTF8? manifest | throw (IO.userError "Invalid diagnostics manifest")
    let chunks : Array BlobRef ← IO.ofExcept (Json.parse text >>= (·.getObjValAs? _ "chunks"))
    let expected := (chunks.map (·.key)).push diagnostics.manifest.key
    check ((← created.get).all expected.contains) "A failed-only job uploaded unreachable build artifacts"

private def publicationTests (tools : Tools) (store : ObjectStore) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    for artifact in [false, true] do
      let pending ← IO.mkRef true
      let preparing ← IO.mkRef true
      let flaky := { store with create := fun key bytes => do
        let saved ← store.create key bytes
        let target := artifact != (← preparing.get)
        if target then
          if ← pending.modifyGet fun old => (old, false) then throw (IO.userError "Publication failure")
        return saved }
      let backend := { tools.backend flaky with
        prepare := fun _ r => do
          let result ← tools.prepareDirectory flaky r directory "fixture"
          preparing.set false
          return result }
      let saved ← IO.mkRef []
      for _ in [:2] do
        let .error error ← (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) request).run
          | throw (IO.userError "Publication failure was swallowed")
        check (error == ⟨.application, "Publication failure"⟩) "Wrong publication error"
      check (!(← pending.get)) "Publication fault was not exercised"

private def bundleTests (store : ObjectStore) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let source := root / "source"
    IO.FS.createDir source
    IO.FS.writeFile (source / "original") "linked content"
    let linked ← IO.Process.output {
      cmd := "ln", args := #["-s", "original", (source / "link").toString] }
    check (linked.exitCode == 0) "Cannot create source symlink fixture"
    let manifest ← (← Bundle.snapshot source 10000).publish store
    let restored := root / "restored"
    Bundle.restore store restored manifest 10000
    check ((← IO.FS.readFile (restored / "link")) == "linked content" &&
      (← (restored / "link").symlinkMetadata).type == .file) "Safe file link was not materialized"
    for action in [IO.FS.writeFile (restored / "original") "changed", IO.FS.removeFile (restored / "original")] do
      action
      let rejected ← try
        discard <| Bundle.delta restored 10000 manifest manifest
        pure false
      catch _ => pure true
      check rejected "A prerequisite was overwritten or deleted"
      Bundle.restore store restored manifest 10000
    let oversized ← try
      discard <| Bundle.delta restored 1 manifest
      pure false
    catch _ => pure true
    check oversized "Unchanged files did not count toward workspace size"
    IO.FS.removeFile (restored / "original")
    IO.FS.createDir (restored / "original")
    let replaced ← try
      discard <| Bundle.delta restored 10000 manifest manifest
      pure false
    catch _ => pure true
    check replaced "A prerequisite file was replaced by a directory"
    IO.FS.removeDir (restored / "original")
    Bundle.restore store restored manifest 10000
    IO.FS.removeFile (source / "link")
    -- A restored dependency checkout refreshes its Git index when Lake checks
    -- its revision. This must not become an artifact conflict between workers.
    let git := source / ".lake/packages/dependency/.git"
    IO.FS.createDirAll git
    IO.FS.writeFile (git / "index") "old cached stat data"
    IO.FS.writeFile (git / "HEAD") "pinned-commit"
    let baseline ← (← Bundle.snapshot source 10000).publish store
    IO.FS.writeFile (git / "index") "refreshed cached stat data"
    let changed ← Bundle.delta source 10000 baseline baseline
    check changed.paths.isEmpty "Git index refresh became a parallel artifact"
    let final ← Bundle.delta source 10000 baseline
    check (final.paths.contains ".lake/packages/dependency/.git/index") "Final workspace lost its Git index"
    IO.FS.writeFile (git / "HEAD") "different-commit"
    let rejected ← try
      discard <| Bundle.delta source 10000 baseline baseline
      pure false
    catch _ => pure true
    check rejected "A module changed the pinned Git revision"
    for target in ["../restored/original", "."] do
      let linked ← IO.Process.output {
        cmd := "ln", args := #["-s", target, (source / "link").toString] }
      check (linked.exitCode == 0) "Cannot create rejected symlink fixture"
      let rejected ← try
        discard <| Bundle.snapshot source 10000
        pure false
      catch _ => pure true
      check rejected "Snapshot followed a directory or external symlink"
      IO.FS.removeFile (source / "link")
    let some first := manifest[0]? | throw (IO.userError "Missing snapshot entry")
    let other := { first with file.sha256 := ← Digest.bytes "conflicting".toUTF8 }
    check ((Bundle.merge #[first] #[other]).toOption.isNone) "Parallel artifact conflict accepted"

private def packCacheTests (store : ObjectStore) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let source := root / "source"
    IO.FS.createDir source
    for i in [:100] do IO.FS.writeFile (source / s!"file-{i}") s!"content-{i}"
    IO.FS.writeFile (source / "empty") ""
    let manifest ← (← Bundle.snapshot source 10000).publish store
    let some entry := manifest[0]? | throw (IO.userError "Empty pack fixture")
    check (manifest.all (·.file.pack == entry.file.pack)) "Files were not packed together"
    let reads ← IO.mkRef (0 : Nat)
    let counting := { store with read := fun key => do
      reads.modify (· + 1)
      store.read key }
    let cache : Bundle.Cache := { directory := root / "cache", bytes := 2000 }
    let restored := root / "restored"
    Bundle.restore counting restored manifest 10000 (some cache)
    check ((← reads.get) == 2) "Small files required separate blob reads"
    reads.set 0
    IO.FS.writeFile (restored / "file-1") "modified private copy"
    Bundle.restore counting restored manifest 10000 (some cache)
    check ((← reads.get) == 0 && (← IO.FS.readFile (restored / "file-1")) == "content-1")
      "Cache was not reused or private work changed a cached pack"
    IO.FS.writeFile (cache.directory / entry.file.pack.sha256) "corrupt cache"
    Bundle.restore counting restored manifest 10000 (some cache)
    check ((← reads.get) == 2) "Corrupt cache was trusted"
    -- A corrupt pack may be shorter than the replacement. Reserve its expected
    -- size even when a file with this cache key already exists.
    let repairCache : Bundle.Cache := { directory := root / "repair-cache", bytes := entry.file.pack.size }
    IO.FS.createDir repairCache.directory
    IO.FS.writeFile (repairCache.directory / entry.file.pack.sha256) ""
    IO.FS.writeFile (repairCache.directory / "older-pack") "occupied space"
    Bundle.restore store (root / "repaired") manifest 10000 (some repairCache)
    let mut cachedBytes := 0
    for file in ← repairCache.directory.readDir do
      cachedBytes := cachedBytes + (← file.path.metadata).byteSize.toNat
    check (cachedBytes ≤ repairCache.bytes) "Repairing a short corrupt pack exceeded the cache budget"
    let offline := { store with read := fun _ => throw (IO.userError "No download expected") }
    let tasks ← (Array.range 2).mapM fun i => IO.asTask
      (Bundle.restore offline (root / s!"concurrent-{i}") manifest 10000 (some cache)) .dedicated
    for task in tasks do IO.ofExcept task.get
    -- Lowering the capacity removes old packs; a pack larger than the cache is
    -- still restorable via a private temporary file without growing the cache.
    Bundle.restore store restored manifest 10000 (some { cache with bytes := 1 })
    check (← cache.directory.readDir).isEmpty "Cache size limit was exceeded"
    for bad in #[
        { entry with path := "../escape" },
        { entry with file.offset := entry.file.pack.size + 1 },
        { entry with file.sha256 := "invalid" },
        { entry with file.format := "unknown" }] do
      let rejected ← try Bundle.restore store restored #[bad] 10000; pure false catch _ => pure true
      check rejected "Invalid packed file accepted"
    let rejected ← try Bundle.restore store restored #[entry, entry] 10000; pure false catch _ => pure true
    check rejected "Duplicate packed path accepted"
    -- A file can cross the storage chunk boundary inside a larger pack.
    let large := root / "large"
    IO.FS.createDir large
    let bytes := ByteArray.mk ((Array.range (Files.chunkSize + 37)).map fun i => (i % 251).toUInt8)
    IO.FS.writeBinFile (large / "spanning") bytes
    IO.FS.writeFile (large / "tail") "last file"
    let packed ← (← Bundle.snapshot large (2 * Files.chunkSize)).publish store
    reads.set 0
    Bundle.restore counting (root / "large-restored") packed (2 * Files.chunkSize)
    check ((← reads.get) == 3 && (← IO.FS.readBinFile (root / "large-restored/spanning")) == bytes &&
      (← IO.FS.readFile (root / "large-restored/tail")) == "last file") "Cross-chunk pack restore failed"
    IO.println "PASS packed transfers, private copies, bounded cache, corruption recovery, and concurrent restores"

private def workspaceTests (store : ObjectStore) : IO Unit := IO.FS.withTempDir fun root => do
  let source := root / "source"
  IO.FS.createDir source
  IO.FS.writeFile (source / "input") "prepared source"
  let files ← (← Bundle.snapshot source 10000).publish store
  let ref ← Files.putJson store files
  let cache := root / "workspace"
  let use := Workspace.use store (some cache) "build-a"
  use fun session => do
    let manifest ← session.readManifest ref
    Bundle.synchronize store session.directory manifest 10000
    session.commit
  let offline := { store with read := fun _ => throw (IO.userError "Unnecessary blob read") }
  Workspace.use offline (some cache) "build-a" fun session => do
    let manifest ← session.readManifest ref
    check (← (session.directory / "input").pathExists) "Clean workspace was discarded"
    let before ← (session.directory / "input").metadata
    Bundle.synchronize offline session.directory manifest 10000
    check ((← (session.directory / "input").metadata).modified == before.modified) "Cached source was rewritten"
    IO.FS.writeFile (session.directory / "output") "published output"
    discard <| (← Bundle.snapshot session.directory 10000).publish store
    session.commit
  use fun session => do
    let manifest ← session.readManifest ref
    Bundle.synchronize offline session.directory manifest 10000
    check (!(← (session.directory / "output").pathExists)) "Replay reused its own output"
    session.commit
  let marker := cache / "ready.json"
  IO.FS.writeFile marker ((← IO.FS.readFile marker).replace "input" "wrong")
  use fun session => do
    let manifest ← session.readManifest ref
    check ((toJson manifest).compress == (toJson files).compress) "Corrupt cached manifest changed committed inputs"
    session.commit
  -- Missing/corrupt files are repaired even when the descriptor says clean.
  for damage in [IO.FS.writeFile (cache / "project/input") "bad", IO.FS.removeFile (cache / "project/input")] do
    damage
    use fun session => do
      let manifest ← session.readManifest ref
      Bundle.synchronize store session.directory manifest 10000
      check ((← IO.FS.readFile (session.directory / "input")) == "prepared source") "Damaged cache not repaired"
      session.commit
  -- A stopped attempt may leave arbitrary untracked files. No clean marker
  -- means none survive into the next attempt, even in a new Session.
  use fun session => IO.FS.writeFile (session.directory / "partial") "unfinished"
  use fun session => do
    check (!(← (session.directory / "input").pathExists) && !(← (session.directory / "partial").pathExists)) "Interrupted workspace reused"
    Bundle.synchronize store session.directory files 10000
    session.commit
  let failed ← try
    use fun session => do
      IO.FS.writeFile (session.directory / "partial") "failed"
      throw (IO.userError "job failure")
    pure false
  catch _ => pure true
  check failed "Exception was swallowed"
  use fun session => do
    check (!(← (session.directory / "input").pathExists) && !(← (session.directory / "partial").pathExists)) "Failed workspace reused"
    Bundle.synchronize store session.directory files 10000
    session.commit
  Workspace.use store (some cache) "build-b" fun session => do
    check (!(← (session.directory / "input").pathExists)) "Different build reused a workspace"
  IO.println "PASS reusable workspaces: no redundant transfers, replay isolation, corruption repair, interrupted/failed attempts"

private def toolchainTests : IO Unit :=
  IO.FS.withTempDir fun root => do
    let source := root / "release/bin"
    IO.FS.createDirAll source
    IO.FS.writeFile (source / "lean") "#!/bin/sh\nif [ \"$1\" = --version ]; then echo 'Lean (version 4.35.0, fixture)'; else test -f \"$1\"; fi\n"
    IO.FS.writeFile (source / "lake") "#!/bin/sh\nexit 0\n"
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x", (source / "lean").toString, (source / "lake").toString] }
    check (mode.exitCode == 0) "Cannot prepare toolchain fixture"
    let archive := root / "release.tar.zst"
    let packed ← IO.Process.output { cmd := "tar", args := #["--zstd", "-cf", archive.toString, "-C", root.toString, "release"] }
    check (packed.exitCode == 0) "Cannot pack toolchain fixture"
    let release : Toolchain.Release := { version := "4.35.0", platform := "linux_aarch64", sha256 := ← Digest.file archive.toString }
    let helper := root / "Helper.lean"
    IO.FS.writeFile helper "-- fixture"
    let cache := root / "toolchains"
    IO.FS.createDirAll (cache / s!"{release.sha256}.pending")
    IO.FS.writeFile (cache / s!"{release.sha256}.pending" / "interrupted") "partial"
    let downloads ← IO.mkRef (0 : Nat)
    let download : String → System.FilePath → IO Unit := fun url path => do
      check (url == "https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux_aarch64.tar.zst") "Wrong release URL"
      downloads.modify (· + 1)
      IO.FS.writeBinFile path (← IO.FS.readBinFile archive)
    let installed ← Toolchain.ensure release cache helper download
    check ((← (installed / "bin/lean").pathExists) && (← downloads.get) == 1) "Toolchain not installed"
    let same ← Toolchain.ensure release cache helper fun _ _ => throw (IO.userError "Must reuse toolchain")
    check (same == installed && !(← (cache / s!"{release.sha256}.pending").pathExists)) "Installation not reused/cleaned"
    let rejected ← try
      discard <| Toolchain.ensure release (root / "corrupt") helper fun _ path => IO.FS.writeFile path "bad archive"
      pure false
    catch _ => pure true
    check (rejected && !(← (root / "corrupt" / release.sha256).pathExists)) "Unverified toolchain was published"
    let rejected ← try
      discard <| Toolchain.ensure release (root / "bad-helper") (root / "missing.lean") download
      pure false
    catch _ => pure true
    check (rejected && !(← (root / "bad-helper" / release.sha256).pathExists)) "Unchecked helper was published"
    for bad in #[{ release with version := "../escape" }, { release with platform := "../escape" },
        { release with sha256 := "invalid" }] do
      check bad.validate.toOption.isNone "Invalid release accepted"
    IO.println "PASS pinned toolchain download, checksum rejection, helper check, interrupted installation and reuse"

/-- Measure executing tasks, not merely the inherited environment variable. -/
private def threadProbe : String := String.intercalate "\n" [
  "private def checkThreadPool (expected : Nat) : IO Unit := do",
  "  let counts ← Std.Mutex.new ((0, 0) : Nat × Nat)",
  "  let tasks ← (Array.range 16).mapM fun _ => IO.asTask do",
  "    counts.atomically do modify fun (active, peak) => (active + 1, max peak (active + 1))",
  "    IO.sleep 30",
  "    counts.atomically do modify fun (active, peak) => (active - 1, peak)",
  "  for task in tasks do IO.ofExcept (← IO.wait task)",
  "  let (_, peak) ← counts.atomically get",
  "  unless peak == expected do throw (IO.userError s!\"Expected {expected} threads, observed {peak}\")", ""]

private def nativeTests : IO Unit := IO.FS.withTempDir fun cacheRoot => do
  toolchainTests
  let tools ← Tools.fromEnvironment
  let tools := { tools with cache := some { directory := cacheRoot / "packs" } }
  let fixture ← IO.FS.realPath "fixtures/Diamond"
  let full ← IO.FS.realPath "fixtures/FullBuild"
  helperFailureTests tools fixture
  let store := objects (← IO.mkRef {})
  failedJobTests tools store fixture
  bundleTests store
  packCacheTests store
  workspaceTests store
  let built ← nativeTest tools store fixture (environment := pool #[2, 2])
  requireSuccess store built
  check (built.modules.size == 4 && built.verification.isNone && built.build.status == .built)
    "Build-only report is incorrect"
  let split ← nativeTest tools store fixture (req := { request with modulesPerJob := 2 })
  requireSuccess store split
  let [base, left, right, final] := split.modules.toList | throw (IO.userError "Missing split results")
  check (left.artifacts.isSome && left.artifacts == right.artifacts &&
    base.artifacts != left.artifacts && final.artifacts != left.artifacts)
    "Bounded jobs lost their shared artifact manifests across a dependency boundary"
  let helper := cacheRoot / "ThreadHelper.lean"
  let original ← IO.FS.readFile tools.helper
  IO.FS.writeFile helper ("import Std.Sync.Mutex\n" ++
    original.replace "def main (args : List String) : IO UInt32 := do"
      (threadProbe ++ "\ndef main (args : List String) : IO UInt32 := do\n  checkThreadPool ((← IO.getEnv \"LEAN_NUM_THREADS\").bind String.toNat? |>.getD 0)"))
  let concurrent ← nativeTest { tools with helper } store fixture (fun directory => do
    for (name, other) in [("Left", "Right"), ("Right", "Left")] do
      let path := directory / "Fixture" / s!"{name}.lean"
      let source ← IO.FS.readFile path
      let command := String.intercalate "\n" [
        "run_cmd Lean.Elab.Command.liftIO do",
        "  unless (← IO.getEnv \"LEAN_NUM_THREADS\") == some \"2\" do",
        "    throw (IO.userError \"Wrong worker CPU budget\")",
        s!"  IO.FS.writeFile \"{name}.started\" \"started\"",
        "  let started ← IO.monoMsNow",
        s!"  while !(← System.FilePath.pathExists \"{other}.started\") do",
        "    if (← IO.monoMsNow) - started > 10000 then",
        "      throw (IO.userError \"Sibling module did not run concurrently\")",
        "    IO.sleep 20", ""]
      IO.FS.writeFile path ("import Lean\nimport Std.Sync.Mutex\n" ++ source ++ "\n" ++ threadProbe ++ "\nrun_cmd Lean.Elab.Command.liftIO (checkThreadPool 1)\n" ++ command))
  requireSuccess store concurrent
  let some left := concurrent.modules.find? (·.name == "Fixture.Left") | throw (IO.userError "Missing Left")
  let some right := concurrent.modules.find? (·.name == "Fixture.Right") | throw (IO.userError "Missing Right")
  check (left.artifacts.isSome && left.artifacts == right.artifacts && left.diagnostics == right.diagnostics)
    "One local job published separate artifacts/diagnostics for each module"
  IO.println "PASS native modules overlap within one Lake job, inherit CPU budget, and share one artifact bundle"
  let defaults ← nativeTest tools store fixture (req := { request with targets := #[] })
  requireSuccess store defaults
  let reused ← nativeTest tools store fixture (req := { request with cache := .reuse, targets := #["+Fixture.Final:olean"] })
  requireSuccess store reused
  let qualified ← nativeTest tools store fixture (req := { request with targets := #["@build_fixture/Fixture"] })
  requireSuccess store qualified
  let oversized ← nativeTest tools store fixture (req := { request with limits := { request.limits with bytes := 1 } })
  check (!oversized.success && (oversized.message.splitOn "artifact byte limit").length > 1) "Oversized workspace accepted"
  let req := { request with check := { mode := .kernel, theorems := #["Fixture.result"] } }
  let report ← nativeTest tools store fixture (req := req)
  requireSuccess store report
  let cached ← nativeTest tools store fixture (fun d => do
    IO.FS.writeFile (d / "Fixture/Unrelated.lean") "theorem unrelated : False := by sorry\n"
    let result ← IO.Process.output {
      cmd := (tools.toolchain / "bin/lake").toString
      cwd := d, args := #["--no-cache", "build", "+Fixture.Unrelated"] }
    check (result.exitCode == 0) "Cannot prepare unrelated cached module")
    { req with cache := .reuse }
  requireSuccess store cached
  check (!cached.build.builtModules.contains "Fixture.Unrelated" && cached.build.builtModules.size == 4)
    "Unrelated cached modules entered the verification closure"
  let some verified := report.verification | throw (IO.userError "No verification report")
  check (verified.theorems.map (·.name) == #["Fixture.result"] && verified.exportFile.isSome)
    "Missing theorem or combined export"
  let some ref := report.build.artifacts | throw (IO.userError "No completed artifacts")
  let manifest : Bundle.Manifest ← Files.readJson store ref
  check (manifest.any (·.path.endsWith "Fixture/Final.olean")) "No final olean"
  publicationTests tools store fixture
  -- Native output must agree with an ordinary Lake build, including -K options,
  -- generated sources, default executable targets, C FFI and project subdirectories.
  for subdir in [".", "packages/app"] do
    let req := { request with targets := #[], subdirectory := subdir, options := ({} : Std.TreeMap String String).insert "greeting" "51" }
    let native ← nativeTest tools store full (req := req)
    requireSuccess store native
    IO.FS.withTempDir fun root => do
      let actual := root / "actual"
      let some ref := native.build.artifacts | throw (IO.userError "Missing executable bundle")
      Bundle.restore store actual (← Files.readJson store ref) req.limits.bytes
      let binary := (if subdir == "." then actual else actual / subdir) / ".lake/build/bin/fixture_app"
      let actualRun ← IO.Process.output { cmd := binary.toString }
      let expected := root / "expected"
      IO.FS.createDir expected
      copyFixture full expected
      let built ← IO.Process.output {
        cmd := (tools.toolchain / "bin/lake").toString
        cwd := expected, args := #["--no-cache", "-Kgreeting=51", "build"] }
      check (built.exitCode == 0) s!"Reference Lake failed: {built.stderr}"
      let expectedRun ← IO.Process.output { cmd := (expected / ".lake/build/bin/fixture_app").toString }
      check (actualRun.exitCode == 0 && actualRun.stdout == expectedRun.stdout && actualRun.stdout == "52\n")
        "Distributed executable differs from ordinary Lake"
  let custom ← nativeTest tools store full (req := { request with targets := #["receipt"] })
  requireSuccess store custom
  check custom.modules.isEmpty "Opaque custom target was treated as a Lean module"
  let some ref := custom.build.artifacts | throw (IO.userError "Custom artifact missing")
  let entries : Bundle.Manifest ← Files.readJson store ref
  let some entry := entries.find? (·.path == "receipt.txt") | throw (IO.userError "Output outside .lake/build lost")
  IO.FS.withTempDir fun root => do
    Bundle.restore store root #[entry] req.limits.bytes
    check ((← IO.FS.readFile (root / entry.path)) == "built 41\n") "Wrong custom output"
  let replacement ← nativeTest tools store full (fun d => do
    IO.FS.writeFile (d / "replaced") "old file"
    IO.FS.writeFile (d / "deleted") "old file"
    let config ← IO.FS.readFile (d / "lakefile.lean")
    IO.FS.writeFile (d / "lakefile.lean") (config ++
      "\ntarget replaceFile pkg : FilePath := do\n  IO.FS.removeFile (pkg.dir / \"replaced\")\n  IO.FS.removeFile (pkg.dir / \"deleted\")\n  IO.FS.createDir (pkg.dir / \"replaced\")\n  let output := pkg.dir / \"replaced\" / \"result\"\n  IO.FS.writeFile output \"new file\"\n  return Job.pure output\n"))
    { request with targets := #["replaceFile"] }
  requireSuccess store replacement
  IO.FS.withTempDir fun root => do
    let some ref := replacement.build.artifacts | throw (IO.userError "Missing replaced artifact")
    Bundle.restore store root (← Files.readJson store ref) request.limits.bytes
    check ((← IO.FS.readFile (root / "replaced/result")) == "new file" && !(← (root / "deleted").pathExists))
      "Final manifest resurrected replaced or deleted files"
  let overlap ← nativeTest tools store full (fun d => do
    let config ← IO.FS.readFile (d / "lakefile.lean")
    IO.FS.writeFile (d / "lakefile.lean") (config.replace "package full_build_fixture"
      "package full_build_fixture where\n  buildDir := \"../..\""))
    { request with subdirectory := "packages/app", targets := #[] }
  check (!overlap.success && (overlap.message.splitOn "must not contain a package").length > 1)
    "An overlapping build directory was cleaned"
  let unknown ← nativeTest tools store fixture (req := { request with targets := #["missing"] })
  check (!unknown.success) "Unknown Lake target accepted"
  let noProofs ← nativeTest tools store full (req := { request with targets := #["receipt"], check := { mode := .kernel } })
  check (!noProofs.success && noProofs.build.status == .built) "Vacuous proof-check success on a native-only target"
  let changedInput ← nativeTest tools store fixture (fun d => do
    IO.FS.writeFile (d / "prepared-input") "original"
    let code ← IO.FS.readFile (d / "Fixture/Base.lean")
    IO.FS.writeFile (d / "Fixture/Base.lean")
      ("import Lean\nrun_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile \"prepared-input\" \"changed\")\n" ++ code))
  check (!changedInput.success && changedInput.modules.any (fun m =>
    m.name == "Fixture.Base" && (m.message.splitOn "changed a prerequisite").length > 1))
    "A module job silently changed prepared inputs"
  let leanConfig ← nativeTest tools store fixture (fun d => do
    IO.FS.removeFile (d / "lakefile.toml")
    IO.FS.writeFile (d / "lakefile.lean") "import Lake\nopen Lake DSL\npackage build_fixture\nlean_lib Fixture\n")
  requireSuccess store leanConfig
  let customDefaults ← nativeTest tools store fixture (fun d => do
    IO.FS.removeFile (d / "lakefile.toml")
    IO.FS.writeFile (d / "lakefile.lean")
      "import Lake\nopen Lake DSL\npackage build_fixture\nlean_lib Fixture where\n  defaultFacets := #[]\n"
    IO.FS.writeFile (d / "Fixture.lean") "This source is intentionally invalid.\n")
    { request with targets := #["Fixture"] }
  requireSuccess store customDefaults
  check customDefaults.modules.isEmpty "Custom library defaults forced an unrelated Lean compilation"
  let runtime ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Base.lean")
      "namespace Fixture\ndef twice (n : Nat) := n + n\nunsafe def castValue (n : Nat) : Int := unsafeCast n\npartial def loop (n : Nat) : Nat := loop (n + 1)\ntheorem twice_zero : twice 0 = 0 := rfl\n")
  requireSuccess store runtime
  let sorryReport ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nnamespace Fixture\ntheorem left : twice 1 = 2 := by sorry\n") req
  check (!sorryReport.success && sorryReport.build.status == .built &&
    sorryReport.verification.any (!·.success)) "Build success and proof rejection conflated"
  let bad ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nexample : False := True.intro\n")
  check (!bad.success && bad.modules.any (fun m => m.name == "Fixture.Final" && m.status == .blocked) &&
    bad.modules.any (fun m => m.name == "Fixture.Left" && m.status == .failed) &&
    bad.modules.any (fun m => m.name == "Fixture.Right" && m.status == .built))
    "Batched failure blocked an independent module or lost the dependent failure"
  for name in ["Fixture.missing", "Fixture.twice"] do
    let missing ← nativeTest tools store fixture (req := { req with check := { mode := .kernel, theorems := #[name] } })
    check (!missing.success && missing.build.status == .built) "Missing/non-theorem requirement accepted"
  let privateSorry ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean")
      "module\npublic import Fixture.Base\nprivate theorem hidden : False := by sorry\nnamespace Fixture\npublic theorem left : twice 1 = 2 := rfl\n") req
  check (!privateSorry.success) "Private sorry escaped verification"
  let assumption ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean")
      "import Fixture.Base\nnamespace Fixture\naxiom assumeLeft : twice 1 = 2\ntheorem left : twice 1 = 2 := assumeLeft\n") req
  check (!assumption.success) "Undeclared axiom accepted"
  let tighter ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Base.lean")
      "namespace Fixture\ndef twice (n : Nat) := n + n\ntheorem standardAxiom (p q : Prop) (h : p ↔ q) : p = q := propext h\n")
    { req with check := { mode := .kernel, allowedAxioms := #[] } }
  check (!tighter.success) "Stricter axiom policy ignored"
  let paranoid ← nativeTest tools store fixture (req := { req with targets := #["+Fixture.Base"], check := { mode := .paranoid } })
  requireSuccess store paranoid
  let some verifiedParanoid := paranoid.verification | throw (IO.userError "Missing paranoid result")
  let some log := verifiedParanoid.diagnostics | throw (IO.userError "Missing checker log")
  let text ← Files.readText store log
  for name in ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"] do
    check ((text.splitOn s!"{name} kernel accepts").length > 1) s!"Skipped checker {name}"
  -- Corrupt an exported proof: it must reach the kernel and be rejected.
  IO.FS.withTempDir fun root => do
    let directory := root / "check"
    IO.FS.createDir directory
    let some exportRef := verified.exportFile | throw (IO.userError "No export")
    let path := root / "proof.ndjson"
    Files.download store exportRef path req.limits.bytes
    check (← tools.verifyExport directory req.limits path).isOk "Published export cannot be rechecked"
    if System.Platform.isOSX then
      check (!(← { tools with sandbox := true }.verifyExport directory req.limits path).isOk) "Sandbox silently bypassed"
    let mut changed := false
    let mut lines : Array String := #[]
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.isEmpty then continue
      let json ← IO.ofExcept (Json.parse line)
      match json.getObjVal? "thm" with
      | .error _ => lines := lines.push line
      | .ok declaration =>
        changed := true
        let fields ← IO.ofExcept declaration.getObj?
        let type ← IO.ofExcept (declaration.getObjVal? "type")
        lines := lines.push (Json.mkObj [("thm", .obj (fields.insert "value" type))]).compress
    check changed "No theorem to corrupt"
    IO.FS.writeFile path (String.intercalate "\n" lines.toList ++ "\n")
    check (!(← tools.verifyExport directory req.limits path).isOk) "Corrupt proof accepted"
    check (((← IO.FS.readFile (root / "check.stdout")).splitOn "Lean default kernel rejected").length > 1)
      "Corrupt proof did not reach kernel"
    IO.FS.writeFile path "{}\nnot NDJSON\n"
    check (!(← tools.verifyExport directory req.limits path).isOk) "Malformed export accepted"
  for version in ["4.34.1", "4.36.0"] do
    let mismatch ← nativeTest tools store fixture (fun d =>
      IO.FS.writeFile (d / "lean-toolchain") s!"leanprover/lean4:v{version}\n")
    check (!mismatch.success && mismatch.build.status == .failed) "Toolchain mismatch accepted"
  IO.println "PASS native Lake builds, executable/FFI/generated/custom targets, subdirectories, exports and kernel rejection"

def main (args : List String) : IO Unit := do
  generatedTests
  if args.contains "--native" then nativeTests
  if let ["--plan", path] := args then
    let modules : Array LeanBuild.Module ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)
    IO.ofExcept (validateModules modules)
    let stats ← checkPartition modules (pool #[7, 7, 7, 7])
    let reference := modelTicks (criticalOrder modules) 28
    let utilization := modules.size * 1000 / (stats.ticks * 28)
    IO.println s!"DAG: {modules.size} modules → {stats.rounds} rounds, {stats.jobs} jobs (4 × 7 CPUs)"
    IO.println s!"Unit-cost compute model: {stats.ticks} slots, {utilization / 10}.{utilization % 10}% CPU use; shared ready queue: {reference} slots. Excludes coordination, transfers and unequal compilation times."
