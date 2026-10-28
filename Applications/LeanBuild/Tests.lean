import LeanBuild
import LeanCloudRuntime.WorkQueueStore
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay

open Lean LeanCloud LeanCloudRuntime LeanBuild

private def check (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def noBlobs : ExecContext IO where
  cancellation := .never
  progress := .ignore
  queues := .unsupported
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

private def objects (ref : Std.Mutex (Std.HashMap String ByteArray)) : ObjectStore where
  ensureContainer := pure ()
  read key := ref.atomically do return (← get)[key]?
  create key bytes := ref.atomically do
    let saved ← get
    if let some old := saved[key]? then return old
    set (saved.insert key bytes)
    return bytes
  putContent key bytes := ref.atomically do
    unless (← get).contains key do modify (·.insert key bytes)
  size key := ref.atomically do return (← get)[key]?.map (·.size)
  erase key := ref.atomically (modify (·.erase key))
  list _ := return #[]

private def request : LeanBuild.Request := {
  repository := "https://github.com/palladin/lean-cloud"
  revision := "main", targets := #["+Fixture.Final"] }

private def fixturePlan : Plan := {
  commit := "fixture", toolchain := "fixture", platform := "fixture", source := default
  modules := #[⟨"Base", #[]⟩, ⟨"Final", #["Base"]⟩] }

private def stub : Backend IO := {
  prepare := fun _ _ => pure { plan := some fixturePlan }
  start := fun _ _ => pure ()
  builder := fun _ _ _ => pure ()
  results := fun _ p => pure (p.modules.map fun m => { name := m.name, status := .built })
  finish := fun _ _ _ _ => pure { name := "targets", status := .built } }

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

private def withEnvironment (store : ObjectStore) (base : ExecContext IO)
    (action : Environment IO → IO α) : IO α := do
  let conn ← LeanLinq.Sqlite.connect ":memory:"
  try
    WorkQueueStore.initializeSchema conn
    let scope := s!"test-{← IO.monoNanosNow}"
    let context := store.executionContextFor scope
    action { base.map MonadCloudExec.restore with
      blobs := context.blobs.map MonadCloudExec.restore
      queues := WorkQueueStore.provider conn (← Std.Mutex.new ()) scope }
  finally conn.close

/-- The same rolling coordinator, with task-backed compiler jobs for model tests. -/
private def runBuilders (env : Environment IO) (plan : Plan)
    (build : CancellationToken IO → LeanBuild.Module → Array BuildResult → IO BuildResult)
    (prefetch : CancellationToken IO → Array BuildResult → IO Unit := fun _ _ => pure ()) : IO Unit := do
  let prepared ← Std.Mutex.new ({} : Std.HashMap String (CancellationToken IO × Array BuildResult))
  let running ← IO.mkRef (#[] : Array (String × Task (Except IO.Error BuildResult)))
  let engine : Builders.Engine BuildResult := {
    prefetch
    prepare := fun stop m inputs => prepared.atomically (modify (·.insert m.name (stop, inputs)))
    submit := fun m => do
      let some (stop, inputs) ← prepared.atomically do return (← get)[m.name]?
        | throw (IO.userError "Submitted before preparation")
      let task ← IO.asTask (build stop m inputs) .dedicated
      running.modify (·.push (m.name, task))
    poll := do
      let mut waiting := #[]
      let mut done := #[]
      for (name, task) in ← running.get do
        if ← IO.hasFinished task then done := done.push (name, ← IO.ofExcept (← IO.wait task))
        else waiting := waiting.push (name, task)
      running.set waiting
      return done
    publish := fun _ _ result => pure result
    finish := check (← running.get).isEmpty "Finished with active compilers"
    cancel := do for (_, task) in ← running.get do discard <| IO.wait task }
  Builders.run env plan engine

private def builderSourceTest : IO Unit := do
  let sources : Array ProgramSource := cloud_sources%
  let current ← IO.mkRef (none : Option SourceSiteId)
  let calls ← IO.mkRef (0 : Nat)
  let line : IO String := do
    let some id ← current.get | throw (IO.userError "Builder has no source position")
    let some text := sources.findSome? fun source => do
      let site ← source.sites.find? (·.id == id)
      (source.text.splitOn "\n").toArray[site.line - 1]?
      | throw (IO.userError "Builder source is not bundled")
    return text
  let backend := { stub with builder := fun _ _ _ => do
    let text ← line
    check ((text.splitOn "Cloud.exec").length > 1 && (text.splitOn "backend.builder").length > 1)
      s!"Builder highlights its parent instead of its exec call: {text}"
    calls.modify (· + 1) }
  let saved ← IO.mkRef []
  let visit : ReplayInterpreter.Observer IO := fun _ source _ => current.set source
  let step := fun branch => (ReplayInterpreter.step (journal saved) (pool #[2, 2]) 100
    (workflow backend) request ⟨0, branch⟩ (some visit)).run
  let .ok (.fork location count) ← step Location.root
    | throw (IO.userError "Workflow did not suspend at parallel builders")
  check (((← line).splitOn "Cloud.parallel").length > 1) "Fork lost its own source position"
  for index in [:count] do
    let .ok .done ← step (location.child index)
      | throw (IO.userError "Builder branch did not complete")
  check ((← calls.get) == 2) "Did not inspect both builder branches"
  IO.println "PASS builder exec source locations through replay"

private def generatedTests : IO Unit := do
  for version in ["4.35.0", "4.35.1", "4.36.0", "5.0.0"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption == some version) "Supported release rejected"
  for version in ["3.99.0", "4.34.99", "4.35", "04.35.0", "4.35.0-rc1", "nightly"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption.isNone) "Unsupported release accepted"
  for old in ["check", "theorems", "allowedAxioms", "paranoid", "modules", "modulesPerJob"] do
    check ((fromJson? (α := LeanBuild.Request) ((toJson request).setObjVal! old Json.null)).toOption.isNone)
      "Removed request field was silently ignored"
  let store := objects (← Std.Mutex.new {})
  for seed in [:40] do
    let modules := (Array.range (4 + seed % 12)).map fun i => {
      name := s!"M{i}", imports := ((Array.range i).filter fun j =>
        (i * 37 + j * 7 + seed) % 3 == 0).map (s!"M{·}") : LeanBuild.Module }
    let plan := { fixturePlan with modules }
    let mut expected : Array (String × Status) := #[]
    for m in modules do
      let blocked := m.imports.any fun dep => expected.any fun (name, status) => name == dep && status != .built
      expected := expected.push (m.name, if blocked then .blocked else if seed % 2 == 0 && m.name == "M1" then .failed else .built)
    let seen ← Std.Mutex.new (#[] : Array String)
    let backend := { stub with
      prepare := fun _ _ => pure { plan := some plan }
      start := Builders.seed
      builder := fun env _ plan => runBuilders env plan fun _ m inputs => do
        check (m.imports.all fun dep => inputs.any (fun r => r.name == dep && r.status == .built)) "Built before prerequisites"
        seen.atomically (modify (·.push m.name))
        pure { name := m.name, status := if seed % 2 == 0 && m.name == "M1" then .failed else .built }
      results := Builders.results }
    let direct ← withEnvironment store (pool #[1 + seed % 4, 2]) fun env => do
      let context := env.map (fun action => captureIO (liftM action))
      let .ok direct ← (DirectInterpreter.interpret context (workflow backend) request).run
        | throw (IO.userError "Direct build failed")
      let stats ← (env.queues.open Builders.queueName).progress
      check (stats.completed == modules.size && stats.failed == (expected.filter (·.2 != .built)).size)
        "Shared progress lost or double-counted successful/failed modules"
      pure direct
    check (direct.modules.map (fun r => (r.name, r.status)) == expected) "Queue build differs from dependency evaluation"
    -- A fresh run namespace ensures replay really builds its own results.
    withEnvironment store (pool #[1 + seed % 4, 2]) fun env => do
      let context := env.map (fun action => captureIO (liftM action))
      let saved ← IO.mkRef []
      let .ok replay ← (replayReport (journal saved) (workflow backend request) context).run
        | throw (IO.userError "Replay build failed")
      check ((toJson direct).compress == (toJson replay).compress) "Direct/replay reports differ"
      let before ← seen.atomically get
      discard <| (replayReport (journal saved) (workflow backend request) context).run
      check ((← seen.atomically get) == before) "Replay reran completed modules"
  -- A SINGLE worker must advance a short chain while its unrelated long
  -- compiler is still running. A finite Lake batch cannot pass this rendezvous.
  withEnvironment store (pool #[3]) fun env => do
    let plan := { fixturePlan with modules := #[⟨"Slow", #[]⟩, ⟨"Fast", #[]⟩, ⟨"Child", #["Fast"]⟩] }
    let child ← IO.mkRef false
    Builders.seed env plan
    runBuilders env plan fun _ m _ => do
      if m.name == "Slow" then
        let deadline := (← IO.monoMsNow) + 3000
        while !(← child.get) do
          check ((← IO.monoMsNow) < deadline) "A batch barrier blocked the same worker's short chain"
          IO.sleep 10
      if m.name == "Child" then child.set true
      return { name := m.name, status := .built }
    check (← child.get) "Dependent module was never built"
  -- Other workers hold Gate/Far. Finishing Root must stop probing Target at
  -- missing Gate, rather than reading all of Target's unfinished prerequisites.
  withEnvironment store (pool #[2]) fun env => do
    let plan := { fixturePlan with modules := #[⟨"Gate", #[]⟩, ⟨"Far", #[]⟩,
      ⟨"Root", #[]⟩, ⟨"Target", #["Root", "Gate", "Far"]⟩] }
    Builders.seed env plan
    let queue := env.queues.open Builders.queueName
    discard (queue.receive 2)
    let stopped ← IO.mkRef false
    let probes ← IO.mkRef (#[] : Array String)
    let some names := env.blobs.names | throw (IO.userError "Missing result names")
    let env := { env with
      cancellation := ⟨stopped.get⟩
      queues := ⟨fun _ => { queue with complete := fun receipt failed => do
        queue.complete receipt failed
        stopped.set true }⟩
      blobs.names := some { names with read := fun name => do
        probes.modify (·.push name)
        names.read name } }
    runBuilders env plan fun _ m _ => pure { name := m.name, status := .built }
    check (!(← probes.get).contains (Builders.resultName "Far"))
      "Publication fetched prerequisites after a known missing dependency"
  -- Slots are replenished without claiming an unbounded ready frontier.
  -- A worker with a busy compiler must observe/download another worker's
  -- artifact before dequeuing its next job. Cursor catch-up must work too.
  withEnvironment store (pool #[2]) fun env => do
    let plan := { fixturePlan with modules := #[⟨"Published", #[]⟩, ⟨"Busy", #[]⟩] }
    Builders.seed env plan
    let queue := env.queues.open Builders.queueName
    let claimed ← queue.receive 1
    discard <| Builders.publishResult env { name := "Published", status := .built }
    queue.complete claimed[0]!.receipt false
    let prefetched ← IO.mkRef false
    runBuilders env plan (fun _ m _ => do
      let deadline := (← IO.monoMsNow) + 3000
      while !(← prefetched.get) do
        check ((← IO.monoMsNow) < deadline) "Busy worker did not prefetch the completion feed"
        IO.sleep 10
      return { name := m.name, status := .built })
      (fun _ results => if results.any (·.name == "Published") then prefetched.set true else pure ())
    check (← prefetched.get) "Completion catch-up skipped a committed artifact"
  withEnvironment store (pool #[3]) fun env => do
    let modules := (Array.range 33).map fun i => ⟨s!"M{i}", #[]⟩
    let plan := { fixturePlan with modules }
    let active ← Std.Mutex.new ((0, 0) : Nat × Nat)
    Builders.seed env plan
    runBuilders env plan fun _ m inputs => do
      check inputs.isEmpty "Independent modules acquired prerequisites"
      active.atomically (modify fun (n, peak) => (n + 1, max peak (n + 1)))
      IO.sleep 40
      active.atomically (modify fun (n, peak) => (n - 1, peak))
      return { name := m.name, status := .built }
    check ((← active.atomically get) == (0, 2)) "Compilation budget was not respected/utilized"
    check ((← Builders.results env plan).size == 33) "Pipeline dropped modules"
    check ((← (env.queues.open Builders.queueName).progress) == ⟨33, 0⟩) "Wrong global progress"
  withEnvironment store (pool #[2]) fun env => do
    Builders.seed env fixturePlan
    let rejected ← try
      runBuilders env fixturePlan fun _ _ _ => pure { name := "Other", status := .built }
      pure false
    catch _ => pure true
    check rejected "Accepted an unrequested module result"
  -- Independent builder sessions share only the queue and immutable results.
  withEnvironment store (pool #[2, 2, 2]) fun env => do
    let seen ← Std.Mutex.new (#[] : Array String)
    let modules := #[⟨"Root", #[]⟩] ++ (Array.range 24).map (fun i =>
      ⟨s!"M{i}", #["Root"] ++ ((Array.range i).filter (fun j => (i + j) % 3 == 0)).map (s!"M{·}")⟩)
    let plan := { fixturePlan with modules }
    Builders.seed env plan
    discard <| Parallel.map 3 (Array.range 3) fun worker =>
      runBuilders { env with currentWorker := { id := s!"w{worker}", cpus := 2 } } plan fun _ m inputs => do
        check (m.imports.all fun dep => inputs.any (fun r => r.name == dep && r.status == .built))
          "Concurrent builder started before all prerequisites"
        IO.sleep 10
        seen.atomically (modify (·.push m.name))
        pure { name := m.name, status := .built }
    check ((← seen.atomically get).size == 25) "Multiple builders lost or duplicated live claims"
    check ((← Builders.results env plan).all (·.status == .built)) "Concurrent builders did not complete"
  -- A crash after publishing a result but before notifying children reuses
  -- that result and repeats the notification; no module is forgotten.
  withEnvironment store (pool #[1]) fun env => do
    let queue := env.queues.open Builders.queueName
    let fail ← IO.mkRef true
    let executions ← IO.mkRef (0 : Nat)
    let interrupted := { env with queues := ⟨fun _ => { queue with send := fun values => do
      if ← fail.get then fail.set false; throw (IO.userError "Interrupted before notification")
      queue.send values }⟩ }
    let build := fun _ m _ => do
      executions.modify (· + 1)
      pure { name := m.name, status := .built : BuildResult }
    Builders.seed env fixturePlan
    let stopped ← try runBuilders interrupted fixturePlan build; pure false catch _ => pure true
    check stopped "Notification interruption was not exercised"
    runBuilders env fixturePlan build
    check ((← executions.get) == 2) "Restart rebuilt an already committed module"
    check ((← Builders.results env fixturePlan).size == 2) "Restart lost a dependent notification"
  withEnvironment store (pool #[1]) fun env => do
    let cancelled ← IO.mkRef false
    let env := { env with cancellation := ⟨cancelled.get⟩ }
    Builders.seed env fixturePlan
    runBuilders env fixturePlan fun _ m _ => do
      cancelled.set true
      pure { name := m.name, status := .built }
    check (← Builders.readResult env "Base").isNone "Cancellation committed the module's partial work"
    check (!(← (env.queues.open Builders.queueName).isIdle)) "Cancellation acknowledged unfinished work"
    cancelled.set false
    runBuilders env fixturePlan fun _ m _ => pure { name := m.name, status := .built }
    check ((← Builders.results env fixturePlan).size == 2) "Cancellation prevented later recovery"
  -- Renewal runs on a background task. Its failure must stop and join the
  -- compiler, propagate out of exec, and replay as a durable application error.
  withEnvironment store (pool #[2]) fun env => do
    let queue := env.queues.open Builders.queueName
    let env := { env with queues := ⟨fun _ => { queue with
      renew := fun _ => throw (IO.userError "Renewal transport failure") }⟩ }
    let calls ← IO.mkRef (0 : Nat)
    let stopped ← IO.mkRef false
    let backend := { stub with
      start := Builders.seed
      results := Builders.results
      builder := fun env _ plan => runBuilders env plan fun cancellation m _ => do
        calls.modify (· + 1)
        let deadline := (← IO.monoMsNow) + 15000
        while !(← cancellation.isRequested) do
          check ((← IO.monoMsNow) < deadline) "Renewal failure did not cancel the compiler"
          IO.sleep 20
        stopped.set true
        pure { name := m.name, status := .built } }
    let context := env.map (fun action => captureIO (liftM action))
    let saved ← IO.mkRef []
    for _ in [:2] do
      let .error error ← (replayReport (journal saved) (workflow backend request) context).run
        | throw (IO.userError "Renewal failure was swallowed")
      check (error == ⟨.application, "Renewal transport failure"⟩) "Wrong renewal failure outcome"
    check ((← stopped.get) && (← calls.get) == 1) "Renewal failure leaked or retried a compiler"
    check (← Builders.readResult env "Base").isNone "Renewal failure committed partial work"
  for stage in ["prepare", "builder", "finish"] do
    let calls ← IO.mkRef (0 : Nat)
    let fail : IO Unit := do calls.modify (· + 1); throw (IO.userError "Job exception")
    let backend := { stub with
      prepare := fun env r => do
        if stage == "prepare" then fail
        stub.prepare env r
      builder := fun env r p => do
        if stage == "builder" then fail
        stub.builder env r p
      finish := fun env r p done => do
        if stage == "finish" then fail
        stub.finish env r p done }
    let saved ← IO.mkRef []
    for _ in [:2] do
      let .error error ← (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) request).run
        | throw (IO.userError "Exception not propagated")
      check (error == ⟨.application, "Job exception"⟩) "Wrong exception outcome"
    check ((← calls.get) == 1) "Application failure retried as a crash"
  check ((validateModules #[⟨"A", #["B"]⟩, ⟨"B", #["A"]⟩]).toOption.isNone) "Cycle accepted"
  check ((validateModules #[⟨"A", #[]⟩, ⟨"A", #[]⟩]).toOption.isNone) "Duplicate accepted"
  IO.println "PASS 40 generated queue DAGs, direct/replay agreement, no round barrier, durable failures"

private def copyFixture (source destination : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "cp", args := #["-R", source.toString ++ "/.", destination.toString] }
  check (out.exitCode == 0) "Fixture copy failed"
  if ← (destination / ".lake").pathExists then IO.FS.removeDirAll (destination / ".lake")
  if ← (destination / "Generated.lean").pathExists then IO.FS.removeFile (destination / "Generated.lean")

private def nativeTest (tools : Tools) (store : ObjectStore) (fixture : System.FilePath)
    (change : System.FilePath → IO Unit := fun _ => pure ())
    (req : LeanBuild.Request := request)
    (environment : ExecContext IO := pool #[3]) : IO LeanBuild.Report :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    let cwd := if req.subdirectory == "." then directory else directory / req.subdirectory
    IO.FS.createDirAll cwd
    copyFixture fixture cwd
    change cwd
    let prepared ← { tools with threads := max 1 environment.currentWorker.cpus }.prepareDirectory store req directory "fixture-commit"
    let backend := { tools.backend store with prepare := fun _ _ => pure prepared }
    let result ← withEnvironment store environment fun env =>
      (DirectInterpreter.interpret (env.map (fun action => captureIO (liftM action))) (workflow backend) req).run
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
    let output := root / "results"
    let input := root / "requests"
    IO.FS.createDir input
    IO.FS.writeFile (input / "finish") ""
    IO.FS.writeFile policy (toJson request).pretty
    let library := tools.toolchain / "lib/lean" /
      (if System.Platform.isOSX then "libLake_shared.dylib" else "libLake_shared.so")
    let run (name : String) := do
      IO.FS.writeFile (input / "0.json") (toJson name).compress
      IO.Process.output {
      cmd := (tools.toolchain / "bin/lake").toString, cwd := directory
      env := #[("LEAN_NUM_THREADS", some "2")]
      args := #["--no-cache", "env", "lean", "--load-dynlib", library.toString, "--run",
        tools.helper.toString, "serve", policy.toString, input.toString, output.toString, directory.toString] }
    IO.FS.writeFile output "[]"
    check ((← run "Missing.Module").exitCode != 0) "A stale result file hid a Lake fetch failure"
    IO.FS.removeFile output
    IO.FS.createDir output
    IO.FS.createDir (output / "0.json")
    check ((← run "Fixture.Base").exitCode != 0) "The helper swallowed a result-publication IO exception"

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
    let results ← withEnvironment store (pool #[2]) fun env => do
      Builders.seed env plan
      tools.builder store env req plan
      Builders.results env plan
    let [result] := results.toList | throw (IO.userError "Missing failed module result")
    check (result.status == .failed && result.artifacts.isNone && result.diagnostics.isSome)
      "Failed module published artifacts or lost diagnostics"
    let mixed ← nativeTest tools store fixture (fun directory =>
      IO.FS.writeFile (directory / "Fixture/Left.lean")
        "import Fixture.Base\nexample : False := True.intro\n")
    check (!mixed.success && mixed.modules.any (fun r => r.name == "Fixture.Left" && r.status == .failed) &&
      mixed.modules.any (fun r => r.name == "Fixture.Right" && r.status == .built) &&
      mixed.modules.any (fun r => r.name == "Fixture.Final" && r.status == .blocked))
      "A failed module lost independent successes in the same Lake session"

/-- Two publications rendezvous while a third compiler waits for them. This
proves both concurrent publication and continued dependency admission. -/
private def streamingPublicationTest (tools : Tools) (store : ObjectStore) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    let signal := root / "published"
    IO.FS.writeFile (directory / "Fixture/Slow.lean") (String.intercalate "\n" [
      "import Lean", "import Fixture.Base",
      "run_cmd Lean.Elab.Command.liftIO do",
      "  let deadline := (← IO.monoMsNow) + 15000",
      s!"  while !(← System.FilePath.pathExists {reprStr signal.toString}) do",
      "    if (← IO.monoMsNow) > deadline then throw (IO.userError \"Publication waited for the Lake batch\")",
      "    IO.sleep 20", ""])
    let req := { request with targets := #["+Fixture.Slow", "+Fixture.Left", "+Fixture.Right", "+Fixture.Final"] }
    let tools := { tools with threads := 3 }
    let prepared ← tools.prepareDirectory store req directory "fixture"
    let some plan := prepared.plan | throw (IO.userError "Cannot prepare streaming publication fixture")
    withEnvironment store (pool #[3]) fun env => do
      let some names := env.blobs.names | throw (IO.userError "Missing named blobs")
      let published ← Std.Mutex.new (0 : Nat)
      let names : BlobNames IO := { names with publish := fun name ref => do
        let selected ← names.publish name ref
        if #["Fixture.Left", "Fixture.Right"].any (fun module => name == Builders.resultName module) then
          let result : BuildResult ← IO.ofExcept (Json.parse (← env.blobs.readText selected) >>= fromJson?)
          let some artifacts := result.artifacts | throw (IO.userError "Published module has no artifacts")
          let manifest : Bundle.Manifest ← Files.readJson store artifacts
          check (!manifest.isEmpty) "Published empty module artifacts"
          published.atomically (modify (· + 1))
          let deadline := (← IO.monoMsNow) + 10000
          while (← published.atomically get) < 2 do
            check ((← IO.monoMsNow) < deadline) "Module publications did not overlap"
            IO.sleep 10
        if name == Builders.resultName "Fixture.Final" then IO.FS.writeFile signal "ready"
        return selected }
      let env := { env with blobs := { env.blobs with names := some names } }
      Builders.seed env plan
      tools.builder store env req plan
      let results ← Builders.results env plan
      check (results.all (·.status == .built)) "Early publication fixture failed"
      check ((← published.atomically get) == 2) "Concurrent publications were not exercised"
    IO.println "PASS persistent Lake: publications overlap and the same worker feeds a newly ready dependent while another compiler is running"

private def publicationTests (tools : Tools) (store : ObjectStore) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    for artifact in [false, true] do
      let pending ← Std.Mutex.new true
      let preparing ← IO.mkRef true
      let flaky := { store with putContent := fun key bytes => do
        store.putContent key bytes
        let target := artifact != (← preparing.get)
        if target then
          let inject ← pending.atomically do
            let old ← get
            set false
            return old
          if inject then throw (IO.userError "Publication failure")
        pure () }
      let backend := { tools.backend flaky with
        prepare := fun _ r => do
          let result ← tools.prepareDirectory flaky r directory "fixture"
          preparing.set false
          return result }
      withEnvironment flaky (pool #[2]) fun env => do
        let context := env.map (fun action => captureIO (liftM action))
        let saved ← IO.mkRef []
        for _ in [:2] do
          let .error error ← (SequentialReplay.interpret (journal saved) context 1000 (workflow backend) request).run
            | throw (IO.userError "Publication failure was swallowed")
          check (error == ⟨.application, "Publication failure"⟩) "Wrong publication error"
      check (!(← pending.atomically get)) "Publication fault was not exercised"

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
    check changed.changed.paths.isEmpty "Git index refresh became a parallel artifact"
    let final ← Bundle.delta source 10000 baseline
    check (final.changed.paths.contains ".lake/packages/dependency/.git/index") "Final workspace lost its Git index"
    IO.FS.writeFile (git / "HEAD") "different-commit"
    let rejected ← try
      discard <| Bundle.delta source 10000 baseline baseline
      pure false
    catch _ => pure true
    check rejected "A module changed the pinned Git revision"
    IO.FS.removeFile (source / "original")
    let difference ← Bundle.delta source 10000 baseline
    check (!(difference.retained.any (·.path == "original"))) "Final manifest retained a deleted file"
    check ((Bundle.mergeMany #[baseline, baseline]).toOption.map Array.size == some baseline.size)
      "Single-pass merging duplicated shared artifacts"
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
    check ((Bundle.mergeMany #[#[first], #[other]]).toOption.isNone) "Parallel artifact conflict accepted"

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
  let legacyRef ← Files.putText store (toJson files).pretty
  let cache := root / "workspace"
  let use := Workspace.use store (some cache) "build-a"
  use fun session => do
    let manifest ← session.readManifest ref
    discard <| session.readManifest legacyRef
    Bundle.synchronize store session.directory manifest 10000
    session.commit
  let offline := { store with read := fun _ => throw (IO.userError "Unnecessary blob read") }
  Workspace.use offline (some cache) "build-a" fun session => do
    let manifest ← session.readManifest ref
    discard <| session.readManifest legacyRef
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

private def parallelIOTests (store : ObjectStore) : IO Unit := do
  -- A rendezvous proves actual overlap, without relying on elapsed speedup.
  let counts ← Std.Mutex.new ((0, 0) : Nat × Nat)
  let values ← Parallel.map 3 (Array.range 12) fun i => do
    counts.atomically do modify fun (active, peak) => (active + 1, max peak (active + 1))
    try
      if i < 3 then
        let deadline := (← IO.monoMsNow) + 3000
        while (← counts.atomically get).2 < 3 do
          if (← IO.monoMsNow) > deadline then throw (IO.userError "IO tasks did not overlap")
          IO.sleep 1
      IO.sleep (12 - i).toUInt32
      return i * 2
    finally
      counts.atomically do modify fun (active, peak) => (active - 1, peak)
  check (values == (Array.range 12).map (· * 2) && (← counts.atomically get) == (0, 3))
    "Bounded IO lost ordering, exceeded its budget, or left tasks running"
  for _ in [:3] do
    counts.atomically (set (0, 0))
    let failed ← try
      discard <| Parallel.map 3 (Array.range 12) fun i => do
        counts.atomically do modify fun (active, peak) => (active + 1, max peak (active + 1))
        try
          if i < 3 then
            let deadline := (← IO.monoMsNow) + 3000
            while (← counts.atomically get).2 < 3 do
              if (← IO.monoMsNow) > deadline then throw (IO.userError "IO tasks did not overlap")
              IO.sleep 1
          if i == 0 then throw (IO.userError "Expected IO failure")
          IO.sleep 40
        finally
          counts.atomically do modify fun (active, peak) => (active - 1, peak)
      pure false
    catch _ => pure true
    check (failed && (← counts.atomically get) == (0, 3)) "Failure returned before IO tasks stopped"
  IO.FS.withTempDir fun root => do
    let traffic ← Std.Mutex.new ((0, 0) : Nat × Nat)
    let observe : {α : Type} → IO α → IO α := fun {_} action => do
      traffic.atomically do modify fun (active, peak) => (active + 1, max peak (active + 1))
      try IO.sleep 10; action
      finally traffic.atomically do modify fun (active, peak) => (active - 1, peak)
    let remote := { store with
      putContent := fun key bytes => observe (store.putContent key bytes)
      read := fun key => observe (store.read key) }
    let bounded ← remote.concurrent 3
    traffic.atomically (set (0, 0))
    discard <| Parallel.map 4 (Array.range 4) fun i =>
      Parallel.map 4 (Array.range 4) fun j => bounded.putBytes s!"{i}/{j}".toUTF8
    check ((← traffic.atomically get) == (0, 3)) "Nested upload pools escaped the shared transfer budget"
    let original := root / "original"
    let bytes := ByteArray.mk ((Array.range (Files.chunkSize * 3 + 19)).map fun i => (i % 251).toUInt8)
    IO.FS.writeBinFile original bytes
    let ref ← Files.upload remote original bytes.size 3
    let (_, peak) ← traffic.atomically get
    check (peak > 1 && peak ≤ 3) "File upload did not use bounded concurrent chunk transfers"
    traffic.atomically (set (0, 0))
    Files.download remote ref (root / "download") bytes.size 3
    let (_, peak) ← traffic.atomically get
    check (peak > 1 && peak ≤ 3 && (← IO.FS.readBinFile (root / "download")) == bytes)
      "Parallel download lost order or exceeded its budget"
    let source := root / "source"
    IO.FS.createDir source
    for i in [:30] do IO.FS.writeFile (source / s!"file-{i}") s!"content-{i}"
    let cache : Bundle.Cache := { directory := root / "cache", bytes := 10000 }
    let manifest ← (← Bundle.snapshot source 10000).publish remote (some cache) 3
    let packs := manifest.foldl (fun set entry => set.insert entry.file.pack.sha256) ({} : Std.HashSet String)
    check (packs.size == 3) "Publication did not distribute files across packs"
    -- Raising transfer concurrency must not turn one module into many tiny
    -- blob objects. Large chunks still overlap inside its single pack.
    let moduleSource := root / "module"
    IO.FS.createDir moduleSource
    IO.FS.writeBinFile (moduleSource / "large") bytes
    for i in [:16] do IO.FS.writeFile (moduleSource / s!"small-{i}") s!"content-{i}"
    let puts ← Std.Mutex.new (0 : Nat)
    let measured := { remote with putContent := fun key bytes => do
      puts.atomically (modify (· + 1))
      remote.putContent key bytes }
    traffic.atomically (set (0, 0))
    let packed ← (← Bundle.snapshot moduleSource (bytes.size + 10000)).publish measured none 3 (packCount := 1)
    let some entry := packed[0]? | throw (IO.userError "Missing packed module")
    check (packed.size == 17 && packed.all (·.file.pack == entry.file.pack))
      "Transfer concurrency fragmented module artifacts"
    check ((← puts.atomically get) == 5 && (← traffic.atomically get).2 > 1)
      "Single-pack publication lost parallel chunk IO or multiplied requests"
    -- Each first read waits for the other packs. Holding the cache lock over
    -- downloads would deadlock this rendezvous even with three restore tasks.
    let arrivals ← Std.Mutex.new (0 : Nat)
    let rendezvous := { store with read := fun key => do
      arrivals.atomically (modify (· + 1))
      let deadline := (← IO.monoMsNow) + 3000
      while (← arrivals.atomically get) < 3 do
        if (← IO.monoMsNow) > deadline then
          throw (IO.userError "Pack cache serialized independent downloads")
        IO.sleep 1
      store.read key }
    Bundle.restore rendezvous (root / "concurrent-downloads") manifest 10000
      (some { directory := root / "shared-cache", bytes := 10000 }) 3
    let some firstPack := manifest[0]? | throw (IO.userError "Missing parallel pack entry")
    let samePack := manifest.filter (·.file.pack == firstPack.file.pack)
    let reads ← Std.Mutex.new (0 : Nat)
    let counting := { store with read := fun key => do
      reads.atomically (modify (· + 1))
      IO.sleep 10
      store.read key }
    discard <| Parallel.map 3 (Array.range 3) fun i =>
      Bundle.restore counting (root / s!"shared-pack-{i}") samePack 10000
        (some { directory := root / "shared-pack-cache", bytes := 10000 })
    check ((← reads.atomically get) == 2)
      "Concurrent readers downloaded the same cached pack more than once"
    let offline := { store with read := fun _ => throw (IO.userError "Producer downloaded its own artifacts") }
    let restored := root / "restored"
    Bundle.restore offline restored manifest 10000 (some cache) 3
    traffic.atomically (set (0, 0))
    Bundle.restore remote (root / "cold") manifest 10000
      (some { directory := root / "cold-cache", bytes := 1 }) 3
    let (_, peak) ← traffic.atomically get
    check (peak > 1 && peak ≤ 3) "Separate artifact packs did not restore concurrently"
    check (← (root / "cold-cache").readDir).isEmpty "Concurrent restore exceeded the pack cache budget"
    for i in [:30] do
      check ((← IO.FS.readFile (restored / s!"file-{i}")) == s!"content-{i}") "Parallel restore changed content"
    Bundle.synchronize offline restored manifest 10000 (some cache) 3
    check (← Bundle.delta restored 10000 manifest manifest 3).changed.paths.isEmpty "Parallel delta changed clean inputs"
    IO.FS.writeFile (restored / "file-0") "altered input"
    let rejected ← try discard <| Bundle.delta restored 10000 manifest manifest 3; pure false catch _ => pure true
    check rejected "Parallel verification accepted changed prerequisites"
    Bundle.synchronize offline restored manifest 10000 (some cache) 3
    let some first := manifest[0]? | throw (IO.userError "Missing parallel pack entry")
    -- Large final manifests use the same bounded chunk upload as artifacts.
    let large := (Array.range 16000).map fun i => { first with path := s!"module-{i}/artifact" }
    traffic.atomically (set (0, 0))
    let reference ← Bundle.publishManifest remote large 3
    let (_, peak) ← traffic.atomically get
    check (reference.size > Files.chunkSize && peak > 1 && peak ≤ 3)
      "Final manifest chunks were not uploaded concurrently within budget"
    let recovered : Bundle.Manifest ← Files.readJson store reference
    check ((toJson recovered).compress == (toJson large).compress) "Parallel manifest upload changed its contents"
    let rejected ← try
      Bundle.restore store (root / "conflict") #[{ first with path := "a" }, { first with path := "a/b" }]
        10000 none 3
      pure false
    catch _ => pure true
    check rejected "Parallel restoration accepted overlapping output paths"
  IO.println "PASS bounded IO overlap, failure joins, parallel chunk transfers, producer cache, parallel artifact verification"

private def backendCacheTests (tools : Tools) (store : ObjectStore) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    let tools := { tools with threads := 2, cache := some { directory := root / "packs" } }
    let req := request
    let prepared ← tools.prepareDirectory store req directory "fixture"
    let some plan := prepared.plan | throw (IO.userError s!"Cache fixture preparation failed: {prepared.error}")
    let built ← withEnvironment store (pool #[2]) fun env => do
      -- Model a canonical result from another attempt whose manifest has the
      -- same files in a different order. Reuse bytes already built locally.
      let some names := env.blobs.names | throw (IO.userError "Missing named blobs")
      let names : BlobNames IO := { names with publish := fun name ref => do
        if name != Builders.resultName "Fixture.Base" then return ← names.publish name ref
        let result : BuildResult ← IO.ofExcept (Json.parse (← env.blobs.readText ref) >>= fromJson?)
        let some original := result.artifacts | throw (IO.userError "Missing Base artifacts")
        let manifest : Bundle.Manifest ← Files.readJson store original
        let repacked ← Files.putJson store manifest.reverse
        check (original != repacked) "Manifest variation was not exercised"
        let selected ← env.blobs.putText (toJson { result with artifacts := some repacked }).compress
        names.publish name selected }
      let env := { env with blobs := { env.blobs with names := some names } }
      Builders.seed env plan
      tools.builder store env req plan
      Builders.results env plan
    check (built.all (·.status == .built)) "Cache fixture build failed"
    let offline := { store with read := fun _ => throw (IO.userError "Redundant artifact download") }
    let finished ← tools.finish offline req plan built
    check (finished.status == .built) s!"Finish did not reuse local artifacts: {finished.message}"
    -- A repeated finish still runs Lake and publishes its final manifest, while
    -- reusing committed sources and module outputs from this worker's cache.
    let again ← tools.finish offline req plan built
    check (again.status == .built) s!"Repeated finish lost its cache: {again.message}"
    IO.println "PASS prepare/build producer cache and finish with all artifact downloads disabled"

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
  let store := objects (← Std.Mutex.new {})
  failedJobTests tools store fixture
  streamingPublicationTest tools store fixture
  bundleTests store
  packCacheTests store
  workspaceTests store
  parallelIOTests store
  backendCacheTests tools store fixture
  let built ← nativeTest tools store fixture (environment := pool #[2, 2])
  requireSuccess store built
  check (built.modules.size == 4 && built.build.status == .built) "Build report is incorrect"
  for result in built.modules do
    let some ref := result.artifacts | throw (IO.userError "Module artifacts missing")
    let entries : Bundle.Manifest ← Files.readJson store ref
    let some entry := entries[0]? | throw (IO.userError "Empty module artifacts")
    check (entries.all (·.file.pack == entry.file.pack))
      "Module publication split its artifacts into separate packs"
  let split ← nativeTest tools store fixture
  requireSuccess store split
  let [base, left, right, final] := split.modules.toList | throw (IO.userError "Missing split results")
  check (left.artifacts.isSome && left.artifacts != right.artifacts &&
    base.artifacts != left.artifacts && final.artifacts != left.artifacts)
    "Modules did not publish distinct artifact manifests"
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
        "  unless (← IO.getEnv \"LEAN_NUM_THREADS\") == some \"3\" do",
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
  check (left.artifacts.isSome && left.artifacts != right.artifacts && left.diagnostics != right.diagnostics)
    "Concurrent modules shared artifacts or diagnostics"
  IO.println "PASS independent module compilers overlap, use one CPU each, and publish separate artifacts"
  let defaults ← nativeTest tools store fixture (req := { request with targets := #[] })
  requireSuccess store defaults
  let reused ← nativeTest tools store fixture (req := { request with cache := .reuse, targets := #["+Fixture.Final:olean"] })
  requireSuccess store reused
  let cachedTarget ← nativeTest tools store fixture (fun d => do
    let result ← IO.Process.output {
      cmd := (tools.toolchain / "bin/lake").toString
      cwd := d, args := #["--no-cache", "build", "+Fixture.Final"] }
    check (result.exitCode == 0) "Cannot prepare cached build targets")
    { request with cache := .reuse, targets := #["+Fixture.Final:olean"] }
  requireSuccess store cachedTarget
  let qualified ← nativeTest tools store fixture (req := { request with targets := #["@build_fixture/Fixture"] })
  requireSuccess store qualified
  let oversized ← nativeTest tools store fixture (req := { request with limits := { request.limits with bytes := 1 } })
  check (!oversized.success && (oversized.message.splitOn "artifact byte limit").length > 1) "Oversized workspace accepted"
  let req := request
  let report ← nativeTest { tools with helper } store fixture (req := req)
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
    "Unrelated cached modules were reported as build targets"
  let some ref := report.build.artifacts | throw (IO.userError "No completed artifacts")
  let manifest : Bundle.Manifest ← Files.readJson store ref
  check (manifest.any (·.path.endsWith "Fixture/Final.olean")) "No final olean"
  IO.FS.withTempDir fun root => do
    Bundle.restore store root manifest req.limits.bytes
    IO.FS.writeFile (root / "Consumer.lean")
      "import Fixture.Final\nexample : Fixture.twice 1 + Fixture.twice 2 = 6 := Fixture.result\n"
    let imported ← IO.Process.output {
      cmd := (tools.toolchain / "bin/lake").toString
      cwd := root, args := #["--no-cache", "env", "lean", "Consumer.lean"] }
    check (imported.exitCode == 0) s!"Restored olean artifacts cannot be imported: {imported.stderr}"
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
  let changedInput ← try
    discard <| nativeTest tools store fixture (fun d => do
      IO.FS.writeFile (d / "prepared-input") "original"
      let code ← IO.FS.readFile (d / "Fixture/Base.lean")
      IO.FS.writeFile (d / "Fixture/Base.lean")
        ("import Lean\nrun_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile \"prepared-input\" \"changed\")\n" ++ code))
    pure false
  catch error => pure ((error.toString.splitOn "changed a prerequisite").length > 1)
  check changedInput "A builder silently changed prepared inputs"
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
  requireSuccess store sorryReport
  check (sorryReport.build.status == .built) "Lean's ordinary sorry warning was turned into a build failure"
  let bad ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nexample : False := True.intro\n")
  check (!bad.success && bad.modules.any (fun m => m.name == "Fixture.Final" && m.status == .blocked) &&
    bad.modules.any (fun m => m.name == "Fixture.Left" && m.status == .failed) &&
    bad.modules.any (fun m => m.name == "Fixture.Right" && m.status == .built))
    "Module failure blocked an independent module or lost the dependent failure"
  for version in ["4.34.1", "4.36.0"] do
    let mismatch ← nativeTest tools store fixture (fun d =>
      IO.FS.writeFile (d / "lean-toolchain") s!"leanprover/lean4:v{version}\n")
    check (!mismatch.success && mismatch.build.status == .failed) "Toolchain mismatch accepted"
  IO.println "PASS native Lake builds, executable/FFI/generated/custom targets, restored artifacts and build failures"

def main (args : List String) : IO Unit := do
  if args == ["--native-only"] then nativeTests; return
  builderSourceTest
  generatedTests
  if args.contains "--io" then parallelIOTests (objects (← Std.Mutex.new {}))
  if args.contains "--native" then nativeTests
