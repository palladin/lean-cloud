import LeanCloudRuntime.Monitoring
import LeanCloudRuntime.Application
import LeanCloudRuntime.Programs
import LeanCloudTests.Support

namespace MonitoringTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def step (index seq : Nat) : Observations.Step := {
  timestamp := toString (100000 + seq)
  event := ⟨"session", seq, seq, "worker1", some 0, (Location.root.child index).key, "execute", "work", "one", some "work"⟩
  branch := some (Location.root.child index) }

private def all (store : ObservationStore.Store) (run : String) : IO (Array Observations.Step) := do
  let mut after := none
  let mut items := #[]
  repeat
    let page ← store.page run after 17
    items := items ++ page.items
    match page.next with
    | none => return items
    | some key =>
      assertTrue (after.all (· < key)) "Non-advancing cursor"
      after := some key

private def http : IO Unit := do
  let inboxConn ← LeanLinq.Sqlite.connect ":memory:"
  let observationConn ← LeanLinq.Sqlite.connect ":memory:"
  try
    let store ← ObservationStore.create observationConn "scheduler"
    let observed := { step 0 1 with
      event := { (step 0 1).event with worker := "scheduler" }
      resources := some {
        incarnation := "boot", timeNs := 1000,
        nodeName := some "machine-1", hostname := some "scheduler-0", cpuCores := some 8,
        memoryCapacity := some 17179869184, cpuCapacityMillis := some 1500 }
      job := some { branch := Location.root, location := Location.root, joining := false, status := .done } }
    store.record observed
    let config : Config ← unwrap (Json.parse (include_str "../deploy/config.json") >>= fromJson?)
    let client : ClientConfig := ⟨"telemetry-test", "sha256:test", "client-token"⟩
    let handler : HttpMailbox.ServerHandler := {
      store := ← Inbox.create inboxConn, token := "internal-token", api := fun _ => pure Json.null
      client := some { token := client.token, api := fun json =>
        Application.deploymentApi programs config client (fun _ _ _ => pure ()) json (some store) }
      telemetry := some (Monitoring.api store) }
    let server ← (HttpServer.start (.v4 ⟨.ofParts 127 0 0 1, 0⟩) handler).block
    try
      let some (.v4 address) := server.localAddr | throw (IO.userError "Missing telemetry test address")
      let url := s!"http://127.0.0.1:{address.port}"
      -- The actual CLI client uses HTTP, parses the typed response, and knows
      -- neither node configuration nor the SQLite path.
      let received ← LeanCloudCli.withHostIO fun host => do
        let handle : {α : Type} → LeanCloudCli.HostOp α → IO (Except String α) := fun op =>
          match op with
          | .getEnv "TEST_TOKEN" => pure (.ok (some client.token))
          | op => host op
        IO.ofExcept (← LeanCloudCli.Cli.runWith handle do
          let connection ← LeanCloudCli.Client.connect url "TEST_TOKEN"
          LeanCloudCli.Client.call connection (.observations "one" "scheduler" none 17))
      assertTrue (received.items.any (·.job.isSome)) "Public API lost scheduler observations"
      assertTrue (received.items.any (fun item => item.resources.map toJson == observed.resources.map toJson))
        "SQLite/HTTP lost machine identity or capacity"
      let response ← LeanCloudCli.Http.post (url ++ "/telemetry") "internal-token" DeploymentApi.Request.nodes.encode.compress
      let node : DeploymentApi.Node ← unwrap ((← unwrap (Json.parse response >>= fromJson? (α := Except String Json))) >>= fromJson?)
      assertEq node.id "scheduler"
      let response ← LeanCloudCli.Http.post (url ++ "/telemetry") "internal-token"
        (DeploymentApi.Request.control "id" "one" .kill).encode.compress
      let result : Except String Json ← unwrap (Json.parse response >>= fromJson?)
      assertTrue (!result.isOk) "Diagnostic endpoint accepted a workflow command"
    finally server.shutdownAndWait.block
  finally inboxConn.close; observationConn.close

private def nativeResources : IO Unit := do
  -- Run on cgroup v2 Linux (including CI); unsupported hosts keep no sample.
  if !(← System.FilePath.pathExists "/sys/fs/cgroup/cgroup.controllers") then return
  let some sample ← Trace.resources | throw (IO.userError "Native resource sample could not be decoded")
  assertTrue (sample.hostname.any (!·.isEmpty)) "Missing container hostname"
  assertTrue (sample.cpuCores.getD 0 > 0 && sample.memoryCapacity.getD 0 > 0)
    "Missing host CPU/RAM capacity"
  assertTrue (sample.cpuCapacityMillis.getD 0 > 0) "Missing visible CPU capacity"
  if let some name ← IO.getEnv "CLOUD_NODE_NAME" then
    if !name.isEmpty && name.utf8ByteSize ≤ 255 then
      assertEq sample.nodeName (some name) "Native JSON changed the deployment-provided name"

def run : IO Unit := IO.FS.withTempFile fun _ path => do
  nativeResources
  let captured ← IO.mkRef (#[] : Array Observations.Step)
  let trace ← Trace.create "worker1" "parallel-source" (fun step => captured.modify (·.push step))
  let fork := Location.root.next
  trace.assign ⟨0, Location.root⟩
  let display : ParallelDisplay := ⟨1, ⟨"200/9,031 · 2%", "201/9,031 · 2%"⟩⟩
  trace.visit fork (some "parallel-site") (some display)
  let records := trace.records { read := fun _ => pure none, create := fun _ record => pure record }
  discard <| records.read (ReplayStore.returnKey (fork.child 0))
  trace.suspend fork
  trace.emit "idle" ""
  let retained := Observations.latest (← captured.get)
  assertTrue (retained.any fun step => step.keys.contains ("label/" ++ fork.key) &&
    step.event.operation == "200/9,031 · 2%" && step.parallel == some display)
    "Parallel labels or count were lost after suspension"
  assertTrue (retained.any fun step => step.keys.contains ("fork/" ++ fork.key) &&
    step.event.source == some "parallel-site" && step.event.location == fork.key)
    "Suspended parallel source was lost or attributed to a child return"
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let store ← ObservationStore.create conn "worker1"
    for observed in retained do store.record observed
    assertTrue ((← all store "parallel-source").any fun step =>
      step.event.activity == "parallel-label" && step.event.operation == "200/9,031 · 2%" &&
        step.parallel == some display)
      "SQLite observation storage lost the parallel labels or count"
    -- Rapid updates replace slots; they never grow an event history.
    for seq in [:3000] do store.record (step 0 seq)
    for index in [1:130] do store.record (step index 3000)
    store.record { step 0 4000 with event := { (step 0 4000).event with run := "other" } }
    for index in [:65] do
      store.record { step 129 (4000 + index) with resources := some {
        incarnation := "boot", timeNs := index * 250000000, memory := some index } }
    let rows ← all store "one"
    assertEq rows.size (130 * 2 + 30) "Observation storage grew with event count"
    let view := Observations.latest (Observations.merge #[] rows)
    assertTrue (view.all (·.event.run == "one")) "Run observations mixed"
    assertTrue (view.any fun s => s.branch == some (Location.root.child 0) && s.event.seq == 2999) "Latest source lost"
    assertTrue (!(view.any fun s => s.branch == some (Location.root.child 0) && s.event.seq < 2999)) "Historical events retained"
    let node ← store.node
    assertTrue (node.online && node.samples.isEmpty) "Missing counters were fabricated"
  finally conn.close
  -- Reopening a node, with no console cache or process state, retains its view.
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let store ← ObservationStore.create conn "worker1"
    assertEq (← all store "one").size 290
    assertEq (← all store "other").size 2
    store.remove "one"
    assertEq (← all store "one").size 0
    assertEq (← all store "other").size 2
    -- Diagnostics have a separate connection from the actor. Failure here may
    -- lose an observation but cannot throw out of the worker's recorder.
    conn.close
    store.record { step 0 9999 with event := { (step 0 9999).event with run := "other" } }
    store.flush
    assertTrue (!(← store.node).warning.isEmpty) "Telemetry storage failure was hidden"
  finally conn.close
  http
  IO.println "Bounded last views, paginated observations, isolation, reopen, and telemetry failures passed"

end MonitoringTests
