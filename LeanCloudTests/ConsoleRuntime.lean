import LeanCloudTests.ConsoleChaos

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

private def demo (f : Fixture) : IO Unit := do
  -- Exercise the installed executable's startup and persisted connection selection.
  let args := #[s!"LEAN_CLOUD_HOME={f.directory / "executable-client"}", ".lake/build/bin/lean_cloud"]
  discard <| external "env" (args ++ #["connect", "test", f.url, "--token-file", (f.directory / "client.token").toString])
  let catalog ← external "env" (args ++ #["programs"])
  assertTrue ((catalog.splitOn "sum-squares/v1").length > 1) "Executable did not restore HTTP connection"
  let before ← f.compose #["ps", "-q"]
  f.command ["run", "sum-squares", "--id", "first"]
  f.command ["run", "sum-squares", "--id", "second"]
  for id in ["first", "second"] do assertEq (← f.wait id) (.success (toJson (55 : Nat)))
  for args in [["programs"], ["ps"], ["status"], ["doctor"], ["inspect", "first"],
      ["watch", "first", "--once"], ["top", "--once"], ["logs", "first"], ["result", "first"]] do f.command args
  assertEq (← f.compose #["ps", "-q"]) before "Submission created or replaced containers"
  let token := (← IO.FS.readFile (f.directory / "client.token")).trimAscii.toString
  cli <| remoteClient (f.directory / "fresh-client") f.url token 4
  let run ← cli (f.context.loadRun "first")
  let timing ← cli ((·.timing) <$> f.context.observation run)
  f.helper "down"
  f.helper "up"
  -- Ephemeral localhost ports can change when a stopped node starts again.
  let address ← f.compose #["port", "scheduler", "8080"]
  let connection : Client.Connection := {
    url := "http://" ++ address
    deployment := f.context.project
    tokenEnv := "LEAN_CLOUD_TOKEN"
    tokenFile := some (f.directory / "client.token").toString }
  cli <| saveJson (f.context.home / "connection.json") connection
  assertEq (← f.wait "first") (.success (toJson (55 : Nat)))
  assertEq ((← cli ((·.timing) <$> f.context.observation run)).map (·.span)) (timing.map (·.span))
  f.command ["remove", "second"]
  assertTrue (!(← cli f.context.allRuns).any (·.id == "second")) "Removal left run in catalog"

private def controls (f : Fixture) : IO Unit := do
  let programs ← cli f.context.deployment
  let some program := programs.programs.find? (·.entry == "log-summary/v1") | throw (IO.userError "No log example")
  let some input := program.sampleInput | throw (IO.userError "No sample input")
  let file := f.directory / "input.json"
  IO.FS.writeFile file (input.setObjVal! "pauseMs" (toJson (3000 : Nat))).compress
  for id in ["paused", "killed"] do
    f.command ["run", "log-summary", "--input", file.toString, "--id", id]
    f.command [if id == "paused" then "pause" else "kill", id]
  assertTrue ((← cli (f.context.control "paused")) == .paused) "Pause not accepted"
  assertTrue (match ← f.wait "killed" with | .cancelled _ => true | _ => false) "Kill did not publish cancellation"
  f.command ["run", "sum-squares", "--id", "other"]
  assertEq (← f.wait "other") (.success (toJson (55 : Nat)))
  assertTrue (← cli (do f.context.outcome (← f.context.loadRun "paused"))).isNone "Paused run completed"
  f.command ["resume", "paused"]
  discard <| f.wait "paused"
  assertEq (← cli (do f.context.result (← f.context.loadRun "paused"))) "files=16, errors=24\n"

private def scaling (f : Fixture) : IO Unit := do
  f.helper "scale" #["0"]
  f.refresh
  f.command ["run", "sum-squares", "--id", "waiting"]
  assertTrue (← cli (do f.context.outcome (← f.context.loadRun "waiting"))).isNone "Zero-worker run completed"
  f.helper "scale" #["2"]
  let address ← f.compose #["port", "scheduler", "8080"]
  let connection : Client.Connection := {
    url := "http://" ++ address
    deployment := f.context.project
    tokenEnv := "LEAN_CLOUD_TOKEN"
    tokenFile := some (f.directory / "client.token").toString }
  cli <| saveJson (f.context.home / "connection.json") connection
  assertEq (← f.wait "waiting") (.success (toJson (55 : Nat)))
  f.helper "scale" #["1"]

end LeanCloudTests.ConsoleRuntime

open LeanCloudTests.ConsoleRuntime in
 def main (args : List String) : IO UInt32 := do
  try
    if let ["--remote", directory, url, tokenFile, count] := args then
      let some nodeCount := count.toNat? | throw (IO.userError "Expected node count")
      let token := (← IO.FS.readFile tokenFile).trimAscii.toString
      cli <| remoteClient directory url token nodeCount
      return 0
    let suite := args.headD "--pool-only"
    unless ["--pool-only", "--maintenance-only", "--scaling-only", "--chaos-only"].contains suite do
      throw (IO.userError "Use --pool-only, --maintenance-only, --scaling-only, --chaos-only, or --remote CLIENT_DIR URL TOKEN_FILE NODE_COUNT")
    let image := if suite == "--chaos-only" then "lean-cloud-chaos:test" else "lean-cloud-demo:test"
    withFixture (suite.drop 2 |>.toString) image fun f => do
      match suite with
      | "--pool-only" => demo f
      | "--maintenance-only" => controls f
      | "--scaling-only" => scaling f
      | "--chaos-only" => chaos f
      | _ => throw (IO.userError "Unknown runtime suite")
    IO.println s!"{suite} passed"
    return 0
  catch error => IO.eprintln error; return 1
