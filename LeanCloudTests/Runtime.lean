import LeanCloudTests.Containers

namespace LeanCloudTests.Runtime
open Containers

def run (build : Bool) : IO Unit := withContext "test" fun ctx => do
  if build then
    discard <| ctx.compose #["build", "worker", "checks"] (timeout := 1800)
  discard <| ctx.compose #["up", "-d", "--wait", "broker", "blobs"] (timeout := 180)
  let checks ← ctx.compose #["run", "--rm", "--no-deps", "checks", configPath] (timeout := 300)
  say ((checks.stdout.trimAscii.toString.splitOn "\n").getLast!)
  discard <| ctx.compose #["run", "--rm", "--no-deps", "submit", "submit", configPath, "normal"]
  let scheduler ← ctx.createScheduler "scheduler" "normal"
  let workers ← (Array.range 3).mapM fun i => ctx.createWorker s!"normal-{i}" "normal"
  ctx.start workers
  ctx.waitAll workers
  ctx.checkReport "normal" "files=16, errors=24"
  let mut participants := 0
  for worker in workers do
    if ((← ctx.logs worker).splitOn "\n").any (fun line => (line.splitOn " location=").length > 1) then
      participants := participants + 1
  require (participants ≥ 2) s!"Expected multiple workers; observed {participants}"
  say s!"Parallel demo: {participants} worker containers processed locations."
  require (← ctx.crash scheduler) "Scheduler was not running"
  discard <| ctx.compose #["run", "--rm", "--no-deps", "checks", configPath, "mailbox-seed", "persistence"]
  discard <| ctx.compose #["kill", "-s", "SIGKILL", "broker"]
  discard <| ctx.compose #["restart", "blobs"]
  discard <| ctx.compose #["up", "-d", "--wait", "broker", "blobs"] (timeout := 180)
  discard <| ctx.compose #["run", "--rm", "--no-deps", "checks", configPath, "mailbox-check", "persistence"]
  ctx.start #[scheduler]
  ctx.checkReport "normal" "files=16, errors=24" (restartTimeout := 60)
  let fresh ← ctx.createWorker "fresh" "normal"
  ctx.start #[fresh]
  ctx.waitAll #[fresh]
  require (!((← ctx.logs fresh).splitOn "\n").any (fun line => (line.splitOn " location=").length > 1))
    "A fresh worker executed work for a completed run"
  say "Persistence: confirmed mail survived broker SIGKILL; scheduler state and blob results survived restart."
  say "All real runtime checks passed."

end LeanCloudTests.Runtime

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println "Usage: lake exe cloud_runtime_tests [--no-build]"
    return 0
  try
    let build ← match args with
      | [] => pure true
      | ["--no-build"] => pure false
      | _ => throw (IO.userError "Usage: lake exe cloud_runtime_tests [--no-build]")
    LeanCloudTests.Runtime.run build
    return 0
  catch error => IO.eprintln error.toString; return 1
