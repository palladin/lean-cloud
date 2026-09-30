import LeanCloudTests.Containers

namespace LeanCloudTests.Runtime
open Containers

def run (build : Bool) : IO Unit := withContext "test" fun ctx => do
  if build then
    discard <| ctx.compose #["build", "worker"] (timeout := 1800)
    discard <| ctx.compose #["build", "checks"] (timeout := 1800)
  discard <| ctx.compose #["up", "-d", "--wait", "db", "queue", "blobs"] (timeout := 180)
  let checks ← ctx.compose #["run", "--rm", "--no-deps", "checks", configPath, "properties"] (timeout := 180)
  say ((checks.stdout.trimAscii.toString.splitOn "\n").getLast!)

  discard <| ctx.compose #["run", "--rm", "--no-deps", "submit", "submit", configPath, "normal"]
  let workers ← (Array.range 3).mapM fun i => ctx.createWorker s!"normal-{i}" "normal"
  ctx.start workers
  ctx.waitAll workers
  ctx.checkReport "normal" "files=16, errors=24"
  let mut participants := 0
  for worker in workers do
    if ((← ctx.logs worker).splitOn "\n").any (·.startsWith "work ") then
      participants := participants + 1
  require (participants ≥ 2) s!"Expected multiple workers to process locations; observed {participants}"
  say s!"Parallel demo: {participants} worker containers processed locations."

  discard <| ctx.compose #["run", "--rm", "--no-deps", "-v",
    s!"{ctx.root / "deploy/recovery-input.json"}:/input.json:ro",
    "submit", "submit", configPath, "recovery", "/input.json"]
  let victim ← ctx.createWorker "interrupted" "recovery"
  ctx.start #[victim]
  let deadline := (← IO.monoMsNow) + 10000
  repeat
    if ((← ctx.logs victim).splitOn "\n").contains "work 0:0/0:4" then break
    require ((← IO.monoMsNow) < deadline) "Worker did not reach the expected exec location"
    checkExit victim (← ctx.status victim)
    IO.sleep 100
  require (← ctx.crash victim) "Worker finished before the targeted crash"
  let replacements ← (Array.range 2).mapM fun i => ctx.createWorker s!"recovery-{i}" "recovery"
  ctx.start replacements
  ctx.waitAll replacements
  ctx.checkReport "recovery" "files=4, errors=6"
  say "Recovery demo: killed a worker during exec; replacement workers completed the run."

  discard <| ctx.compose #["restart", "db", "queue", "blobs"]
  discard <| ctx.compose #["up", "-d", "--wait", "db", "queue", "blobs"] (timeout := 180)
  ctx.checkReport "normal" "files=16, errors=24" (restartTimeout := 60)
  ctx.checkReport "recovery" "files=4, errors=6" (restartTimeout := 60)
  say "Persistence: both reports survived restarting all three services."
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
