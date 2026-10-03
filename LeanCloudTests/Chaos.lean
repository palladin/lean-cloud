import LeanCloudTests.Containers

namespace LeanCloudTests.Chaos
open Lean Containers

structure Options where
  seed : Nat := 1
  crashes : Nat := 8
  workers : Nat := 3
  timeout : Nat := 120
  build : Bool := true
  deriving ToJson

private def number (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some value => .ok value
  | none => .error s!"{flag} requires a natural number"

def parse (options : Options) : List String → Except String Options
  | [] => do
    unless options.crashes > 0 && options.workers > 0 && options.timeout > 0 do
      throw "crashes, workers, and timeout must be positive"
    return options
  | "--no-build" :: rest => parse { options with build := false } rest
  | "--seed" :: value :: rest => do parse { options with seed := ← number "--seed" value } rest
  | "--crashes" :: value :: rest => do parse { options with crashes := ← number "--crashes" value } rest
  | "--workers" :: value :: rest => do parse { options with workers := ← number "--workers" value } rest
  | "--timeout" :: value :: rest => do parse { options with timeout := ← number "--timeout" value } rest
  | arg :: _ => throw s!"Unknown or incomplete option: {arg}"

structure Fault where
  worker : Nat
  delayMs : Nat
  deriving ToJson, BEq, Inhabited

/-- A fixed generator produces the whole injection plan before any worker runs.
The seed reproduces this plan, not real concurrent timing. -/
def plan (options : Options) : Array Fault := Id.run do
  let mut seed := options.seed
  let mut faults := #[]
  for _ in [:options.crashes] do
    seed := (1664525 * seed + 1013904223) % 4294967296
    let worker := (seed / 65536) % (options.workers + 1)
    seed := (1664525 * seed + 1013904223) % 4294967296
    faults := faults.push ⟨worker, 100 + (seed / 65536) % 601⟩
  return faults

def run (options : Options) : IO Unit := withContext s!"chaos-{options.seed}" fun ctx => do
  let faults := plan options
  IO.FS.writeFile (ctx.artifacts / "plan.json") (Json.mkObj [
    ("generator", toJson "lcg32/v1"), ("options", toJson options), ("plan", toJson faults)]).pretty
  let input := Json.mkObj [
    ("files", toJson ((Array.range 16).map fun i => s!"demo/log-{i}.txt")),
    ("batchSize", toJson (1 : Nat)), ("pauseMs", toJson (1500 : Nat))]
  let inputFile := ctx.artifacts / "input.json"
  IO.FS.writeFile inputFile input.compress
  if options.build then
    discard <| ctx.compose #["build", "worker"] (timeout := 1800)
  discard <| ctx.compose #["up", "-d", "--wait", "broker", "blobs"] (timeout := 180)
  -- Seed global blobs through the ordinary application submission command.
  discard <| ctx.compose #["run", "--rm", "--no-deps", "submit", "submit", configPath, "seed-files"]
  discard <| ctx.compose #["run", "--rm", "--no-deps", "-v", s!"{inputFile}:/input.json:ro",
    "submit", "submit", configPath, "chaos", "/input.json"]
  let scheduler ← ctx.createScheduler "scheduler" "chaos"
  let workers ← (Array.range options.workers).mapM fun i => ctx.createWorker s!"worker-{i}" "chaos"
  ctx.start workers
  ctx.event "started" [("seed", toJson options.seed), ("workers", toJson options.workers)]
  let mut killed := 0
  for index in [:faults.size] do
    let fault := faults[index]!
    IO.sleep fault.delayMs.toUInt32
    let worker := if fault.worker == options.workers then scheduler else workers[fault.worker]!
    if ← ctx.crash worker then
      killed := killed + 1
      ctx.event "crashed" [("index", toJson index), ("worker", toJson worker), ("exitCode", toJson (137 : Nat))]
      ctx.start #[worker]
      ctx.event "restarted" [("worker", toJson worker)]
    else
      ctx.event "already_finished" [("index", toJson index), ("worker", toJson worker)]
  require (killed > 0) "No actor was crashed; this run did not exercise recovery"
  ctx.event "faults_stopped" [("crashes", toJson killed)]
  ctx.waitAll workers options.timeout
  ctx.checkReport "chaos" "files=16, errors=24"
  let fresh ← ctx.compose #["run", "--rm", "--no-deps", "worker", "worker", configPath, "chaos"]
  require ((fresh.stdout.splitOn "\n").contains "completed chaos" &&
    !(fresh.stdout.splitOn "\n").any (fun line => (line.splitOn " location=").length > 1))
    "A fresh worker must read the saved outcome without processing new work"
  ctx.event "passed" [("crashes", toJson killed), ("report", toJson "files=16, errors=24")]

end LeanCloudTests.Chaos

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println "Usage: lake exe cloud_chaos [--seed N] [--crashes N] [--workers N] [--timeout SECONDS] [--no-build]"
    return 0
  try
    LeanCloudTests.Chaos.run (← IO.ofExcept (LeanCloudTests.Chaos.parse {} args))
    return 0
  catch error => IO.eprintln error.toString; return 1
