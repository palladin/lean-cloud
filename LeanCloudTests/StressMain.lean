import LeanCloudTests.Stress
import LeanCloudTests.PoolModel

def main (args : List String) : IO UInt32 := do
  let inputs ← match args with
    | [] => pure LeanCloudTests.StressWorkload.large
    | ["--smoke"] => pure LeanCloudTests.StressWorkload.smoke
    | _ => IO.eprintln "Usage: cloud_stress_tests [--smoke]"; return 1
  for input in inputs do
    IO.println (← LeanCloudTests.Stress.measure input).compress
  let start ← IO.monoMsNow
  let count := if args.isEmpty then 32 else 16
  LeanCloudTests.PoolModel.stress count
  IO.println (Lean.Json.mkObj [("poolRuns", Lean.toJson count),
    ("elapsedMs", Lean.toJson ((← IO.monoMsNow) - start))]).compress
  return 0
