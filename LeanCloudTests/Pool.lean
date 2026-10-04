import LeanCloud.Pool
import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

private def change (state : Pool.State) (cmd : Pool.Command) : IO Pool.State := do
  return (← unwrap (Pool.command state cmd)).1

private def takeJob (state : Pool.State) (worker : String) : IO (Pool.State × String × Assignment) := do
  let (next, reply) := Pool.acquire 100 state worker
  match reply with
  | .execute run assignment => return (next, run, assignment)
  | _ => throw (IO.userError "Expected a pool assignment")

private def initial : Pool.State := { runs := #[⟨"first", .active, {}⟩, ⟨"second", .active, {}⟩] }

def poolCases : Array TestCase := #[
  ⟨"pool.shared-workers-route-and-rotate", do
    let (state, run, first) ← takeJob initial "worker1"
    assertEq run "first"
    let (again, run, duplicate) ← takeJob state "worker1"
    assertEq run "first"
    assertEq duplicate first
    assertEq (toJson again).compress (toJson state).compress
    let (state, run, second) ← takeJob state "worker2"
    assertEq run "second"
    -- Attempt numbers are local to each run. Routing must include its run ID.
    assertEq first.attempt second.attempt
    let state := Pool.report state "first" ⟨"worker1", first.attempt, .ok .done, #[]⟩
    assertTrue (state.runs[0]?.any (·.scheduler.finished)) "First run did not complete"
    assertTrue (state.runs[1]?.all (!·.scheduler.finished)) "Report crossed run namespaces"
    assertTrue (Pool.valid state "second" "worker2" second.attempt) "Unrelated assignment was revoked"⟩,
  ⟨"pool.pause-revokes-only-one-run", do
    let (state, _, first) ← takeJob initial "worker1"
    let (state, _, second) ← takeJob state "worker2"
    let state ← change state (.pause "first")
    assertTrue (!Pool.valid state "first" "worker1" first.attempt) "Paused assignment still valid"
    assertTrue (Pool.valid state "second" "worker2" second.attempt) "Pause crossed runs"
    let stale := Pool.report state "first" ⟨"worker1", first.attempt, .ok .done, #[]⟩
    assertEq (toJson stale).compress (toJson state).compress
    let restored := Pool.recover state
    assertTrue (restored.runs[0]?.any (·.mode == .paused)) "Restart lost pause"
    let state ← change state (.resume "first")
    let (state, run, retry) ← takeJob state "worker1"
    assertEq run "first"
    assertTrue (retry.attempt > first.attempt) "Resume reused a revoked attempt"
    let stale := Pool.report state "first" ⟨"worker1", first.attempt, .ok .done, #[]⟩
    assertTrue (stale.runs[0]?.all (!·.scheduler.finished)) "Stale report completed resumed run"⟩,
  ⟨"pool.kill-is-terminal-and-submission-is-idempotent", do
    let state ← change initial (.kill "first")
    let duplicate ← change state (.submit "first")
    assertEq (toJson state).compress (toJson duplicate).compress
    assertTrue (Pool.command state (.resume "first")).toOption.isNone "Killed run resumed"
    let (_, run, _) ← takeJob state "worker1"
    assertEq run "second"
    assertTrue (Pool.command state (.pause "missing")).toOption.isNone "Unknown run accepted"
    let sealed ← change state (.kill "unsubmitted")
    let registered ← change sealed (.submit "unsubmitted")
    assertTrue (Pool.command registered (.resume "unsubmitted")).toOption.isNone "Late submission undid cancellation"⟩,
  ⟨"pool.crash-recovery-fences-outstanding-assignments", do
    let (state, _, first) ← takeJob initial "worker1"
    let (state, _, second) ← takeJob state "worker2"
    let recovered := Pool.recover state
    assertTrue (!Pool.valid recovered "first" "worker1" first.attempt) "Old attempt survived restart"
    assertTrue (!Pool.valid recovered "second" "worker2" second.attempt) "Old attempt survived restart"
    let (state, _, retry) ← takeJob recovered "worker2"
    assertTrue (retry.attempt > first.attempt) "Restart reused attempt number"
    let encoded := (toJson state).compress
    let restored : Pool.State ← unwrap (Json.parse encoded >>= fromJson?)
    assertEq (toJson restored).compress encoded⟩,
  ⟨"pool.expiry-and-fair-run-selection", do
    let (state, _, first) ← takeJob initial "worker1"
    let expired := Pool.tick 100 state
    assertTrue (!Pool.valid expired "first" "worker1" first.attempt) "Expired assignment still valid"
    let (state, run, _) ← takeJob expired "worker1"
    assertEq run "second"
    let (_, run, _) ← takeJob state "worker2"
    assertEq run "first"⟩,
  ⟨"pool.interleaved-forks-join-without-crossing-runs", do
    for seed in [:24] do
      let mut state := initial
      let mut children : Array (String × Assignment) := #[]
      for worker in ["worker1", "worker2"] do
        let (next, run, job) ← takeJob state worker
        state := Pool.report next run ⟨worker, job.attempt, .ok (.fork Location.root 2), #[]⟩
      for index in [:4] do
        let worker := s!"w{index}"
        let (next, run, job) ← takeJob state worker
        state := next
        children := children.push (run, job)
      let mut pending := Array.range 4
      let mut permutation := seed
      for _ in [:4] do
        let chosen := permutation % pending.size
        permutation := permutation / pending.size
        let some index := pending[chosen]? | throw (IO.userError "Missing permutation")
        pending := pending.extract 0 chosen ++ pending.extract (chosen + 1) pending.size
        let some (run, job) := children[index]? | throw (IO.userError "Missing child")
        state := Pool.report state run ⟨s!"w{index}", job.attempt, .ok .done, #[]⟩
        -- Redelivery must not double-count a child or change another run.
        state := Pool.report state run ⟨s!"w{index}", job.attempt, .ok .done, #[]⟩
      for worker in ["worker1", "worker2"] do
        let (next, run, job) ← takeJob state worker
        assertTrue job.joining "Parent resumed before collecting children"
        state := Pool.report next run ⟨worker, job.attempt, .ok .done, #[]⟩
      assertTrue (state.runs.all (·.scheduler.finished)) "A run lost its completion"⟩
]
end LeanCloudTests
