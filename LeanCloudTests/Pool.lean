import LeanCloud.Pool
import LeanCloudTests.Support
import LeanCloudTests.Generated

namespace LeanCloudTests
open Lean LeanCloud

private def change (state : Pool.State) (cmd : Pool.Command) : IO Pool.State := do
  return (← unwrap (Pool.command state cmd)).1

private def takeJob (state : Pool.State) (worker : String) : IO (Pool.State × String × Assignment) := do
  let (next, reply) := Pool.acquire 100 state worker
  match reply with
  | .execute run assignment => return (next, run, assignment)
  | _ => throw (IO.userError "Expected a pool assignment")

/-- Test actors explicitly stop before acknowledging cancellation. No timeout
or ordinary readiness message is treated as proof of termination. -/
private def stopOld (state : Pool.State) : Pool.State :=
  state.runs.foldl (fun state run => run.scheduler.stopping.foldl
    (fun state worker => Pool.stopped state run.id worker run.scheduler.barrier) state) state

private def initial : Pool.State := { runs := #[{ id := "first" }, { id := "second" }] }

def poolCases : Array TestCase := #[
  ⟨"pool.catalog-recovery-remembers-terminal-writer", do
    let state ← change {} (.kill "cancelled")
    let (state, reply) := Pool.acquire 100 state "old-worker"
    let .finalize id attempt _ := reply | throw (IO.userError "Missing terminal assignment")
    let catalog : Pool.Catalog ← unwrap (Json.parse (toJson state.catalog).compress >>= fromJson?)
    let recovered := Pool.recover catalog.restore
    let (_, reply) := Pool.acquire 100 recovered "replacement"
    assertEq (toJson reply) (toJson Pool.Reply.idle)
      "Catalog recovery forgot an active terminal writer"
    let some run := recovered.runs[0]? | throw (IO.userError "Missing restored run")
    assertTrue (run.scheduler.stopping.contains "old-worker") "Terminal owner was not cancelled"
    let ready := Pool.stopped recovered id "old-worker" run.scheduler.barrier
    let (_, reply) := Pool.acquire 100 ready "replacement"
    let .finalize nextId nextAttempt _ := reply | throw (IO.userError "Finalization did not resume")
    assertEq nextId id
    assertTrue (nextAttempt > attempt) "Finalization reused the old attempt"⟩,
  ⟨"pool.cancellation-awaits-every-owner-and-restarts-at-root", do
    let state ← change {} (.submit "nested")
    let (state, id, root) ← takeJob state "a"
    let state := Pool.report state id ⟨"a", root.attempt, .ok (.fork Location.root.next 2), #[]⟩
    let (state, _, left) ← takeJob state "a"
    let (state, _, right) ← takeJob state "b"
    let stopped ← change (← change state (.pause id)) (.resume id)
    let some run := stopped.runs[0]? | throw (IO.userError "Missing run")
    let barrier := run.scheduler.barrier
    let (_, reply) := Pool.acquire 100 stopped "a"
    assertEq (toJson reply) (toJson (Pool.Reply.cancel id barrier))
    let half := Pool.stopped stopped id "a" barrier
    let (_, waiting) := Pool.acquire 100 half "replacement"
    assertEq (toJson waiting) (toJson Pool.Reply.idle) "One stop acknowledgement released the whole batch"
    let stale := Pool.stopped half id "b" (barrier + 1)
    assertEq (toJson stale) (toJson half)
    let ready := Pool.stopped half id "b" barrier
    let (ready, _, root) ← takeJob ready "replacement"
    assertEq root.branchStart Location.root "Resume restored a saved child instead of reconstructing the root"
    assertTrue (root.attempt > right.attempt) "Restart reused an old attempt"
    let late := Pool.report ready id ⟨"a", left.attempt, .ok .done, #[]⟩
    assertTrue (Pool.valid late id "replacement" root.attempt) "Late reply satisfied a replacement ticket"
    assertTrue (late.runs[0]?.all (!·.scheduler.finished)) "Late child reply completed the root"⟩,
  ⟨"pool.terminal-publication-retries-after-worker-and-scheduler-crash", do
    let state ← change {} (.submit "cancelled")
    let state ← change state (.configureWorkers #[])
    let state ← change state (.kill "cancelled")
    assertEq (state.runs[0]?.map (·.finalization)) (some .pending)
    let (_, reply) := Pool.acquire 100 state "worker1"
    assertTrue (match reply with | .drain _ => true | _ => false) "Zero-worker pool assigned a finalizer"
    let state ← change state (.configureWorkers #["worker1", "worker2"])
    let (state, reply) := Pool.acquire 100 state "worker1"
    let .finalize id first outcome := reply | throw (IO.userError "Missing finalizer")
    let (duplicateState, duplicate) := Pool.acquire 100 state "worker1"
    assertEq (toJson duplicateState) (toJson state)
    assertEq (toJson duplicate) (toJson reply)
    let renewed := Pool.renew 100 (Pool.tick 50 state) id "worker1" first
    assertTrue (Pool.valid (Pool.tick 75 renewed) id "worker1" first) "Finalizer renewal was ignored"
    let expired := Pool.tick 100 state
    let (state, replacement) := Pool.acquire 100 (stopOld expired) "worker2"
    let .finalize _ second _ := replacement | throw (IO.userError "Expired finalizer was not retried")
    assertTrue (second > first) "Finalizer reused an expired attempt"
    assertEq (toJson (Pool.report state id ⟨"worker1", first, .ok .done, #[]⟩)) (toJson state)
    let (report, world) ← unwrap (evaluate 10000
      (Worker.finalize "worker2" (SimulationBackend.observed "worker2") second outcome) ({} : SimulationBackend.World))
    assertTrue (report.recorded.contains (ReplayStore.returnKey Location.root)) "Report omitted the durable root record"
    -- Publication survived; the report was lost and the scheduler restarted.
    let recovered := Pool.recover state
    assertTrue (!Pool.valid recovered id "worker2" second) "Restart retained finalization ownership"
    let (state, retry) := Pool.acquire 100 (stopOld recovered) "worker1"
    let .finalize _ third _ := retry | throw (IO.userError "Restart lost terminal intent")
    assertTrue (third > second) "Restart reused finalization attempt"
    let (report, after) ← unwrap (evaluate 10000
      (Worker.finalize "worker1" (SimulationBackend.observed "worker1") third outcome) world)
    assertEq after.records world.records "Retry overwrote the durable outcome"
    let finished := Pool.report state id report
    assertEq (finished.runs[0]?.map (·.finalization)) (some .done)
    assertEq (toJson (Pool.acquire 100 finished "worker1").2) (toJson Pool.Reply.idle)⟩,
  ⟨"pool.legacy-run-defaults-to-pending-finalization", do
    let catalog : Pool.RunCatalog ← unwrap (fromJson? (Json.mkObj [
      ("id", toJson "old"), ("mode", toJson Pool.Mode.killed),
      ("scheduler", toJson ({} : Scheduler.State))]))
    let some run := ({ runs := #[catalog] } : Pool.Catalog).restore.runs[0]?
      | throw (IO.userError "Missing restored run")
    assertEq run.finalization Scheduler.Status.pending
    let (_, reply) := Pool.acquire 100 { runs := #[run] } "worker1"
    assertTrue (match reply with | .finalize .. => true | _ => false) "Saved terminal intent was lost"⟩,
  ⟨"pool.failure-in-child-revokes-siblings-and-survives-recovery", do
    let source := lower (.parallel [.value 7, .value 9]) (m := SimM SimulationBackend.World)
    let runJob (world : SimulationBackend.World) (worker : String) (fuel : Nat) (job : Assignment) :=
      unwrap (evaluate 10000 (Worker.execute worker (SimulationBackend.observed worker)
        SimulationBackend.blobs fuel source 0 job) world)
    let state ← change {} (.submit "failed")
    let (state, id, root) ← takeJob state "worker1"
    let (fork, world) ← runJob {} "worker1" 1000 root
    let state := Pool.report state id fork
    let (state, _, left) ← takeJob state "worker1"
    let (state, _, right) ← takeJob state "worker2"
    let (failure, _) ← runJob world "worker1" 0 left
    let .error error := failure.progress | throw (IO.userError "Expected interpreter fuel exhaustion")
    let state := Pool.report state id failure
    assertEq (state.runs[0]?.bind Pool.Run.terminalOutcome) (some (.failure error))
    assertTrue (!Pool.valid state id "worker1" left.attempt && !Pool.valid state id "worker2" right.attempt)
      "Failed run retained an active sibling"
    assertTrue (state.runs[0]?.all fun run => run.scheduler.jobs.all fun job =>
      match job.status with | .running .. => false | _ => true) "Failed run displays running jobs"
    for report in [failure, ⟨"worker2", right.attempt, .ok .done, #[]⟩,
        ⟨"worker2", right.attempt, .error ⟨.protocol, "Later failure"⟩, #[]⟩] do
      assertEq (toJson (Pool.report state id report)) (toJson state)
    let saved := (← unwrap (Json.parse (toJson state.catalog).compress >>= fromJson? (α := Pool.Catalog))).restore
    let recovered := Pool.recover saved
    assertEq (recovered.runs[0]?.bind Pool.Run.terminalOutcome) (some (.failure error))
    assertTrue (Pool.command recovered (.resume id)).toOption.isNone "Failure resumed"
    assertTrue (Pool.command recovered (.pause id)).toOption.isNone "Failure became paused"
    let killed ← change recovered (.kill id)
    assertEq (killed.runs[0]?.bind Pool.Run.terminalOutcome) (some (.failure error))
    let (sealing, reply) := Pool.acquire 100 (stopOld recovered) "worker1"
    let .finalize failed attempt outcome := reply | throw (IO.userError "Missing terminal assignment")
    assertEq failed id
    assertEq outcome (.failure error)
    let (report, world) ← unwrap (evaluate 10000
      (Worker.finalize "worker1" (SimulationBackend.observed "worker1") attempt outcome) world)
    assertEq ((world.records.lookup (ReplayStore.returnKey Location.root)).map (·.outcome)) (some outcome)
    let recovered := Pool.report sealing id report
    assertEq (recovered.runs[0]?.map (·.finalization)) (some .done)
    let next ← change recovered (.submit "healthy")
    let (next, other, job) ← takeJob next "worker1"
    assertEq other "healthy"
    assertTrue (Pool.valid next other "worker1" job.attempt) "Failure prevented another run from using the worker"
    assertEq (toJson next.runs[0]?) (toJson recovered.runs[0]?)⟩,
  ⟨"pool.stale-failure-cannot-terminate-replacement-or-killed-run", do
    let (state, id, old) ← takeJob initial "worker1"
    let resumed ← change (stopOld (← change state (.pause id))) (.resume id)
    let (resumed, _, _) ← takeJob resumed "worker2"
    let (resumed, replacementRun, current) ← takeJob resumed "worker1"
    assertEq replacementRun id
    assertTrue (current.attempt > old.attempt) "Expected a replacement attempt"
    let stale : Report := ⟨"worker1", old.attempt, .error ⟨.protocol, "Stale failure"⟩, #[]⟩
    -- Stale reports may add observation hints; they must not install a failure.
    let after := Pool.report resumed id stale
    assertTrue (after.runs.all (·.scheduler.error.isNone)) "Stale attempt installed a failure"
    assertTrue (Pool.valid after id "worker1" current.attempt) "Stale failure revoked replacement work"
    let killed ← change state (.kill id)
    assertEq (toJson (Pool.report killed id stale)) (toJson killed)
    assertEq (killed.runs[0]?.bind Pool.Run.terminalOutcome) (some (.cancelled "Killed by user"))⟩,
  ⟨"pool.legacy-state-defaults-to-unconfigured-membership", do
    let catalog : Pool.Catalog ← unwrap (fromJson? (Json.mkObj [
      ("runs", toJson initial.runs), ("cursor", toJson initial.cursor)]))
    let state := catalog.restore
    assertTrue state.membership.active.isNone "Legacy state acquired an empty pool"
    discard (takeJob state "worker1")⟩,
  ⟨"pool.elastic-drain-preserves-running-work", do
    let state ← change initial (.configureWorkers #["worker1", "worker2"])
    let (state, id, job) ← takeJob state "worker2"
    let smaller ← change state (.configureWorkers #["worker1"])
    assertTrue (Pool.valid smaller id "worker2" job.attempt) "Scale-down revoked an executing assignment"
    let (_, reply) := Pool.acquire 100 smaller "worker2"
    let .drain generation := reply | throw (IO.userError "Retiring worker got more work")
    let finished := Pool.report smaller id ⟨"worker2", job.attempt, .ok .done, #[]⟩
    assertTrue (finished.runs.any (fun run => run.id == id && run.scheduler.finished)) "Drain lost current result"
    let retired := Pool.drained finished "worker2" generation
    assertTrue (retired.membership.drained.contains "worker2") "Drain acknowledgement lost"
    assertEq (toJson (Pool.drained retired "worker2" generation)).compress (toJson retired).compress
    let restored := (← unwrap (fromJson? (α := Pool.Catalog) (toJson (Pool.recover retired).catalog))).restore
    assertTrue (restored.membership.drained.contains "worker2") "Restart forgot retired worker"⟩,
  ⟨"pool.elastic-stale-drain-cannot-retire-rejoined-worker", do
    let old ← change initial (.configureWorkers #["worker1"])
    let generation := old.membership.generation
    let joined ← change old (.configureWorkers #["worker1", "worker2"])
    let (joined, id, job) ← takeJob joined "worker2"
    let stale := Pool.drained joined "worker2" generation
    assertEq (toJson stale).compress (toJson joined).compress
    assertTrue (Pool.valid stale id "worker2" job.attempt) "Stale acknowledgement revoked new work"
    let smaller ← change stale (.configureWorkers #["worker1"])
    let stale := Pool.drained smaller "worker2" generation
    assertTrue (!stale.membership.drained.contains "worker2") "Old generation acknowledged a later drain"
    assertTrue (Pool.valid stale id "worker2" job.attempt) "Old drain fenced active computation"⟩,
  ⟨"pool.elastic-zero-retry-and-stopped-worker", do
    let (busy, id, job) ← takeJob initial "worker1"
    let empty ← change busy (.configureWorkers #[])
    let retry ← change empty (.configureWorkers #[])
    assertEq retry.membership.generation empty.membership.generation
    let stopped ← change retry (.workerStopped "worker1" retry.membership.generation)
    assertTrue (!Pool.valid stopped id "worker1" job.attempt) "Stopped worker retained an assignment"
    let joined ← change stopped (.configureWorkers #["worker2"])
    assertTrue (joined.membership.drained.contains "worker1") "Another resize forgot stopped worker"
    let (joined, _, _) ← takeJob joined "worker2"
    let (_, reply) := Pool.acquire 100 joined "worker1"
    assertTrue (match reply with | .drain _ => true | _ => false) "Retired worker reacquired work"⟩,
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
    let state ← change (stopOld state) (.resume "first")
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
    let (state, reply) := Pool.acquire 100 state "worker1"
    let .finalize id attempt outcome := reply | throw (IO.userError "Missing cancellation assignment")
    assertEq id "first"
    assertEq outcome (.cancelled "Killed by user")
    let state := Pool.report state id ⟨"worker1", attempt, .ok .done, #[]⟩
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
    let (state, _, retry) ← takeJob (stopOld recovered) "worker2"
    assertTrue (retry.attempt > first.attempt) "Restart reused attempt number"
    let encoded := (toJson state.catalog).compress
    let restored := (← unwrap (Json.parse encoded >>= fromJson? (α := Pool.Catalog))).restore
    assertEq (toJson restored.catalog).compress encoded
    assertTrue (restored.runs.all (·.scheduler.pending.isEmpty)) "Catalog restored live tickets"⟩,
  ⟨"pool.expiry-and-fair-run-selection", do
    let (state, _, first) ← takeJob initial "worker1"
    let expired := Pool.tick 100 state
    assertTrue (!Pool.valid expired "first" "worker1" first.attempt) "Expired assignment still valid"
    let (state, run, _) ← takeJob (stopOld expired) "worker1"
    assertEq run "second"
    let (_, run, _) ← takeJob state "worker2"
    assertEq run "first"⟩,
  ⟨"pool.heartbeats-renew-only-the-current-attempt", do
    let (state, id, job) ← takeJob initial "worker1"
    let (state, other, second) ← takeJob state "worker2"
    let state := Pool.tick 50 state
    -- The run, worker, and attempt all matter: attempt numbers repeat across runs.
    for (run, worker, attempt) in [(other, "worker1", job.attempt),
        (id, "worker2", job.attempt), (id, "worker1", job.attempt + 1)] do
      assertEq (toJson (Pool.renew 100 state run worker attempt)) (toJson state)
    let renewed := Pool.renew 100 state id "worker1" job.attempt
    assertEq (toJson (Pool.renew 100 renewed id "worker1" job.attempt)) (toJson renewed)
    let elapsed := Pool.tick 75 renewed
    assertTrue (Pool.valid elapsed id "worker1" job.attempt) "Busy worker lost its renewed lease"
    assertTrue (!Pool.valid elapsed other "worker2" second.attempt) "Renewal crossed run namespaces"
    let expired := Pool.tick 25 elapsed
    assertEq (toJson (Pool.renew 100 expired id "worker1" job.attempt)) (toJson expired)
    for revoked in [Pool.recover renewed, ← change renewed (.pause id), ← change renewed (.kill id)] do
      assertEq (toJson (Pool.renew 100 revoked id "worker1" job.attempt)) (toJson revoked)
    let retiring ← change state (.configureWorkers #["worker2"])
    let retiring := Pool.tick 75 (Pool.renew 100 retiring id "worker1" job.attempt)
    assertTrue (Pool.valid retiring id "worker1" job.attempt) "Drain prevented current work from renewing"
    let drained := Pool.drained retiring "worker1" retiring.membership.generation
    assertEq (toJson (Pool.renew 100 drained id "worker1" job.attempt)) (toJson drained)⟩,
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
        assertEq job.branchStart Location.root "Expected the parent branch start"
        state := Pool.report next run ⟨worker, job.attempt, .ok .done, #[]⟩
      assertTrue (state.runs.all (·.scheduler.finished)) "A run lost its completion"⟩
]
end LeanCloudTests
