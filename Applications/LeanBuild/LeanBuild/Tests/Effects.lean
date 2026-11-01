import LeanBuild.Tests.BuilderModel
import LeanBuild.Project
import LeanBuild.Prefetch.Program

namespace LeanBuild.Tests
open Lean LeanEff LeanCloud Builders

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  unless condition do throw message

private def plan (modules : Array Module) : Plan := {
  commit := "model", toolchain := "model", platform := "model", source := default, modules }

/-- Each generated DAG runs on 2–4 builders with separate CPU budgets, Lake
sessions and artifact caches. Reproducible schedules interleave individual Eff
requests, simulated compiler completions, lease expiry and cooperative cancellation. -/
private def schedules : Except String Unit := do
  let phases := #["install", "submit", "publish", "commit", "send", "ack"]
  let mut staleAcks := 0
  let mut repeatedCommits := 0
  let mut overlappingBuilders := 0
  let mut crossWorkerRedeliveries := 0
  let mut releasedOnCancel := 0
  let mut cancelledJobs := 0
  let mut cancellationPhases : Std.HashSet String := {}
  for seed in [:40] do
    let modules := (Array.range 36).map fun i =>
      let parents := if i < 12 then #[] else
        (Array.range i).filter fun j => (j * 13 + i * 7 + seed) % 11 == 0
      { name := s!"M{i}", imports := parents.map (s!"M{·}") : Module }
    let p := plan modules
    let cpus := (Array.range (2 + seed % 3)).map fun i => 2 + (seed + i) % 4
    for failure in [none, some "M0", some "M7"] do
      for mode in [:3] do
        let faults : BuilderModel.Faults := {
          expire := if mode == 0 then 0 else 2
          cancelAfter := if mode == 2 then phases[seed % phases.size]? else none }
        match BuilderModel.run p cpus seed failure faults with
        | .error error => throw s!"seed={seed}, failure={failure}, mode={mode}: {error}"
        | .ok final =>
          ensure (final.outcomes.all Except.isOk) "Unexpected builder error in cancellation/redelivery schedule"
          let c := final.coverage
          ensure (c.requests > modules.size && c.switches > 0 && c.poolOverlap)
            s!"seed={seed}: generated schedule did not interleave effects/pool children"
          if mode > 0 then ensure (c.expiries == 2 && c.redeliveries ≥ 2) s!"seed={seed}: missing redelivery coverage"
          if mode == 2 then
            ensure (c.cancellations == 1 && c.cancelledOutstanding > 0 && faults.cancelAfter == some c.cancellationPhase)
              s!"seed={seed}: missing cancellation coverage"
            cancellationPhases := cancellationPhases.insert c.cancellationPhase
          else ensure (c.cancellations == 0) "Unexpected cancellation"
          staleAcks := staleAcks + c.staleAcks
          repeatedCommits := repeatedCommits + c.repeatedCommits
          crossWorkerRedeliveries := crossWorkerRedeliveries + c.crossWorkerRedeliveries
          releasedOnCancel := releasedOnCancel + c.releasedOnCancel
          cancelledJobs := cancelledJobs + c.cancelledJobs
          if c.buildersOverlap && final.participating ≥ 2 then overlappingBuilders := overlappingBuilders + 1
          let mut expected : Std.HashMap String Status := {}
          ensure (final.records.size == modules.size) "Missing or additional durable results"
          for m in modules do
            let status : Status := if m.imports.any (fun n => expected[n]? != some .built) then .blocked
              else if failure == some m.name then .failed else .built
            expected := expected.insert m.name status
            ensure (final.records[m.name]?.map (·.status) == some status)
              s!"seed={seed}, failure={failure}, mode={mode}, module={m.name}: DAG result differs"
  ensure (staleAcks > 0 && repeatedCommits > 0 && overlappingBuilders > 0)
    "Schedules missed stale ACKs, competing commits or overlapping builders"
  ensure (phases.all cancellationPhases.contains) "Schedules missed a cancellation boundary"
  ensure (crossWorkerRedeliveries > 0 && releasedOnCancel > 0 && cancelledJobs > 0)
    "Schedules missed redelivery to another builder or cancellation lease cleanup"

/-- One-off operation failures reach the real Eff continuation, then stop that
builder scope. Other builders recover its released work; no crash retry is used.
Half of the schedules also fail engine cancellation after it stops compiler jobs. -/
private def operationFailures : Except String Unit := do
  let sites : Array BuilderModel.FaultSite := #[.readResult, .send, .receive, .publish]
  for seed in [:40] do
    let modules := (Array.range 24).map fun i =>
      { name := s!"F{i}", imports := if i < 8 then #[] else #[s!"F{i-8}"] : Module }
    for site in sites do
      for cleanup in [false, true] do
        let faults : BuilderModel.Faults := { operation := some site, skip := seed % 4, failCleanup := cleanup }
        match BuilderModel.run (plan modules) #[2, 3, 4] seed none faults with
        | .error error => throw s!"fault seed={seed}, site={reprStr site}, cleanup={cleanup}: {error}"
        | .ok final =>
          ensure (final.coverage.operationFailures == 1) "Operation failure was never injected"
          let errors := final.outcomes.filterMap fun | .error error => some error | _ => none
          let expected := if cleanup then BuildError.cleanup site.error (.tool "cancel failed") else site.error
          ensure (errors == #[expected]) s!"Wrong fault propagation: {reprStr errors}"
          ensure (final.coverage.cleanupFailures == if cleanup then 1 else 0) "Missing cleanup failure coverage"
          ensure (final.records.size == modules.size && final.records.toArray.all (fun (_, r) => r.status == .built))
            "Surviving builders did not finish released work"

/-- Exercise the critical interleavings directly, including late duplicate
receipts and cancellation during an upload. -/
private def transitions : Except String Unit := do
  let m : Module := ⟨"A", #[]⟩
  let cfg := Settings.ofPlan (plan #[m]) 2
  let (s, _) ← advance cfg 0 ({} : Builders.State Unit) #[]
  let (s, _) ← advance cfg 1 s #[.received #[⟨"r1", toJson "A"⟩] false]
  let (s, _) ← advance cfg 2 s #[.prepared "A"]
  let (s, actions) ← advance cfg 3 s #[.compiled "A" ()]
  ensure (s.submitted.isEmpty && s.uploading.contains "A" &&
    actions.any (fun | .publish _ _ => true | _ => false)) "Compilation did not free its slot before publishing"
  let (cancelled, actions) ← advance cfg 4 s #[.cancelled]
  ensure (cancelled.finished && actions.isEmpty) "Cancellation admitted more work"
  let result : BuildResult := { name := "A", status := .built }
  let (s, _) ← advance cfg 4 s #[.published result]
  let s := { s with receiving := true }
  let (s, _) ← advance cfg 5 s #[.received #[⟨"r2", toJson "A"⟩] false]
  let (s, actions) ← advance cfg 6 s #[.settled "A" #["r1"]]
  ensure (actions.any (fun | .settle _ _ receipts => receipts == #["r2"] | _ => false))
    "A late duplicate was dropped or recompiled"
  let (s, _) ← advance cfg 7 s #[.settled "A" #["r2"]]
  ensure s.unlocking.isEmpty "Duplicate settlement retained the module"
  ensure ((advance cfg 8 s #[.compiled "A" ()]).toOption.isNone) "Duplicate compiler reply was accepted"

private def preparation : Except String Unit := do
  let snapshot : Bundle.Snapshot := ⟨"unused", 1, #[]⟩
  let handle (failAt : String) : {α : Type} → Project.PrepareOp α → StateM (Array String) (Except BuildError α)
    | _, .fetch => pure (.ok "commit")
    | _, .hasSubmodules => pure (.ok false)
    | _, .checkProject => pure (.ok "toolchain")
    | _, .discover => pure (if failAt == "discover" then .error (.tool "discovery failed") else .ok #[])
    | _, .snapshot => pure (.ok snapshot)
    | _, .platform => pure (.ok "platform")
    | _, .publish _ => do
      modify (·.push "publish")
      return if failAt == "publish" then .error (.network "publication failed") else .ok default
    | _, .diagnostics => do modify (·.push "diagnostics"); return .ok default
  let (failed, log) := (Project.runWith (handle "discover") Project.prepare).run #[]
  ensure (failed.toOption.any (fun p => p.plan.isNone && p.error == "discovery failed") && log == #["diagnostics"])
    "Discovery failure was not a report"
  let (failed, log) := (Project.runWith (handle "publish") Project.prepare).run #[]
  ensure ((match failed with | .error (.network "publication failed") => true | _ => false) && log == #["publish"])
    "Publication failure was swallowed"

private def lakeLifecycle : Except String Unit := do
  let fresh : LakeSession.State := {}
  ensure (fresh.submit "A").toOption.isNone "Submitted before session startup"
  let opened ← fresh.start
  ensure opened.start.toOption.isNone "Started one session twice"
  let running ← opened.submit "A"
  ensure running.finish.toOption.isNone "Finished with an outstanding Lake job"
  ensure (running.submit "A").toOption.isNone "Submitted a duplicate Lake job"
  ensure (running.complete #["Unknown"]).toOption.isNone "Accepted an unknown Lake result"
  let drained ← running.complete #["A"]
  ensure (drained.complete #["A"]).toOption.isNone "Returned a Lake result twice"
  let closed ← drained.finish
  ensure (closed.submit "B").toOption.isNone "Submitted after session shutdown"
  ensure (running.cancel.phase == .closed && running.cancel.pending.isEmpty) "Cancellation retained active jobs"

private def finalization : Except String Unit := do
  let difference : Bundle.Difference := ⟨⟨"unused", 1, #[]⟩, #[]⟩
  let handle (failAt : String) : {α : Type} → Project.FinishOp α → StateM (Array String) (Except BuildError α)
    | _, .now => pure (.ok 10)
    | _, .progress _ => pure (.ok ())
    | _, .manifests _ => pure (.ok #[])
    | _, .restore _ => do modify (·.push "restore"); return .ok #[]
    | _, .targets => do
      modify (·.push "targets")
      return if failAt == "targets" then .error (.tool "compile failed") else .ok #["A"]
    | _, .difference _ => do modify (·.push "verify"); return .ok difference
    | _, .diagnostics => pure (.ok default)
    | _, .publish _ => do
      modify (·.push "publish")
      return if failAt == "publish" then .error (.network "upload failed") else .ok default
    | _, .commit => do modify (·.push "commit"); return .ok ()
  let (success, log) := (Project.runWith (handle "") (Project.finish #[])).run #[]
  ensure (success.toOption.any (·.status == .built) && log == #["restore", "targets", "verify", "publish", "commit"])
    "Workspace commit did not follow verified publication"
  let (failed, log) := (Project.runWith (handle "targets") (Project.finish #[])).run #[]
  ensure (failed.toOption.any (·.status == .failed) && !log.contains "commit" && !log.contains "publish")
    "Failed target build committed a workspace"
  let (failed, log) := (Project.runWith (handle "publish") (Project.finish #[])).run #[]
  ensure (failed.toOption.isNone && !log.contains "commit") "Publication failure committed a workspace"

private structure PreviewModel where
  seen : Array Nat := #[]
  started : Array Nat := #[]
  clock : Nat := 0

private def prefetchPolicy : Except String Unit := do
  let items := (Array.range 205).map fun i =>
    { position := ⟨205 - i, i⟩, value := toJson i : WorkPreview }
  let handle : {α : Type} → Prefetch.Operation α → StateM PreviewModel (Except BuildError α)
    | _, .observe => do
      let s ← get
      set { s with started := #[], clock := s.clock + 10 }
      if s.clock > 10000 then return .error (.protocol "Prefetch did not finish")
      return .ok (s.clock, s.started, s.seen.size == 205)
    | _, .peek after =>
      pure (.ok ((items.filter (fun item => after.all (·.sequence < item.position.sequence))).extract 0 100))
    | _, .start item => do
      modify fun s => { s with seen := s.seen.push item.position.sequence, started := s.started.push item.position.sequence }
      return .ok ()
  let (result, final) := (Prefetch.runWith handle (Prefetch.program 3)).run {}
  ensure (result.isOk && final.seen == Array.range 205) "Virtual-clock prefetch lost order or repeated entries"

/-- Tests are pure; IO is only used to report a failed assertion to the runner. -/
def effectTests : IO Unit := do
  IO.ofExcept schedules
  IO.ofExcept operationFailures
  IO.ofExcept transitions
  IO.ofExcept preparation
  IO.ofExcept lakeLifecycle
  IO.ofExcept finalization
  IO.ofExcept prefetchPolicy
  IO.println "PASS pure Eff models: 680 effect-interleaved DAG schedules with operation/cleanup faults, 2–4 builders, redelivery, cancellation, Lake lifecycle, prefetch ordering and project boundaries"

end LeanBuild.Tests
