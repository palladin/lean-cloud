import LeanCloudTests.Generated

/-! Seeded tests of the deployed Pool transitions and actual replay worker.
Each run gets its own replay namespace. Sim exposes worker commit/reply/crash
boundaries; the driver interleaves them with Pool administration and reports.
Scheduler transitions are atomic here: HTTP delivery and SQLite commit failures
belong to the adapter tests, not to this state-machine test. -/

namespace LeanCloudTests.PoolModel
open Lean LeanCloud

private abbrev World := SimulationBackend.World
private instance : Inhabited World := ⟨{}⟩
private instance : Inhabited Pool.Run := ⟨{ id := "" }⟩

private structure Workflow where
  id : String
  source : Tree
  input : Nat
  expected : Exit

private instance : Inhabited Workflow := ⟨⟨"", .value 0, 0, .success Json.null⟩⟩

private structure Task where
  run : Nat
  assignment : Assignment
  actor : Simulation.Actor World Report
  finalizing : Option Exit := none

private structure Model where
  pool : Pool.State := {}
  workflows : Array Workflow
  worlds : Array World
  tasks : Array (Option Task) := #[none, none, none]
  reports : Array (Nat × Report) := #[]
  delivered : Array (Nat × Report) := #[]
  orphans : Array (Nat × Simulation.Orphan World) := #[]

private def workers := #["worker1", "worker2", "worker3"]
private def cancelled := Exit.cancelled "Killed by user"

-- Suspended Sim continuations live in Type 1; checks share that result universe.
private def ensure (condition : Bool) (message : String) : Except String PUnit.{2} :=
  unless condition do throw message

private def same [ToJson α] (left right : α) : Bool := toJson left == toJson right

private def control (model : Model) (command : Pool.Command) : Except String Model :=
  match Pool.command model.pool command with
  | .ok (pool, _) => .ok { model with pool }
  | .error error => .error error

private def execute (model : Model) (worker run : Nat) (assignment : Assignment) : SimM World Report :=
  Worker.execute workers[worker]! (SimulationBackend.observed workers[worker]!) SimulationBackend.blobs 10000
    (lower model.workflows[run]!.source) model.workflows[run]!.input assignment

private def acquire (model : Model) (worker : Nat) : Except String Model := do
  let (pool, reply) := Pool.acquire 100 model.pool workers[worker]!
  let model := { model with pool }
  match reply with
  | .execute id assignment =>
    let some run := model.workflows.findIdx? (·.id == id) | throw "Assignment names an unknown workflow"
    ensure (Pool.valid pool id workers[worker]! assignment.attempt) "New assignment is invalid"
    let task := Task.mk run assignment (.ofProgram (execute model worker run assignment)) none
    return { model with tasks := model.tasks.set! worker (some task) }
  | .finalize id attempt outcome =>
    let some run := model.workflows.findIdx? (·.id == id) | throw "Finalization names an unknown workflow"
    ensure (Pool.valid pool id workers[worker]! attempt) "New finalization is invalid"
    let action := Worker.finalize workers[worker]! (SimulationBackend.observed workers[worker]!) attempt outcome
    let task : Task := ⟨run, ⟨attempt, Location.root⟩, .ofProgram action, some outcome⟩
    return { model with tasks := model.tasks.set! worker (some task) }
  | .drain generation => return { model with pool := Pool.drained pool workers[worker]! generation }
  | .idle => return model
  | .acknowledged => throw "Acquisition returned a report acknowledgement"

private def simulationEvent (model : Model) (worker : Nat) (task : Task) (event : Simulation.Event 1) :
    Except String Model := do
  let start : Simulation.Start World Report 1 := fun _ _ => match task.finalizing with
    | none => execute model worker task.run task.assignment
    | some outcome => Worker.finalize workers[worker]! (SimulationBackend.observed workers[worker]!) task.assignment.attempt outcome
  let state : Simulation.State World Report 1 := ⟨model.worlds[task.run]!, fun _ => task.actor, fun _ => 0, #[]⟩
  let after ← (Simulation.step start event state).mapError reprStr
  return { model with
    worlds := model.worlds.set! task.run after.world
    tasks := model.tasks.set! worker (some { task with actor := after.actors ⟨0, by decide⟩ })
    orphans := model.orphans ++ after.orphans.map (task.run, ·) }

private def advance (model : Model) (worker : Nat) : Except String Model := do
  let some task := model.tasks[worker]! | return ← acquire model worker
  -- Production workers check revocation at record boundaries. An already
  -- submitted operation may still commit later as an orphan.
  if !Pool.valid model.pool model.workflows[task.run]!.id workers[worker]! task.assignment.attempt then
    let model ← match task.actor with
      | .waiting .. | .responding .. => simulationEvent model worker task (.crash ⟨0, by decide⟩)
      | _ => pure model
    return { model with tasks := model.tasks.set! worker none }
  match task.actor with
  | .waiting .. => simulationEvent model worker task (.commit ⟨0, by decide⟩)
  | .responding .. => simulationEvent model worker task (.resume ⟨0, by decide⟩)
  | .stopped => return { model with tasks := model.tasks.set! worker none }
  | .finished report =>
    if let .error error := report.progress then throw s!"Replay worker failed: {reprStr error}"
    return { model with tasks := model.tasks.set! worker none, reports := model.reports.push (task.run, report) }

private def crash (model : Model) (worker : Nat) : Except String Model := do
  let some task := model.tasks[worker]! | return model
  let model ← match task.actor with
    | .waiting .. | .responding .. => simulationEvent model worker task (.crash ⟨0, by decide⟩)
    | _ => pure model
  return { model with tasks := model.tasks.set! worker none }

private def deliver (model : Model) (index : Nat) : Model :=
  match model.reports[index]? with
  | none => model
  | some (run, report) => { model with
      pool := Pool.report model.pool model.workflows[run]!.id report
      reports := model.reports.eraseIdxIfInBounds index
      delivered := model.delivered.push (run, report) }

private def settleOrphan (model : Model) (index : Nat) (commit : Bool) : Model :=
  match model.orphans[index]? with
  | none => model
  | some (run, orphan) => { model with
      worlds := if commit then model.worlds.set! run (orphan.commit model.worlds[run]!) else model.worlds
      orphans := model.orphans.eraseIdxIfInBounds index }

private def restart (model : Model) : Except String Model := do
  -- Restart starts from the wire/storage representation, not an in-memory alias.
  let .ok saved := Json.parse (toJson model.pool).compress >>= fromJson? (α := Pool.State)
    | throw "Cannot restore saved Pool state"
  let pool := Pool.recover saved
  ensure (same (Pool.recover pool) pool) "Recovery is not idempotent"
  for run in pool.runs do
    ensure (run.scheduler.jobs.all fun job => match job.status with | .running .. => false | _ => true)
      "Recovery retained a live attempt"
  return { model with pool }

private def kill (model : Model) (run : Nat) : Except String Model := do
  control model (.kill model.workflows[run]!.id)

private def check (before after : Model) : Except String PUnit.{2} := do
  ensure (decide ((after.pool.runs.map (·.id)).toList.Pairwise (· ≠ ·))) "Duplicate run IDs"
  for (run, index) in after.pool.runs.toList.zipIdx do
    let previous := before.pool.runs[index]!
    ensure (run.id == previous.id) "Run order/identity changed"
    ensure (previous.scheduler.nextAttempt ≤ run.scheduler.nextAttempt) "Attempt counter went backwards"
    ensure (previous.mode != .killed || run.mode == .killed) "A killed run was reactivated"
    ensure (run.scheduler.error.isNone) "Generated workflow acquired an interpreter error"
    ensure (decide ((run.scheduler.jobs.map (·.branch)).toList.Pairwise (· ≠ ·))) "Duplicate branch jobs"
    for job in previous.scheduler.jobs do
      if job.status == .done then
        ensure (run.scheduler.jobs.any fun next => next.branch == job.branch && next.status == .done)
          "Completed branch reopened or disappeared"
    for job in run.scheduler.jobs do
      match job.status with
      | .running worker attempt _ =>
        ensure (run.mode == .active && attempt < run.scheduler.nextAttempt) "Invalid running attempt"
        ensure (Pool.valid after.pool run.id worker attempt) "Running job is not valid"
      | .done =>
        ensure ((after.worlds[index]!.records.lookup (ReplayStore.returnKey job.branch)).isSome)
          "Scheduler completed a branch without a durable result"
      | _ => pure .unit
    let world := after.worlds[index]!
    for (key, record) in before.worlds[index]!.records do
      ensure (world.records.lookup key == some record) "A committed replay record changed"
    if let some record := world.records.lookup (ReplayStore.returnKey Location.root) then
      ensure (record.outcome == after.workflows[index]!.expected ||
        (run.mode == .killed && record.outcome == cancelled)) "Stored outcome differs from direct evaluation"
    if run.finalization == .done then
      ensure ((world.records.lookup (ReplayStore.returnKey Location.root)).isSome) "Kill lost its terminal result"
  for worker in workers do
    let assignments := after.pool.runs.foldl (fun count run => count +
      (run.scheduler.jobs.filter fun job => match job.status with
        | .running owner attempt _ => owner == worker && Pool.valid after.pool run.id worker attempt
        | _ => false).size +
      (match run.finalization with | .running owner _ _ => if owner == worker then 1 else 0 | _ => 0)) 0
    ensure (assignments ≤ 1) s!"{worker} has valid assignments in several runs"

private def isolated (before after : Model) (id : String) : Except String PUnit.{2} := do
  for run in before.pool.runs do
    if run.id != id then
      let some unchanged := after.pool.runs.find? (·.id == run.id) | throw "Unrelated run disappeared"
      ensure (same run unchanged) "An operation changed another run"

private def progress (model : Model) : Except String Model := do
  let mut model := model
  for worker in [:workers.size] do
    let after ← advance model worker
    check model after
    model := after
  let after := deliver model 0
  check model after
  return after

/-- High LCG bits choose operations; low bits would lock workers and operations
into a short repeating pattern. Every failure records the seed and event prefix. -/
private def event (model : Model) (random : Nat) (allowKill : Bool) : Except String (String × Model) := do
  let worker := random / 65536 % workers.size
  let run := random / 4096 % model.workflows.size
  let id := model.workflows[run]!.id
  match random / 256 % 32 with
  | 0 | 1 | 2 =>
    let command := match random / 256 % 32 with
      | 0 => Pool.Command.submit id | 1 => .pause id | _ => .resume id
    let after ← match Pool.command model.pool command with
      | .ok (pool, _) => pure { model with pool }
      | .error _ =>
        ensure (model.pool.runs[run]!.mode == .killed) "Unexpected administrative failure"
        pure model
    isolated model after id
    return (reprStr command, after)
  | 3 =>
    if !allowKill then return (s!"advance worker {worker}", ← advance model worker)
    -- Keep one workflow alive so every seed must complete real work after chaos.
    let run := 1 + run % (model.workflows.size - 1)
    let after ← kill model run
    isolated model after model.workflows[run]!.id
    return (s!"kill {run}", after)
  | 4 =>
    let mask := random / 8192 % 8
    let active := (workers.zipIdx.filter fun (_, i) => mask / (2 ^ i) % 2 == 1).map (·.1)
    return (s!"configure {active}", ← control model (.configureWorkers active))
  | 5 =>
    -- An explicit stopped-worker acknowledgement is sent only after its
    -- process has stopped. Old generations may arrive after it rejoins.
    let model ← crash model worker
    let generation := model.pool.membership.generation - random / 16384 % 2
    return (s!"drained {worker} {generation}",
      { model with pool := Pool.drained model.pool workers[worker]! generation })
  | 6 => return ("scheduler restart", ← restart model)
  | 7 => return ("expire assignments", { model with pool := Pool.tick 100 model.pool })
  | 8 =>
    let (pool, reply) := Pool.acquire 100 model.pool workers[worker]!
    let (again, duplicate) := Pool.acquire 100 pool workers[worker]!
    ensure (same pool again && same reply duplicate) "Duplicate readiness changed the assignment"
    -- Model a lost reply: a later readiness request must recover the assignment.
    return (s!"repeat readiness {worker}", { model with pool })
  | 9 =>
    let index := random / 8192 % max 1 model.reports.size
    let after := deliver model index
    if let some (run, _) := model.reports[index]? then isolated model after model.workflows[run]!.id
    return (s!"deliver report {index}", after)
  | 10 =>
    let index := random / 8192 % max 1 model.delivered.size
    let reports := match model.delivered[index]? with
      | some report => model.reports.push report | none => model.reports
    return (s!"redeliver report {index}", { model with reports })
  | 11 => return (s!"crash worker {worker}", ← crash model worker)
  | 12 | 13 =>
    let commit := random / 256 % 32 == 12
    let index := random / 8192 % max 1 model.orphans.size
    return (s!"orphan {index} commit={commit}", settleOrphan model index commit)
  | 14 => return ("time passes", { model with pool := Pool.tick 50 model.pool })
  | 15 =>
    let some task := model.tasks[worker]! | return ("no heartbeat", model)
    let id := model.workflows[task.run]!.id
    let pool := Pool.renew 100 model.pool id workers[worker]! task.assignment.attempt
    let after := { model with pool }
    isolated model after id
    if !Pool.valid model.pool id workers[worker]! task.assignment.attempt then
      ensure (same model.pool pool) "Heartbeat revived a revoked assignment"
    return (s!"renew {worker} {id} {task.assignment.attempt}", after)
  | 16 | 17 =>
    -- Permit useful work between faults rather than endlessly restarting
    -- workers before they have reached any record or suspension boundary.
    let mut after := model
    for _ in [:8] do after ← progress after
    return ("processing window", after)
  | _ => return (s!"advance worker {worker}", ← advance model worker)

private def setup (seed : Nat) : Except String (Array Workflow × Pool.State) := do
  let mut workflows : Array Workflow := #[]
  let mut pool : Pool.State := {}
  for run in [:3] do
    let id := s!"run-{run}"
    let generated := (generate (2 + seed % 2) (seed * 17 + run * 71)).1
    let source := Tree.parallel [.effect (seed + run), .parallel [generated, .value (run + 1)]]
    let input := seed % 17 + run * 29
    let .ok (outcome, _) := evaluate 1000000 (DirectInterpreter.interpret SimulationBackend.blobs (lower source) input).run {}
      | throw "Direct evaluation exhausted its test budget"
    let expected := match outcome with | .ok value => Exit.success (toJson value) | .error error => .failure error
    workflows := workflows.push ⟨id, source, input, expected⟩
    let .ok (next, _) := Pool.command pool (.submit id) | throw "Submission failed"
    pool := next
  return (workflows, pool)

private def initial (seed : Nat) : Except String Model :=
  match setup seed with
  | .error error => .error error
  | .ok (workflows, pool) =>
    control { pool, workflows, worlds := Array.replicate 3 {} } (.configureWorkers workers)

private def runSeed (seed : Nat) : Except String PUnit.{2} := do
  let mut model ← initial seed
  -- First reach a real parallel suspension in every run. Thus every generated
  -- trace starts with children, durable records, and reports to redeliver.
  for _ in [:100] do
    if model.pool.runs.all (·.scheduler.jobs.size > 1) then break
    model ← progress model
  ensure (model.pool.runs.all (·.scheduler.jobs.size > 1)) "Warmup did not fork every run"
  ensure (model.delivered.size ≥ 3) "Warmup did not deliver all root reports"
  let mut random := seed + 1
  let mut history : Array String := #[]
  for index in [:400] do
    random := nextSeed random
    let step := do
      let (description, after) ← event model random (seed % 2 == 1 && index ≥ 300)
      check model after
      return (description, after)
    match step with
    | .error error => throw s!"seed={seed} step={index} random={random}\n{error}\nEvents:\n{String.intercalate "\n" history.toList}"
    | .ok (description, after) =>
      history := history.push description
      model := after
  -- Faults stop. Restore capacity, resume surviving workflows, and fairly run
  -- every worker/report until all surviving workflows have durable results.
  model ← control model (.configureWorkers workers)
  for run in model.pool.runs do
    if run.mode != .killed then model ← control model (.resume run.id)
  model ← restart model
  for _ in [:model.orphans.size] do
    let after := settleOrphan model 0 true
    check model after
    model := after
  for _ in [:10000] do
    if model.pool.runs.all (fun run => if run.mode == .killed then run.finalization == .done else run.scheduler.finished) then
      check model model
      return
    model ← progress model
  throw s!"seed={seed}: Pool failed to finish after faults stopped"

def cases : Array TestCase := (Array.range 64).map fun seed =>
  ⟨s!"pool/model/{seed}", do
    match runSeed seed with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"seed={seed}: {error}")⟩

end LeanCloudTests.PoolModel
