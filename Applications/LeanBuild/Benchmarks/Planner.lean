import LeanBuild.Batch

/-! Offline benchmark only. Generates a MiniZinc instance from the production
planner, validates solver schedules independently, and re-scores their grouping
using the same critical-order list scheduling policy as the heuristic benchmark.
All module IDs are zero-based internally and one-based in MiniZinc. -/

open Lean LeanCloud LeanBuild
namespace PlannerBench

structure Graph where
  modules : Array LeanBuild.Module
  dependencies : Array (Array Nat)
  order : Array Nat
  deriving ToJson, FromJson

structure Schedule where
  round : Array Nat
  worker : Array Nat
  start : Array Nat
  duration : Array Nat
  deriving ToJson, FromJson

structure Metrics where
  rounds : Nat
  jobs : Nat
  ticks : Nat
  cost : Nat
  deriving ToJson, FromJson, BEq, Repr

structure Case where
  graph : Graph
  cpus : Array Nat
  penalty : Nat
  baseline : Schedule
  metrics : Metrics
  planningMs : Nat
  deriving ToJson, FromJson

def require (condition : Bool) (message : String) : Except String Unit :=
  unless condition do throw message

def graph (modules : Array LeanBuild.Module) : Except String Graph := do
  validateModules modules
  require (!modules.isEmpty) "Empty graph"
  let ids := (modules.zipIdx).foldl (fun m (node, i) => m.insert node.name i)
    ({} : Std.HashMap String Nat)
  return {
    modules := modules
    dependencies := modules.map fun m => m.imports.map (ids[·]!)
    order := (criticalOrder modules).map (ids[·.name]!) }

/-- Independent list scheduler. Returns starts and duration for one job.
Dependencies outside the job were committed by an earlier round. -/
def simulate (g : Graph) (members : Array Nat) (cpus : Nat) :
    Except String (Array (Nat × Nat) × Nat) := do
  require (cpus > 0) "Zero CPU capacity"
  let memberSet := members.foldl (fun set i => set.insert i) ({} : Std.HashSet Nat)
  let mut pending := g.order.filter memberSet.contains
  let mut done : Std.HashSet Nat := {}
  let mut starts := #[]
  let mut ticks := 0
  for _ in [:members.size] do
    if pending.isEmpty then break
    let ready := (pending.filter fun i => g.dependencies[i]!.all fun dep =>
      !memberSet.contains dep || done.contains dep).extract 0 cpus
    require (!ready.isEmpty) "Cyclic or incomplete job"
    for i in ready do
      starts := starts.push (i, ticks)
      done := done.insert i
    pending := pending.filter (!done.contains ·)
    ticks := ticks + 1
  require pending.isEmpty "Incomplete simulation"
  return (starts, ticks)

/-- Check actual unit intervals, including CPU usage and round barriers.
This does not trust the solver's cost or feasibility status. -/
def validate (g : Graph) (cpus : Array Nat) (s : Schedule) : Except String Unit := do
  let n := g.modules.size
  require (!cpus.isEmpty && cpus.all (· > 0)) "Invalid CPU capacities"
  require (s.round.size == n && s.worker.size == n && s.start.size == n) "Schedule size mismatch"
  require (!s.duration.isEmpty) "No round durations"
  let mut boundaries := #[0]
  for d in s.duration do boundaries := boundaries.push (boundaries.back! + d)
  let mut loads : Std.HashMap (Nat × Nat) Nat := {}
  for i in [:n] do
    let r := s.round[i]!
    let w := s.worker[i]!
    require (r > 0 && r ≤ s.duration.size && w > 0 && w ≤ cpus.size) "Round/worker out of range"
    require (s.start[i]! ≥ boundaries[r-1]! && s.start[i]! + 1 ≤ boundaries[r]!)
      "Module crosses round boundary"
    let key := (w, s.start[i]!)
    let load := loads[key]?.getD 0 + 1
    require (load ≤ cpus[w-1]!) "CPU oversubscription"
    loads := loads.insert key load
    for dep in g.dependencies[i]! do
      require (s.start[dep]! + 1 ≤ s.start[i]!) "Dependency starts too late"
      require (s.round[dep]! ≤ r) "Dependency in later round"
      require (s.round[dep]! != r || s.worker[dep]! == w) "Cross-job dependency inside round"

/-- Re-run the returned grouping under our existing list scheduling policy.
The optimizer's start times are deliberately not used to claim executable speed. -/
def rescore (g : Graph) (cpus : Array Nat) (penalty : Nat) (s : Schedule) :
    Except String Metrics := do
  validate g cpus s
  let mut rounds := 0
  let mut jobs := 0
  let mut ticks := 0
  for r in [:s.duration.size] do
    let mut duration := 0
    let mut nonempty := false
    for w in [:cpus.size] do
      let members := (Array.range g.modules.size).filter fun i =>
        s.round[i]! == r+1 && s.worker[i]! == w+1
      if members.isEmpty then continue
      nonempty := true
      jobs := jobs + 1
      let (_, time) ← simulate g members cpus[w]!
      duration := max duration time
    if nonempty then rounds := rounds + 1
    ticks := ticks + duration
  return { rounds, jobs, ticks, cost := ticks + penalty * rounds }

def prepare (g : Graph) (cpus : Array Nat) (penalty : Nat) : IO Case := do
  IO.ofExcept <| require (!cpus.isEmpty && cpus.all (· > 0)) "CPUs must be positive"
  let ids := (g.modules.zipIdx).foldl (fun m (node, i) => m.insert node.name i)
    ({} : Std.HashMap String Nat)
  let n := g.modules.size
  let mut s : Schedule := {
    round := Array.replicate n 0, worker := Array.replicate n 0
    start := Array.replicate n 0, duration := #[] }
  let mut pending := g.modules
  let mut done : Array BuildResult := #[]
  let mut offset := 0
  let started ← IO.monoMsNow
  for r in [:n] do
    if pending.isEmpty then break
    let groups := partition pending done cpus 0
    IO.ofExcept <| require (groups.size == cpus.size && groups.any (!·.isEmpty)) "Planner made no progress"
    let mut duration := 0
    let mut chosen : Std.HashSet String := {}
    for w in [:cpus.size] do
      let members := groups[w]!.map (ids[·.name]!)
      let (starts, time) ← IO.ofExcept (simulate g members cpus[w]!)
      duration := max duration time
      for (i, t) in starts do
        let some node := g.modules[i]? | throw (IO.userError "Unknown module ID")
        s := { s with
          round := s.round.set! i (r+1), worker := s.worker.set! i (w+1)
          start := s.start.set! i (offset+t) }
        chosen := chosen.insert node.name
        done := done.push { name := node.name, status := .built }
    s := { s with duration := s.duration.push duration }
    offset := offset + duration
    pending := pending.filter (!chosen.contains ·.name)
  let planningMs := (← IO.monoMsNow) - started
  IO.ofExcept <| require pending.isEmpty "Incomplete heuristic plan"
  let metrics ← IO.ofExcept (rescore g cpus penalty s)
  return { graph := g, cpus, penalty, baseline := s, metrics, planningMs }

def solverInstance (c : Case) (maxRounds : Nat) : Except String Json := do
  require (maxRounds ≥ c.metrics.rounds) "Round bound excludes baseline"
  let n := c.graph.modules.size
  let capacity := c.cpus.foldl (· + ·) 0
  let lower := (n + capacity - 1) / capacity
  -- Any plan within the incumbent cost has at most this many paid barriers.
  let maxRounds := if c.penalty == 0 then maxRounds else
    min maxRounds ((c.metrics.cost - lower) / c.penalty)
  let mut earliest := Array.replicate n 0
  let mut tailLength := Array.replicate n 1
  for i in [:n] do
    earliest := earliest.set! i ((c.graph.dependencies[i]!.map fun d => earliest[d]! + 1).foldl max 0)
  for i in (Array.range n).reverse do
    for d in c.graph.dependencies[i]! do
      tailLength := tailLength.set! d (max tailLength[d]! (tailLength[i]! + 1))
  let edges := c.graph.dependencies.zipIdx.flatMap fun (deps, i) => deps.map (· + 1, i+1)
  return Json.mkObj [
    ("n", toJson c.graph.modules.size), ("workers", toJson c.cpus.size), ("cpus", toJson c.cpus),
    ("edges", toJson edges.size), ("src", toJson (edges.map (·.1))), ("dst", toJson (edges.map (·.2))),
    ("max_rounds", toJson maxRounds), ("horizon", toJson c.metrics.cost),
    ("penalty", toJson c.penalty), ("upper", toJson c.metrics.cost),
    ("hint_round", toJson c.baseline.round), ("hint_worker", toJson c.baseline.worker),
    ("hint_start", toJson c.baseline.start),
    ("earliest", toJson earliest), ("tail_length", toJson tailLength),
    ("hint_duration", toJson (c.baseline.duration ++ Array.replicate (maxRounds-c.metrics.rounds) 0))]

def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

def writeJson [ToJson α] (path : System.FilePath) (value : α) : IO Unit :=
  IO.FS.writeFile path ((toJson value).pretty ++ "\n")

/-- A dependency-closed window of consecutive rounds. Earlier inputs are
already published; later rounds cannot be prerequisites. Keep global priority. -/
def window (c : Case) (first last : Nat) : Except String Case := do
  require (first > 0 && first ≤ last && last ≤ c.metrics.rounds) "Invalid round window"
  let ids := (Array.range c.graph.modules.size).filter fun i =>
    first ≤ c.baseline.round[i]! && c.baseline.round[i]! ≤ last
  let names := ids.foldl (fun set i => match c.graph.modules[i]? with
    | some m => set.insert m.name
    | none => set) ({} : Std.HashSet String)
  let modules := c.graph.modules.filterMap fun m =>
    if names.contains m.name then some { m with imports := m.imports.filter names.contains } else none
  let mut g ← graph modules
  let localIds := ids.zipIdx.foldl (fun map (old, new) => map.insert old new) ({} : Std.HashMap Nat Nat)
  g := { g with order := c.graph.order.filterMap (localIds[·]?) }
  let offset := (c.baseline.duration.extract 0 (first-1)).foldl (· + ·) 0
  let s : Schedule := {
    round := ids.map fun i => c.baseline.round[i]! - first + 1
    worker := ids.map (c.baseline.worker[·]!)
    start := ids.map fun i => c.baseline.start[i]! - offset
    duration := c.baseline.duration.extract (first-1) last }
  let metrics ← rescore g c.cpus c.penalty s
  return { graph := g, cpus := c.cpus, penalty := c.penalty, baseline := s, metrics, planningMs := 0 }

def saveCase (directory : System.FilePath) (c : Case) (maxRounds : Nat) : IO Unit := do
  IO.FS.createDirAll directory
  writeJson (directory / "case.json") c
  let data ← IO.ofExcept (solverInstance c maxRounds)
  writeJson (directory / "instance.json") data
  let rounds ← IO.ofExcept (data.getObjValAs? Nat "max_rounds")
  IO.println s!"{c.graph.modules.size} modules, CPUs {c.cpus}, baseline {repr c.metrics}, {c.planningMs} ms; round bound {rounds}"

def evaluate (c : Case) (log : String) : Except String Json := do
  let mut candidates : Array Json := #[]
  let mut statuses : Array String := #[]
  let mut statistics : Array Json := #[]
  let mut best := c.metrics
  for line in log.splitOn "\n" do
    if line.trimAscii.toString.isEmpty then continue
    let message ← Json.parse line
    let kind ← message.getObjValAs? String "type"
    if kind == "error" then throw s!"Solver error: {message.compress}"
    if kind == "status" then statuses := statuses.push (← message.getObjValAs? String "status")
    if kind == "statistics" then statistics := statistics.push (← message.getObjVal? "statistics")
    if kind != "solution" then continue
    let output ← message.getObjVal? "output"
    let s : Schedule ← fromJson? (← output.getObjVal? "json")
    let metrics ← rescore c.graph c.cpus c.penalty s
    let rounds := s.round.foldl max 0
    let solverTicks := s.duration.foldl (· + ·) 0
    let cost := solverTicks + c.penalty * rounds
    require (cost ≤ c.metrics.cost) "Solver violated objective bound"
    if metrics.cost < best.cost || (metrics.cost == best.cost && metrics.rounds < best.rounds) then best := metrics
    candidates := candidates.push (Json.mkObj [
      ("timeMs", (message.getObjVal? "time").toOption.getD Json.null),
      ("solverTicks", toJson solverTicks), ("solverCost", toJson cost), ("resimulated", toJson metrics)])
  return Json.mkObj [
    ("modules", toJson c.graph.modules.size), ("cpus", toJson c.cpus), ("penalty", toJson c.penalty),
    ("heuristic", toJson c.metrics), ("heuristicPlanningMs", toJson c.planningMs),
    ("statuses", toJson statuses), ("statistics", toJson statistics),
    ("candidates", toJson candidates), ("bestValidated", toJson best)]

def selfTest : IO Unit := do
  let g ← IO.ofExcept (graph #[⟨"A", #[]⟩, ⟨"B", #[]⟩, ⟨"C", #["A", "B"]⟩])
  let good : Schedule := { round := #[1,1,1], worker := #[1,1,1], start := #[0,0,1], duration := #[2] }
  IO.ofExcept <| validate g #[2,2] good
  for bad in [
      { good with worker := #[1,2,1] },
      { good with start := #[0,0,0] },
      { good with round := #[1,1,2] },
      { good with worker := #[1,1,0] },
      { good with start := #[0,0] },
      { good with duration := #[1] }] do
    IO.ofExcept <| require (!(validate g #[2,2] bad).isOk) "Validator accepted invalid schedule"
  IO.ofExcept <| require (!(validate g #[1,1] good).isOk) "Validator accepted oversubscription"
  let m ← IO.ofExcept (rescore g #[2,2] 1 good)
  IO.ofExcept <| require (m == ⟨1,1,2,3⟩) "Incorrect re-score"
  let idle := { good with start := #[0,0,2], duration := #[3] }
  let idleMetrics ← IO.ofExcept (rescore g #[2,2] 1 idle)
  IO.ofExcept <| require (idleMetrics == m) "Re-score trusted solver start times"
  let c ← prepare g #[2,2] 1
  IO.ofExcept <| require (c.metrics == m) "Baseline mismatch"
  IO.println "PASS independent schedule validation and re-simulation"

def fixtures (directory : System.FilePath) : IO Unit := do
  let independent := (Array.range 8).map fun i => { name := s!"I{i}", imports := #[] : LeanBuild.Module }
  let chain := (Array.range 5).map fun i => {
    name := s!"C{i}", imports := if i == 0 then #[] else #[s!"C{i-1}"] : LeanBuild.Module }
  let join : Array LeanBuild.Module := #[⟨"A", #[]⟩, ⟨"B", #[]⟩, ⟨"C", #["A", "B"]⟩]
  let wide := #[{ name := "Root", imports := #[] : LeanBuild.Module }] ++
    (Array.range 16).map fun i => { name := s!"F{i}", imports := #["Root"] : LeanBuild.Module }
  let cases : Array (String × Array Nat × Array LeanBuild.Module × Nat) := #[
    ("independent", #[2,2], independent, 3), ("chain", #[2,2], chain, 6),
    ("join", #[2,2], join, 3), ("fanout", #[2,2], wide, 7),
    ("heterogeneous", #[1,4], independent.extract 0 4, 2)]
  for (name, cpus, modules, expected) in cases do
    let c ← prepare (← IO.ofExcept (graph modules)) cpus 1
    IO.ofExcept <| require (c.metrics.cost == expected) s!"Unexpected fixture baseline: {name}"
    saveCase (directory / name) c modules.size
    writeJson (directory / name / "expected.json") expected

end PlannerBench

def main (args : List String) : IO Unit := do
  match args with
  | ["test"] => PlannerBench.selfTest
  | ["fixtures", directory] => PlannerBench.fixtures directory
  | ["prepare", input, directory, cpuText, penaltyText, roundsText] =>
    let cpus ← (cpuText.splitOn ",").toArray.mapM fun s => do
      let some n := s.toNat? | throw (IO.userError "Expected comma-separated positive CPU capacities")
      pure n
    let some penalty := penaltyText.toNat? | throw (IO.userError "Invalid overhead")
    let some rounds := roundsText.toNat? | throw (IO.userError "Invalid round bound")
    let modules ← PlannerBench.readJson input
    let g ← IO.ofExcept (PlannerBench.graph modules)
    let c ← PlannerBench.prepare g cpus penalty
    let maxRounds := if rounds == 0 then c.metrics.rounds else rounds
    PlannerBench.saveCase directory c maxRounds
  | ["window", source, directory, firstText, lastText] =>
    let c ← PlannerBench.readJson (System.FilePath.mk source / "case.json")
    let some first := firstText.toNat? | throw (IO.userError "Invalid first round")
    let some last := lastText.toNat? | throw (IO.userError "Invalid last round")
    let sub ← IO.ofExcept (PlannerBench.window c first last)
    PlannerBench.saveCase directory sub (2 * sub.metrics.rounds)
  | ["evaluate", directory, log, output] =>
    let c ← PlannerBench.readJson (System.FilePath.mk directory / "case.json")
    let report ← IO.ofExcept (PlannerBench.evaluate c (← IO.FS.readFile log))
    PlannerBench.writeJson output report
    IO.println report.pretty
  | _ => throw (IO.userError "Usage: plan_bench test | fixtures OUT | prepare DAG.json OUT CPUs PENALTY MAX_ROUNDS | window SOURCE OUT FIRST LAST | evaluate OUT SOLVER.jsonl REPORT.json")
