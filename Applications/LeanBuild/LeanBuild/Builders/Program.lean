import LeanBuild.Builders.Model
import LeanBuild.LakeSession
import LeanEff.Core

namespace LeanBuild.Builders
open Lean LeanCloud LeanEff

/-- Domain capabilities. The handler owns every resource; requests contain data. -/
inductive Operation (α : Type) : Type → Type 1 where
  | readResult (name : String) : Operation α (Option BuildResult)
  | commitResult (result : BuildResult) : Operation α BuildResult
  | prepared : Operation α (Std.HashSet String)
  | remember (inputs : Array BuildResult) : Operation α Unit
  | install (module : Module) (inputs : Array BuildResult) (prefetch : Bool) : Operation α Unit
  | lake (operation : LakeSession.Operation α β) : Operation α β
  | publish (module : Module) (value : α) : Operation α BuildResult
  | receive (count : Nat) : Operation α (Array WorkDelivery × Bool)
  | send (items : Array WorkItem) : Operation α Unit
  | complete (receipts : Array String) (failed : Bool) : Operation α Unit
  | release (receipts : Array String) : Operation α Unit
  | cancelled : Operation α Bool
  | events : Operation α (Nat × Array (Event α))
  | activity (text : String) : Operation α Unit

inductive BuildEffect (α : Type) : Effect where
  | request (operation : Operation α β) : BuildEffect α (Except String β)
  /-- Start a scoped job; its eventual reply joins the coordinator's event stream. -/
  | launch (job : EffF (BuildEffect α) Empty (Except String (Event α))) : BuildEffect α Unit
  /-- Bounded overlap, preserving result order and joining on failure. -/
  | parallel (limit count : Nat) (jobs : Fin count → EffF (BuildEffect α) Empty (Except String β)) :
      BuildEffect α (Except String (Array β))
  | all (limit count : Nat) (jobs : Fin count → EffF (BuildEffect α) Empty (Except String Bool)) :
      BuildEffect α (Except String Bool)

abbrev Program (α : Type) := ExceptT String (EffF (BuildEffect α) Empty)

def perform (operation : Operation α β) : Program α β := ExceptT.mk (EffF.send (.request operation))

def parallel (limit : Nat) (items : Array β) (body : β → Program α γ) : Program α (Array γ) :=
  ExceptT.mk (EffF.send (.parallel limit items.size (fun i => (body items[i]).run)))

def all (limit : Nat) (items : Array β) (body : β → Program α Bool) : Program α Bool :=
  ExceptT.mk (EffF.send (.all limit items.size (fun i => (body items[i]).run)))

private def inputs (cfg : Settings) (m : Module) : Program α (Array BuildResult) := do
  let missing ← liftExcept (Dependencies.missing cfg.modules (← perform .prepared) m.imports)
  parallel (ioConcurrency cfg.cpus) missing fun dep => do
    let some result ← perform (.readResult dep.name) | throw "Missing transitive prerequisite"
    return result

/-- Preparation policy is shared by the real handler and deterministic models. -/
def prepare (cfg : Settings) (m : Module) : Program α (Event α) := do
  if let some result ← perform (.readResult m.name) then return .published result
  let parents ← parallel (ioConcurrency cfg.cpus) m.imports fun name => perform (.readResult name)
  if parents.any Option.isNone then return .deferred m.name
  if parents.any (fun r => r.any (·.status != .built)) then
    return .published (← perform (.commitResult {
      name := m.name, status := .blocked, message := "A prerequisite failed" }))
  let missing ← inputs cfg m
  let direct := parents.filterMap id
  perform (.install m (direct ++ missing.filter (fun r => !m.imports.contains r.name)) false)
  perform (.remember missing)
  return .prepared m.name

/-- A durable result must be followed by all successor notifications before ACK.
Each successor progresses independently, even when another has many parents. -/
def settle (cfg : Settings) (m : Module) (result : BuildResult) (receipts : Array String) : Program α (Event α) := do
  let candidates := cfg.dependents[m.name]?.getD #[]
  let concurrency := ioConcurrency cfg.cpus
  let checks := max 1 (min concurrency candidates.size)
  discard <| parallel checks candidates fun candidate => do
    let ready ← all (concurrency / checks) candidate.imports fun name => return (← perform (.readResult name)).isSome
    if ready && !(← perform .cancelled) then
      perform (.send #[item cfg.scores candidate])
  unless ← perform .cancelled do perform (.complete receipts (result.status != .built))
  return .settled m.name receipts

def prefetch (cfg : Settings) (value : Json) : Program α Unit := do
  let name : String ← liftExcept (fromJson? value)
  let some m := cfg.modules[name]? | throw "Unknown queued module"
  if (← perform (.readResult name)).isSome then return
  let parents ← parallel (ioConcurrency cfg.cpus) m.imports fun name => perform (.readResult name)
  unless parents.all (fun result => result.any (·.status == .built)) do return
  let missing ← inputs cfg m
  unless missing.isEmpty do
    perform (.install m missing true)
    perform (.remember missing)

def seedProgram (plan : Plan) : Program α Unit := do
  liftExcept (validateModules plan.modules)
  let roots := plan.modules.filter (·.imports.isEmpty)
  let scores := priorities plan.modules
  for offset in [:((roots.size + 99) / 100)] do
    perform (.send ((roots.extract (offset * 100) ((offset + 1) * 100)).map (item scores)))

def resultsProgram (plan : Plan) (cpus : Nat) : Program α (Array BuildResult) :=
  parallel (ioConcurrency cpus) plan.modules fun m => do
    let some result ← perform (.readResult m.name) | throw s!"Missing module result: {m.name}"
    return result

private def launch (job : Program α (Event α)) : Program α Unit := ExceptT.mk do
  EffF.send (BuildEffect.launch job.run)
  return .ok ()

/-- Dispatch never waits for preparation/publication: only submitting to the
persistent Lake session is synchronous. The handler scopes all launched jobs. -/
def dispatch (cfg : Settings) : Action α → Program α Unit
  | .submit m => perform (.lake (.submit m))
  | .receive count => launch do
    let (deliveries, idle) ← perform (.receive count)
    return .received deliveries idle
  | .prepare m => launch (prepare cfg m)
  | .publish m value => launch do
    let result ← perform (.publish m value)
    unless result.name == m.name do throw "Builder returned an unrequested module"
    return .published (← perform (.commitResult result))
  | .settle m result receipts => launch (settle cfg m result receipts)
  | .release name receipts => launch do
    perform (.release receipts)
    return .settled name receipts

partial def loop (cfg : Settings) (state : State α := {}) : Program α Bool := do
  let (now, events) ← perform .events
  if events.any (fun | .cancelled => true | _ => false) then return false
  let compiled ← perform (.lake .poll)
  let events := events ++ compiled.map fun (name, value) => Event.compiled name value
  let (state, actions) ← liftExcept (advance cfg now state events)
  for action in actions do dispatch cfg action
  perform (.activity (state.activity cfg.cpus))
  if state.finished then return true
  loop cfg state

def program (plan : Plan) (cpus : Nat) : Program α Unit := do
  liftExcept (validateModules plan.modules)
  perform (.lake (.start cpus))
  if ← loop (.ofPlan plan cpus) then perform (.lake .finish)
  else perform (.lake .cancel)

end LeanBuild.Builders
