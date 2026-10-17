import LeanCloudCli.Connections
import LeanCloud.Timing

namespace LeanCloudCli
open Lean LeanCloud

/-- All workflow operations use the scheduler API, including localhost deployments. -/
def Context.deployment (ctx : Context) : Cli Deployment := do
  let connection ← ctx.requireConnection
  let info ← Client.call connection .describe
  let programs ← Client.call connection .programs
  let deployment : Deployment := { project := ctx.project, image := info.image, programs }
  saveJson (ctx.home / "deployment.json") deployment
  return deployment

def Context.loadRun (ctx : Context) (id : String) : Cli Run := do
  validateId id
  let connection ← ctx.requireConnection
  let info ← Client.call connection (.run id)
  unless info.id == id do throw "Deployment returned a different run identity"
  let run := Connections.cachedRun info
  request (.createDir (ctx.directory id))
  saveJson (ctx.directory id / "run.json") run
  return run

def Context.control (ctx : Context) (id : String) : Cli Pool.Mode := do
  let connection ← ctx.requireConnection
  return (← Client.call connection (.run id)).mode

def Context.allRuns (ctx : Context) : Cli (Array Run) := do
  let connection ← ctx.requireConnection
  let mut runs := #[]
  let mut after := none
  repeat
    let page ← Client.call connection (.runs after 50)
    for info in page.items do
      runs := runs.push (Connections.cachedRun info)
    match page.next with
    | none => break
    | some next =>
      unless after.all (· < next) do throw "Deployment returned a non-advancing page cursor"
      after := some next
  saveJson (ctx.home / "runs.json") runs
  return runs

def Context.node (ctx : Context) (role : String) : String := s!"{ctx.project}-{role}"

def Context.observation (ctx : Context) (run : Run) : Cli Timing.Status := do
  let status ← Client.call (← ctx.requireConnection) (.inspect run.id)
  if let some timing := status.timing then
    request (.createDir (ctx.directory run.id))
    saveJson (ctx.directory run.id / "timing.json") timing
  return status

def Context.outcome (ctx : Context) (run : Run) : Cli (Option Exit) :=
  do Client.call (← ctx.requireConnection) (.outcome run.id)

def Context.result (ctx : Context) (run : Run) : Cli String :=
  do Client.call (← ctx.requireConnection) (.result run.id)

def Context.savedTiming (ctx : Context) (run : Run) : Cli (Option Timing.Run) := do
  try
    let path := ctx.directory run.id / "timing.json"
    if ← request (.exists path) then pure (some (← readJson path)) else pure none
  catch _ => pure none

private def chooseProgram (programs : Array ProgramInfo) (name : String) : Except String ProgramInfo :=
  let found := programs.filter fun p => p.entry == name || (p.entry.splitOn "/").head! == name
  match found.toList with
  | [program] => .ok program
  | [] => .error s!"Unknown program: {name}"
  | _ => .error "Specify the program version (name/version)"

def Context.resume (ctx : Context) (id : String) : Cli Unit := do
  let connection ← ctx.requireConnection
  Connections.control ctx connection id (fun key => .control key id .resume)
  printLine s!"Resume accepted for {id}. Use 'ps' to inspect its state."

def Context.pause (ctx : Context) (id : String) : Cli Unit := do
  let connection ← ctx.requireConnection
  Connections.control ctx connection id (fun key => .control key id .pause)
  printLine s!"Pause accepted for {id}. Use 'ps' to observe workers stopping."

def Context.kill (ctx : Context) (id : String) : Cli Unit := do
  let connection ← ctx.requireConnection
  Connections.control ctx connection id (fun key => .control key id .kill)
  printLine s!"Kill accepted for {id}. Use 'ps' to observe finalization."

def Context.launch (ctx : Context) (name : String) (file : Option String) (id : Option String) : Cli Unit := do
  let connection ← ctx.requireConnection
  let program ← liftExcept (chooseProgram (← Client.call connection .programs) name)
  let input ← match file, program.sampleInput with
    | some file, _ => readJson (α := Json) ((← request .currentDir) / file)
    | none, some sample => pure sample
    | none, none => throw "This program needs --input FILE.json"
  let id ← match id with
    | some id => pure id
    | none => pure ("run-" ++ (← request .randomId))
  validateId id
  printLine s!"Submitting {id}. Retry with '--id {id}' if the connection is interrupted."
  Client.call connection (.submit id program.entry input)
  printLine s!"Submitted {id}. Use 'ps' or 'inspect {id}'."

def Context.removeRun (ctx : Context) (id : String) : Cli Unit := do
  Connections.control ctx (← ctx.requireConnection) id (fun key => .remove key id)
  request (.removeTree (ctx.directory id))
  printLine s!"Removed {id}."

end LeanCloudCli
