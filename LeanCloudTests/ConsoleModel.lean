import LeanCloudCli.Application

namespace LeanCloudTests.ConsoleModel
open Lean LeanCloud LeanCloudCli

structure Invocation where
  command : String
  args : Array String
  input : Option String
  deriving Inhabited, BEq, Repr

/-- A pure host for the real CLI, with scripted processes, input, time and failures. -/
structure World where
  files : Array (String × String) := #[]
  directories : Array String := #["/work"]
  env : Option String := none
  envs : Array (String × String) := #[]
  lines : List String := []
  keys : List UInt32 := []
  stdout : String := ""
  stderr : String := ""
  time : Nat := 0
  terminalAvailable : Bool := true
  terminal : Bool := false
  size : Nat × Nat := (120, 35)
  sizes : List (Nat × Nat) := []
  nextLock : Nat := 0
  locks : Array (LockId × String) := #[]
  trace : Array String := #[]
  processes : Array Invocation := #[]
  nextProcess : Nat := 0
  children : Array (ProcessId × List ProcessChunk) := #[]
  stream : Option (Invocation → Except String (List ProcessChunk)) := none
  failAt : Option Nat := none
  process : Invocation → Except String ProcessOutput := fun call =>
    .error s!"Unexpected process: {reprStr call}"

def World.file (world : World) (path : System.FilePath) : Option String :=
  (world.files.find? (·.1 == path.toString)).map (·.2)

def World.save (world : World) (path : System.FilePath) (text : String) : World :=
  { world with files := (world.files.filter (·.1 != path.toString)).push (path.toString, text) }

def World.json [ToJson α] (world : World) (path : System.FilePath) (value : α) : World :=
  world.save path (toJson value).compress

private def label : HostOp α → String
  | .process .. => "process" | .readFile .. => "readFile" | .writeFile .. => "writeFile"
  | .startProcess .. => "startProcess" | .pollProcess .. => "pollProcess" | .closeProcess .. => "closeProcess"
  | .rename .. => "rename" | .exists .. => "exists" | .readDir .. => "readDir"
  | .isDir .. => "isDir"
  | .createDir .. => "createDir" | .realPath .. => "realPath" | .currentDir => "currentDir"
  | .getEnv .. => "getEnv" | .pid => "pid" | .now => "now" | .sleep .. => "sleep"
  | .write .. => "write" | .flush => "flush" | .readLine => "readLine"
  | .enterTerminal => "enterTerminal" | .leaveTerminal => "leaveTerminal"
  | .key .. => "key" | .dimensions => "dimensions" | .lock .. => "lock" | .unlock .. => "unlock"

private def operation : HostOp α → ExceptT String (StateM World) α
  | .process command args input => do
    let call := Invocation.mk command args input
    modify fun w => { w with processes := w.processes.push call }
    liftExcept ((← get).process call)
  | .startProcess command args => do
    let call := Invocation.mk command args none
    modify fun w => { w with processes := w.processes.push call }
    let world ← get
    let chunks ← liftExcept <| match world.stream with
      | some stream => stream call
      | none => world.process call |>.map fun output =>
        [{ stdout := output.stdout.toUTF8, stderr := output.stderr.toUTF8, exitCode := some output.exitCode }]
    let token := ProcessId.mk world.nextProcess
    modify fun w => { w with nextProcess := w.nextProcess + 1, children := w.children.push (token, chunks) }
    return token
  | .pollProcess token timeout => do
    let some (_, chunks) := (← get).children.find? (·.1 == token) | throw "Unknown process"
    let chunk := chunks.headD { exitCode := some 0 }
    modify fun w => { w with
      time := w.time + timeout.toNat
      children := w.children.map fun (id, rest) => (id, if id == token then rest.drop 1 else rest) }
    return chunk
  | .closeProcess token => do
    unless (← get).children.any (·.1 == token) do throw "Unknown process"
    modify fun w => { w with children := w.children.filter (·.1 != token) }
  | .readFile path => do
    let some text := (← get).file path | throw s!"Missing file: {path}"
    return text
  | .writeFile path text => modify (·.save path text)
  | .rename source target => do
    let some text := (← get).file source | throw s!"Missing source: {source}"
    modify fun w => { (w.save target text) with files :=
      ((w.save target text).files.filter (·.1 != source.toString)) }
  | .exists path => do
    let world ← get
    return (world.file path).isSome || world.directories.contains path.toString
  | .readDir path => do
    let directory := path.toString ++ "/"
    let paths := (← get).directories ++ (← get).files.map (·.1)
    return paths.foldl (fun result p =>
      if p.startsWith directory then
        let name := (p.drop directory.length |>.toString.splitOn "/").head!
        if result.contains name then result else result.push name
      else result) #[]
  | .createDir path => modify fun w => { w with directories := w.directories.push path.toString }
  | .isDir path => return (← get).directories.contains path.toString
  | .realPath path => return path
  | .currentDir => return "/work"
  | .getEnv name => do
    if let some value := (← get).envs.find? (·.1 == name) then return some value.2
    if name == "LEAN_CLOUD_PROJECT" then return (← get).env
    if name == "HOME" then return some "/home/test"
    return none
  | .pid => return 42
  | .now => return (← get).time
  | .sleep ms => modify fun w => { w with time := w.time + ms.toNat }
  | .write text stderr => modify fun w =>
    if stderr then { w with stderr := w.stderr ++ text } else { w with stdout := w.stdout ++ text }
  | .flush => pure ()
  | .readLine => do
    let line := (← get).lines.headD ""
    modify fun w => { w with lines := w.lines.drop 1 }
    return line
  | .enterTerminal => do
    let active := (← get).terminalAvailable && !(← get).terminal
    if active then modify fun w => { w with terminal := true }
    return active
  | .leaveTerminal => modify fun w => { w with terminal := false }
  | .key timeout => do
    let key := (← get).keys.headD 4
    modify fun w => { w with keys := w.keys.drop 1, time := w.time + timeout.toNat }
    return key
  | .dimensions => do
    let size := (← get).sizes.headD (← get).size
    modify fun w => { w with size, sizes := w.sizes.drop 1 }
    return size
  | .lock path => do
    unless !(← get).locks.any (·.2 == path.toString) do throw "Already locked"
    let token := LockId.mk (← get).nextLock
    modify fun w => { w with nextLock := w.nextLock + 1, locks := w.locks.push (token, path.toString) }
    return token
  | .unlock token => do
    unless (← get).locks.any (·.1 == token) do throw "Unknown lock"
    modify fun w => { w with locks := w.locks.filter (·.1 != token) }

def handle (op : HostOp α) : StateM World (Except String α) := do
  let world ← get
  modify fun w => { w with trace := w.trace.push (label op) }
  if world.failAt == some world.trace.size then return .error "injected host failure"
  operation op

def run (program : Cli α) (world : World := {}) : Except String α × World :=
  (Cli.runWith handle program).run world

end LeanCloudTests.ConsoleModel
