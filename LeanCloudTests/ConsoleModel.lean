import LeanCloudCli.Application

namespace LeanCloudTests.ConsoleModel
open Lean LeanCloud LeanCloudCli

/-- A pure host for the real CLI, with scripted HTTP, input, time and failures. -/
structure World where
  files : Array (String × String) := #[]
  directories : Array String := #["/work"]
  env : Option String := none
  envs : Array (String × String) := #[]
  lines : List String := []
  keys : List UInt32 := []
  stdout : String := ""
  stderr : String := ""
  clipboard : String := ""
  time : Nat := 0
  terminalAvailable : Bool := true
  terminal : Bool := false
  size : Nat × Nat := (120, 35)
  sizes : List (Nat × Nat) := []
  nextLock : Nat := 0
  nextId : Nat := 0
  locks : Array (LockId × String) := #[]
  trace : Array String := #[]
  failAt : Option Nat := none
  http : Option (String → String → Json → Except String Json) := none
  httpRequests : Array Json := #[]
  httpDelay : Nat := 0
  nextHttp : Nat := 0
  pendingHttp : Array (HttpId × Nat × Except String String) := #[]

def World.file (world : World) (path : System.FilePath) : Option String :=
  (world.files.find? (·.1 == path.toString)).map (·.2)

def World.save (world : World) (path : System.FilePath) (text : String) : World :=
  { world with files := (world.files.filter (·.1 != path.toString)).push (path.toString, text) }

def World.json [ToJson α] (world : World) (path : System.FilePath) (value : α) : World :=
  world.save path (toJson value).compress

private def label : HostOp α → String
  | .httpPost .. => "httpPost"
  | .httpStart .. => "httpStart" | .httpPoll .. => "httpPoll" | .httpCancel .. => "httpCancel"
  | .readFile .. => "readFile" | .writeFile .. => "writeFile"
  | .rename .. => "rename" | .exists .. => "exists" | .readDir .. => "readDir"
  | .removeTree .. => "removeTree"
  | .isDir .. => "isDir"
  | .createDir .. => "createDir" | .realPath .. => "realPath" | .currentDir => "currentDir"
  | .getEnv .. => "getEnv" | .pid => "pid" | .now => "now" | .sleep .. => "sleep"
  | .randomId => "randomId"
  | .write .. | .writeStyled .. => "write" | .flush => "flush" | .readLine => "readLine"
  | .enterTerminal => "enterTerminal" | .leaveTerminal => "leaveTerminal"
  | .key .. => "key" | .dimensions => "dimensions" | .lock .. => "lock" | .unlock .. => "unlock"
  | .copyClipboard .. => "copyClipboard"

private def exchange (url token body : String) : ExceptT String (StateM World) String := do
    let json ← liftExcept (Json.parse body)
    let some http := (← get).http | throw "Unexpected HTTP request"
    modify fun w => { w with httpRequests := w.httpRequests.push json }
    return (← liftExcept (http url token json)).compress

private def operation : HostOp α → ExceptT String (StateM World) α
  | .httpPost url token body => exchange url token body
  | .httpStart url token body => do
    let result ← observing (exchange url token body)
    let world ← get
    let id : HttpId := ⟨world.nextHttp⟩
    set { world with
      nextHttp := world.nextHttp + 1
      pendingHttp := world.pendingHttp.push (id, world.time + world.httpDelay, result) }
    return id
  | .httpPoll id => do
    let world ← get
    let some (_, due, result) := world.pendingHttp.find? (·.1 == id) | throw "Unknown HTTP request"
    if world.time < due then return none
    set { world with pendingHttp := world.pendingHttp.filter (·.1 != id) }
    return some result
  | .httpCancel id => modify fun w => { w with pendingHttp := w.pendingHttp.filter (·.1 != id) }
  | .readFile path => do
    let some text := (← get).file path | throw s!"Missing file: {path}"
    return text
  | .removeTree path => modify fun world =>
    let retained (name : String) := name != path.toString && !name.startsWith (path.toString ++ "/")
    { world with files := world.files.filter (retained ∘ Prod.fst), directories := world.directories.filter retained }
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
  | .randomId => do
    let value := (← get).nextId
    modify fun w => { w with nextId := value + 1 }
    return s!"request-{value}"
  | .now => return (← get).time
  | .sleep ms => modify fun w => { w with time := w.time + ms.toNat }
  | .write text stderr => modify fun w =>
    if stderr then { w with stderr := w.stderr ++ text } else { w with stdout := w.stdout ++ text }
  | .writeStyled line => modify fun w => { w with stdout := w.stdout ++ Styled.plain line ++ "\n" }
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
  | .copyClipboard text => modify fun w => { w with clipboard := text }
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
