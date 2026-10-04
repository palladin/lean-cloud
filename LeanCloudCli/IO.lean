import LeanCloudCli.Effects
import LeanCloudCli.Native

namespace LeanCloudCli

private structure Resources where
  locks : Array (Option Native.Lock) := #[]
  terminal : Bool := false
  processes : Array (Option Native.Process) := #[]

/-- Only this handler touches the host. Process arguments remain separate argv entries. -/
private def handle (resources : IO.Ref Resources) : HostOp α → IO α
  | .process command args input => do
    let output ← IO.Process.output { cmd := command, args } input
    return ⟨output.exitCode, output.stdout, output.stderr⟩
  | .startProcess command args => do
    let child ← Native.startProcess command args
    let state ← resources.get
    resources.set { state with processes := state.processes.push (some child) }
    return ⟨state.processes.size⟩
  | .pollProcess token timeout => do
    let some child := (← resources.get).processes[token.value]? >>= id
      | throw (IO.userError "Unknown or closed process")
    Native.pollProcess child timeout
  | .closeProcess token => do
    let some child := (← resources.get).processes[token.value]? >>= id
      | throw (IO.userError "Unknown or closed process")
    Native.closeProcess child
    resources.modify fun state => { state with processes := state.processes.set! token.value none }
  | .readFile path => IO.FS.readFile path
  | .writeFile path text => IO.FS.writeFile path text
  | .appendFile path text => IO.FS.withFile path .append (fun file => file.putStr text)
  | .rename source target => IO.FS.rename source target
  | .exists path => path.pathExists
  | .readDir path => return (← path.readDir).map (·.fileName)
  | .isDir path => path.isDir
  | .createDir path => IO.FS.createDirAll path
  | .realPath path => IO.FS.realPath path
  | .currentDir => IO.Process.getCurrentDir
  | .getEnv name => IO.getEnv name
  | .pid => IO.Process.getPID
  | .now => IO.monoMsNow
  | .sleep milliseconds => IO.sleep milliseconds
  | .write text stderr => do
    let stream ← if stderr then IO.getStderr else IO.getStdout
    stream.putStr text
  | .writeStyled line => do (← IO.getStdout).putStr (Styled.plain line ++ "\n")
  | .flush => do (← IO.getStdout).flush; (← IO.getStderr).flush
  | .readLine => do (← IO.getStdin).getLine
  | .enterTerminal => do
    let active ← Native.enter
    if active then resources.modify fun state => { state with terminal := true }
    return active
  | .leaveTerminal => do
    Native.leave
    resources.modify fun state => { state with terminal := false }
  | .key timeout => Native.key timeout
  | .dimensions => return ((← Native.columns).toNat, (← Native.rows).toNat)
  | .lock path => do
    let lock ← Native.lock path.toString
    let state ← resources.get
    resources.set { state with locks := state.locks.push (some lock) }
    return ⟨state.locks.size⟩
  | .unlock token => do
    let state ← resources.get
    let some lock := state.locks[token.value]? >>= id
      | throw (IO.userError "Unknown or released CLI lock")
    Native.unlock lock
    resources.modify fun state => { state with locks := state.locks.set! token.value none }

/-- Host errors return through Eff so the CLI's error and cleanup paths are shared
    by real execution and tests. The outer guard also releases abandoned resources. -/
def withHostIO (use : ({α : Type} → HostOp α → IO (Except String α)) → IO β) : IO β := do
  let resources ← IO.mkRef ({} : Resources)
  try
    use (fun operation => do
      try return .ok (← handle resources operation)
      catch error => return .error error.toString)
  finally
    let state ← resources.get
    for child in state.processes do
      if let some child := child then Native.closeProcess child
    if state.terminal then Native.leave
    for lock in state.locks do
      if let some lock := lock then Native.unlock lock

def Cli.runIO (program : Cli α) : IO (Except String α) :=
  withHostIO (fun handle => Cli.runWith handle program)

end LeanCloudCli
