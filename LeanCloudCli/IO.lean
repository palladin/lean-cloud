import LeanCloudCli.Effects
import LeanCloudCli.Native
import LeanCloudCli.Http

namespace LeanCloudCli

private structure Resources where
  locks : Array (Option Native.Lock) := #[]
  terminal : Bool := false
  nextHttp : Nat := 0
  http : Std.HashMap HttpId (Task (Except IO.Error String)) := {}

private def randomHex (count : Nat) : IO String := IO.FS.withFile "/dev/urandom" .read fun file => do
  let bytes ← file.read count.toUSize
  unless bytes.size == count do throw (IO.userError "Could not obtain secure random bytes")
  let digits := "0123456789abcdef".toList.toArray
  return String.ofList (bytes.data.toList.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

/-- Only this handler touches HTTP, local client files, and the terminal. -/
private def handle (resources : IO.Ref Resources) : HostOp α → IO α
  | .httpPost url token body => Http.post url token body
  | .httpStart url token body => do
    let task ← IO.asTask (Http.post url token body) .dedicated
    let state ← resources.get
    let id : HttpId := ⟨state.nextHttp⟩
    resources.set { state with nextHttp := state.nextHttp + 1, http := state.http.insert id task }
    return id
  | .httpPoll id => do
    let some task := (← resources.get).http[id]?
      | throw (IO.userError "Unknown HTTP request")
    unless ← IO.hasFinished task do return none
    resources.modify fun state => { state with http := state.http.erase id }
    return some (task.get.mapError toString)
  | .httpCancel id => do
    if let some task := (← resources.get).http[id]? then IO.cancel task
    resources.modify fun state => { state with http := state.http.erase id }
  | .readFile path => IO.FS.readFile path
  | .writeFile path text => IO.FS.writeFile path text
  | .rename source target => IO.FS.rename source target
  | .removeTree path => do
    let metadata ← try some <$> path.symlinkMetadata catch
      | .noFileOrDirectory .. => pure none
      | error => throw error
    if let some metadata := metadata then
      if metadata.type == .dir then IO.FS.removeDirAll path
      else IO.FS.removeFile path
  | .exists path => path.pathExists
  | .readDir path => return (← path.readDir).map (·.fileName)
  | .isDir path => path.isDir
  | .createDir path => IO.FS.createDirAll path
  | .realPath path => IO.FS.realPath path
  | .currentDir => IO.Process.getCurrentDir
  | .getEnv name => IO.getEnv name
  | .pid => IO.Process.getPID
  | .randomId => randomHex 16
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
  | .copyClipboard text => do
    let (command, args) ← if System.Platform.isOSX then pure ("pbcopy", #[])
      else if (← IO.getEnv "WAYLAND_DISPLAY").isSome then pure ("wl-copy", #[])
      else pure ("xclip", #["-selection", "clipboard"])
    let output ← IO.Process.output { cmd := command, args } (some text)
    unless output.exitCode == 0 do throw (IO.userError s!"Clipboard copy failed: {output.stderr.trimAscii}")
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
    for (_, task) in state.http.toArray do IO.cancel task
    if state.terminal then Native.leave
    for lock in state.locks do
      if let some lock := lock then Native.unlock lock

def Cli.runIO (program : Cli α) : IO (Except String α) :=
  withHostIO (fun handle => Cli.runWith handle program)

end LeanCloudCli
