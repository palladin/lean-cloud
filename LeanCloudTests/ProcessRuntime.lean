import LeanCloudCli.IO
import LeanCloudCli.Process

namespace LeanCloudTests.ProcessRuntime
open LeanCloudCli

private def require (condition : Bool) (message : String) : Cli Unit :=
  unless condition do throw message

private partial def collect (token : ProcessId) (fuel : Nat := 500)
    (out err : ByteArray := ByteArray.empty) (early := false) : Cli (ProcessChunk × Bool) := do
  if fuel == 0 then throw "Process test timed out"
  let chunk ← request (.pollProcess token 20)
  require (chunk.stdout.size ≤ 8192 && chunk.stderr.size ≤ 8192) "Unbounded native pipe read"
  let early := early || (chunk.exitCode.isNone && (!chunk.stdout.isEmpty || !chunk.stderr.isEmpty))
  let out := out ++ chunk.stdout
  let err := err ++ chunk.stderr
  if chunk.exitCode.isSome then return (⟨out, err, chunk.exitCode⟩, early)
  collect token (fuel - 1) out err early

private partial def ready (token : ProcessId) (fuel : Nat := 500) : Cli Unit := do
  if fuel == 0 then throw "Child did not become ready"
  let chunk ← request (.pollProcess token 20)
  if !chunk.stdout.isEmpty then return
  if chunk.exitCode.isSome then throw "Child exited before readiness"
  ready token (fuel - 1)

private def checkOutput (self : String) (mode : String) (expectedOut expectedErr : ByteArray)
    (code : UInt32) : Cli Unit := do
  let token ← request (.startProcess self #["--child", mode])
  try
    let (output, early) ← collect token
    require early "Native backend buffered output until exit"
    require (output.stdout == expectedOut && output.stderr == expectedErr) "Pipe bytes were lost or changed"
    require (output.exitCode == some code) "Wrong child exit code"
  finally request (.closeProcess token)

/-- Fixtures are Lean subprocesses, including a grandchild in the owned process group. -/
def child (mode : String) (marker : String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match mode with
  | "stream" =>
    for byte in "first λ🙂\n".toUTF8.data do
      out.write (ByteArray.mk #[byte]); out.flush
      IO.sleep 3
    err.putStr "warning\n"; err.flush
    IO.sleep 150
    out.putStr "last"; out.flush
    return 0
  | "flood" =>
    for _ in [:64] do
      out.write (ByteArray.mk (Array.replicate 8192 65))
      err.write (ByteArray.mk (Array.replicate 8192 66))
    return 7
  | "mark" =>
    IO.sleep 1500
    IO.FS.writeFile marker "descendant survived"
    return 0
  | "group" | "orphan" =>
    let _ ← IO.Process.spawn { cmd := (← IO.appPath).toString, args := #["--child", "mark", marker] }
    out.putStr "ready\n"; out.flush
    if mode == "group" then IO.sleep 60000
    return 0
  | _ => throw (IO.userError "Unknown fixture")

def run : IO Unit := do
  let self := (← IO.appPath).toString
  let tests : Cli Unit := do
    checkOutput self "stream" "first λ🙂\nlast".toUTF8 "warning\n".toUTF8 0
    checkOutput self "flood" (ByteArray.mk (Array.replicate (8192 * 64) 65))
      (ByteArray.mk (Array.replicate (8192 * 64) 66)) 7
    let missing ← observing (request (.startProcess "/does-not-exist/lean-cloud-test" #[]))
    require missing.toOption.isNone "Missing executable was accepted"
    let invalid ← observing (request (.startProcess self #["bad\x00argument"]))
    require invalid.toOption.isNone "NUL in argv was silently truncated"
  match ← Cli.runIO tests with
  | .error error => throw (IO.userError error)
  | .ok () => pure ()
  -- Exercise the real append handler, decoder, and log path on a streamed child.
  let logDir := (← IO.Process.getCurrentDir) / ".lean-cloud" / s!"logging-test-{← IO.Process.getPID}"
  IO.FS.createDirAll logDir
  let log := logDir / "output.log"
  try
    match ← Cli.runIO (Process.runLogged self #["--child", "stream"] log) with
    | .error error => throw (IO.userError error)
    | .ok () => pure ()
    let text ← IO.FS.readFile log
    -- stdout and stderr have independent pipes, so their relative order may vary.
    if (text.splitOn "first λ🙂\n").length != 2 || (text.splitOn "warning\n").length != 2 ||
        !text.endsWith "last" then
      throw (IO.userError s!"Incomplete saved output: {text}")
  finally
    if ← log.pathExists then IO.FS.removeFile log
    IO.FS.removeDir logDir
  for scenario in ["explicit", "outer", "orphan", "signal"] do
    let directory := (← IO.Process.getCurrentDir) / ".lean-cloud" / s!"process-test-{← IO.Process.getPID}"
    IO.FS.createDirAll directory
    let marker := directory / scenario
    let test : Cli Unit := do
      let mode := if scenario == "orphan" then "orphan" else "group"
      let token ← request (.startProcess self #["--child", mode, marker.toString])
      ready token
      if scenario == "orphan" then request (.sleep 100)
      if scenario == "signal" then
        let pid ← request .pid
        discard <| request (.process "/bin/kill" #["-INT", toString pid] none)
        let stopped ← observing (request (.pollProcess token 20))
        require stopped.toOption.isNone "SIGINT did not interrupt process polling"
      if scenario != "outer" then request (.closeProcess token)
      -- Otherwise withHostIO must close the unclaimed process when the handler exits.
    match ← Cli.runIO test with
    | .error error => throw (IO.userError error)
    | .ok () => pure ()
    IO.sleep 1800
    if ← marker.pathExists then throw (IO.userError "Process cleanup left a live grandchild")
    IO.FS.removeDir directory
  -- A cancelled process must not poison the signal state of a later command.
  match ← Cli.runIO (checkOutput self "stream" "first λ🙂\nlast".toUTF8 "warning\n".toUTF8 0) with
  | .error error => throw (IO.userError error)
  | .ok () => pure ()
  IO.println "Process tests passed: incremental bytes, saved logs, both pipes beyond capacity, exit codes, invalid argv, SIGINT recovery, and process-group cleanup."

end LeanCloudTests.ProcessRuntime

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--child", mode] => LeanCloudTests.ProcessRuntime.child mode ""
  | ["--child", mode, marker] => LeanCloudTests.ProcessRuntime.child mode marker
  | [] =>
    try LeanCloudTests.ProcessRuntime.run; return 0
    catch error => IO.eprintln error; return 1
  | _ => return 2
