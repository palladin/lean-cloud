import LeanCloudTests.ConsoleRemote
import LeanCloudTests.PoolWorkload
import LeanCloudTests.Support
import Std.Async.TCP

/-! Deployment is test setup, outside the HTTP-only console. Fault injection
uses Docker explicitly; every workflow operation uses the real client API. -/
namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

def external (command : String) (args : Array String) : IO String := do
  let output ← IO.Process.output { cmd := command, args }
  unless output.exitCode == 0 do throw (IO.userError (output.stderr ++ output.stdout))
  return output.stdout.trimAscii.toString

def cli (action : Cli α) : IO α := do IO.ofExcept (← action.runIO)

structure Fixture where
  directory : System.FilePath
  context : Context
  url : String

def Fixture.compose (f : Fixture) (args : Array String) : IO String :=
  external "docker" (#["compose", "-p", f.context.project, "-f", (f.directory / "compose.json").toString] ++ args)

def Fixture.helper (f : Fixture) (action : String) (args : Array String := #[]) : IO Unit := do
  discard <| external "bash" (#["deploy/local.sh", action, f.directory.toString] ++ args)

def Fixture.refresh (f : Fixture) : IO Unit := do
  let address ← f.compose #["port", "scheduler", "8080"]
  let connection : Client.Connection := {
    url := "http://" ++ address
    deployment := f.context.project
    tokenEnv := "LEAN_CLOUD_TOKEN"
    tokenFile := some (f.directory / "client.token").toString }
  cli <| saveJson (f.context.home / "connection.json") connection

def Fixture.command (f : Fixture) (args : List String) : IO Unit :=
  cli (discard (LeanCloudCli.command f.context args))

def Fixture.wait (f : Fixture) (id : String) : IO Exit :=
  cli do awaitOutcome f.context (← f.context.loadRun id) ((← request .now) + 120000)

private def availablePort : IO UInt16 := do
  let socket ← Std.Async.TCP.Socket.Server.mk
  socket.bind (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
  socket.listen 1
  let .v4 address ← socket.getSockName | throw (IO.userError "Expected a loopback IPv4 socket")
  return address.port

def withFixture (suite image : String) (action : Fixture → IO Unit) : IO Unit := do
  let root ← IO.Process.getCurrentDir
  let name := s!"lean-cloud-{suite}-{← IO.Process.getPID}"
  let directory := root / ".lean-cloud" / name
  -- Assign a fixed port for this fixture. Docker may change an ephemeral port
  -- on an automatic node restart, stranding the client during crash recovery.
  let port ← availablePort
  discard <| external "bash" #["deploy/local.sh", "init", directory.toString, image, name, "3", toString port]
  let ctx : Context := ⟨directory / "client", name⟩
  let f : Fixture := ⟨directory, ctx, ""⟩
  try
    f.helper "up"
    let address ← f.compose #["port", "scheduler", "8080"]
    let url := "http://" ++ address
    IO.FS.createDirAll ctx.home
    cli <| saveJson (ctx.home / "connection.json") ({
      url, deployment := name, tokenEnv := "LEAN_CLOUD_TOKEN", tokenFile := some (directory / "client.token").toString } : Client.Connection)
    action { f with url }
  catch error =>
    let logs ← try f.compose #["logs", "--no-color", "--tail", "300"] catch _ => pure "Logs unavailable"
    IO.FS.writeFile (directory / "failure.log") logs
    throw error
  finally
    IO.println s!"Cleaning deployment {name}…"
    (← IO.getStdout).flush
    let started ← IO.monoMsNow
    f.helper "clean" #["--yes"]
    IO.println s!"Deployment cleanup finished in {(← IO.monoMsNow) - started} ms."
    (← IO.getStdout).flush


end LeanCloudTests.ConsoleRuntime
