import LeanCloudTests.ConsoleRemote
import LeanCloudTests.PoolWorkload
import LeanCloudTests.Support

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

def withFixture (suite image : String) (action : Fixture → IO Unit) : IO Unit := do
  let root ← IO.Process.getCurrentDir
  let name := s!"lean-cloud-{suite}-{← IO.Process.getPID}"
  let directory := root / ".lean-cloud" / name
  discard <| external "bash" #["deploy/local.sh", "init", directory.toString, image, name, "3", "0"]
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
    f.helper "clean" #["--yes"]


end LeanCloudTests.ConsoleRuntime
