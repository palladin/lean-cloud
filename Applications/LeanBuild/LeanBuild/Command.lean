import LeanBuild
import LeanCloudRuntime.Run
import LeanCloud.DirectInterpreter

namespace LeanBuild.Command
open Lean LeanCloudRuntime

private def decode [FromJson α] (path : String) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

/-- An application utility, separate from the cloud console. Use an existing
storage configuration to run locally or download an immutable artifact. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["run", config, input, output] =>
      let cfg ← Config.load config
      let tools ← Tools.fromEnvironment
      let request : Request ← decode input
      IO.ofExcept request.validate
      let conn ← LeanLinq.Sqlite.connect ":memory:"
      let outcome ← try
        WorkQueueStore.initializeSchema conn
        let scope := s!"direct-{← IO.monoNanosNow}"
        let context := cfg.objects.executionContextFor scope
        let queues := WorkQueueStore.provider conn (← Std.Mutex.new ()) scope
        let context := { context with queues := ⟨fun name =>
          (queues.open name).map (fun action => LeanCloud.captureIO (liftM action))⟩ }
        (LeanCloud.DirectInterpreter.interpret context (workflow (tools.backend cfg.objects)) request).run
      finally conn.close
      let .ok report := outcome
        | throw (IO.userError "Build workflow failed")
      IO.FS.writeFile output (toJson report).pretty
      return if report.success then 0 else 1
    | ["download", config, refFile, output] =>
      let cfg ← Config.load config
      let ref : FileRef ← decode refFile
      if output == "-" then
        IO.print (← Files.readText cfg.objects ref Files.metadataLimit)
      else Files.download cfg.objects ref output (16 * 1024 * 1024 * 1024)
      return 0
    | ["restore", config, refFile, directory] =>
      let cfg ← Config.load config
      let ref : FileRef ← decode refFile
      let destination := System.FilePath.mk directory
      if ← destination.pathExists then throw (IO.userError "Restore requires a new directory")
      let manifest : Bundle.Manifest ← Files.readJson cfg.objects ref
      IO.FS.createDirAll destination
      Bundle.restore cfg.objects destination manifest (16 * 1024 * 1024 * 1024)
      return 0
    | _ =>
      IO.eprintln "Usage: files run CONFIG INPUT REPORT | files download CONFIG FILE_REF OUTPUT | files restore CONFIG MANIFEST_REF DIRECTORY"
      return 2
  catch error => IO.eprintln s!"{error}"; return 1

end LeanBuild.Command
