import LeanVerify
import LeanCloudRuntime.Run
import LeanCloud.DirectInterpreter

namespace LeanVerify.Command
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
      let .ok report ← (LeanCloud.DirectInterpreter.interpret cfg.objects.storage
        (workflow (tools.backend cfg.objects)) request).run
        | throw (IO.userError "Verification workflow failed")
      IO.FS.writeFile output (toJson report).pretty
      return if report.success then 0 else 1
    | ["download", config, refFile, output] =>
      let cfg ← Config.load config
      let ref : FileRef ← decode refFile
      if output == "-" then
        IO.print (← Files.readText cfg.objects ref Files.metadataLimit)
      else Files.download cfg.objects ref output (16 * 1024 * 1024 * 1024)
      return 0
    | _ =>
      IO.eprintln "Usage: files run CONFIG INPUT REPORT | files download CONFIG FILE_REF OUTPUT"
      return 2
  catch error => IO.eprintln s!"{error}"; return 1

end LeanVerify.Command
