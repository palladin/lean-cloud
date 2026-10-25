import CubeAndConquer
import LeanCloudRuntime.Run
import LeanCloud.DirectInterpreter

namespace CubeAndConquer.Command
open Lean LeanCloud LeanCloudRuntime

private def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

/-- Accept either the runtime node configuration or just its blob configuration.
Credentials remain local to this utility and never enter the submitted request. -/
def objects (path : System.FilePath) : IO ObjectStore := do
  let json : Json ← readJson path
  let config : Storage.Config ← IO.ofExcept (fromJson? ((json.getObjVal? "blobs").toOption.getD json))
  IO.ofExcept config.validate
  return config.objects

private def writeNew (path : System.FilePath) (text : String) : IO Unit := do
  if path.toString == "-" then IO.println text; return
  unless !(← path.pathExists) do throw (IO.userError "Output already exists")
  IO.FS.writeFile path text

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["prepare", config, source, output] =>
      let store ← objects config
      store.ensureContainer
      discard <| Dimacs.scan source
      let limit ← match ← IO.getEnv "LEAN_CLOUD_SAT_INPUT_BYTES" with
        | none => pure ({} : Limits).inputBytes
        | some text => match text.toNat? with | some n => pure n | none => throw (IO.userError "Invalid input byte limit")
      let request : Request := { cnf := ← Files.upload store source limit }
      writeNew output (toJson request).pretty
    | ["download", config, refPath, output] =>
      let store ← objects config
      let ref : FileRef ← readJson refPath
      unless output == "-" || !(← (System.FilePath.mk output).pathExists) do throw (IO.userError "Output already exists")
      -- Check all chunks/hash before publishing a destination filename.
      IO.FS.withTempFile fun _ path => do
        Files.download store ref path ref.size
        let input ← IO.FS.Handle.mk path .read
        let destination ← if output == "-" then IO.getStdout else pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk output .write))
        repeat
          let bytes ← input.read 65536
          if bytes.isEmpty then break
          destination.write bytes
        destination.flush
    | ["verify", config, reportPath] =>
      let report : Report ← readJson reportPath
      let store ← objects config
      let tools ← Tools.fromEnvironment
      let actual ← tools.verifyBundle store report.bundle
      unless actual == report.outcome do throw (IO.userError "Report differs from verified evidence")
      IO.println (toJson actual).compress
      if actual == .inconclusive then return 2
    | ["run", config, requestPath] =>
      let store ← objects config
      let tools ← Tools.fromEnvironment
      let request : Request ← readJson requestPath
      let outcome ← (DirectInterpreter.interpret store.executionContext (workflow (backend tools store)) request).run
      match outcome with
      | .ok report => IO.println (toJson report).pretty
      | .error error => throw (IO.userError error.message)
    | _ => throw (IO.userError "Usage: sat_files prepare CONFIG CNF INPUT.json | download CONFIG REF.json FILE | verify CONFIG REPORT.json | run CONFIG INPUT.json")
    return 0
  catch error => IO.eprintln s!"{error}"; return 1

end CubeAndConquer.Command
