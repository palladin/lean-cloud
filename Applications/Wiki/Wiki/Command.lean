import Wiki
import Wiki.Import
import LeanCloudRuntime.Run
import LeanCloud.DirectInterpreter

namespace Wiki.Command
open Lean LeanCloud LeanCloudRuntime

def decode [FromJson α] (path : String) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

def write [ToJson α] (path : String) (value : α) : IO Unit :=
  IO.FS.writeFile path ((toJson value).pretty ++ "\n")

private def run [FromJson ι] [ToJson α] (store : ObjectStore)
    (program : ι → Cloud IO α) (input output : String) : IO Unit := do
  let result ← (DirectInterpreter.interpret store.executionContext program (← decode input)).run
  match result with
  | .error e => throw (IO.userError e.message)
  | .ok value => write output value

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["import", config, dump, index, output] =>
      let cfg ← Config.load config
      cfg.objects.ensureContainer
      write output (← Import.multistream cfg.objects dump index)
    | ["import-xml", config, dump, output] =>
      let cfg ← Config.load config
      cfg.objects.ensureContainer
      write output (← Import.document cfg.objects dump)
    | ["download", config, refFile, output] =>
      let cfg ← Config.load config
      let ref : FileRef ← decode refFile
      if output == "-" then IO.print (← Files.readText cfg.objects ref maxShardBytes)
      else Files.download cfg.objects ref output maxShardBytes
    | ["run", config, program, input, output] =>
      let cfg ← Config.load config
      let b := backend cfg.objects
      match program with
      | "wiki-prepare" => run cfg.objects (prepare b) input output
      | "wiki-count" => run cfg.objects (count b) input output
      | "wiki-grep" => run cfg.objects (grep b) input output
      | _ => throw (IO.userError "Unknown Wiki program")
    | _ =>
      IO.eprintln "Usage: files import CONFIG DUMP.bz2 INDEX.txt[.bz2] REQUEST.json | files import-xml CONFIG DUMP.xml[.bz2] REQUEST.json | files download CONFIG FILE_REF OUTPUT | files run CONFIG PROGRAM INPUT OUTPUT"
      return 2
    return 0
  catch error => IO.eprintln s!"{error}"; return 1
end Wiki.Command
