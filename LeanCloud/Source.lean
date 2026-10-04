import LeanCloud.Program
import Lean.Elab.Term

namespace LeanCloud
open Lean Elab Term

/-- Bundle the source file at compilation. Labels are unique source fragments;
missing or ambiguous fragments are rejected instead of highlighting a guessed line. -/
def ProgramSource.locate (source : ProgramSource) (markers : Array (String × String)) : Except String ProgramSource := do
  let lines := source.text.splitOn "\n" |>.toArray
  let sites ← markers.mapM fun (operation, marker) => do
    let found := (Array.range lines.size).filter fun i => (lines[i]!.splitOn marker).length > 1
    match found.toList with
    | [index] => return { operation, line := index + 1 : SourceSite }
    | _ => throw s!"Source marker must occur exactly once: {marker}"
  return { source with sites }

elab "cloud_source%" : term => do
  let file ← getFileName
  let source ← IO.FS.readFile file
  let file := System.FilePath.mk file |>.fileName |>.getD file
  let file := Syntax.mkStrLit file
  let source := Syntax.mkStrLit source
  elabTerm (← `({ file := $file, text := $source : LeanCloud.ProgramSource })) none

end LeanCloud
