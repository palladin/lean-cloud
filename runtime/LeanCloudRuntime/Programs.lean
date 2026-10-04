import LeanCloudRuntime.Program
import LeanCloudRuntime.Demo
import LeanCloudRuntime.Squares

namespace LeanCloudRuntime
open LeanCloud

private def sites (source : ProgramSource) (markers : Array (String × String)) : ProgramSource :=
  match source.locate markers with
  | .ok source => source
  | .error message => panic! message

def logSummary : CloudProgram Demo.Input BlobRef := {
  name := "log-summary", version := "v1", description := "Count ERROR lines in batches of global log files"
  run := Demo.workflow, sampleInput := some { Demo.input with pauseMs := 3000 }
  source := some (sites Demo.source #[
    ("parallel", "let counts ←"), ("resolveBlob", "let text ←"),
    ("readBlob", "let text ←"), ("analyze-batch", "Cloud.exec"), ("putBlob", "CloudBlob.putText")]) }

def sumSquares : CloudProgram (Array Nat) Nat := {
  name := "sum-squares", version := "v1", description := "Compute squares in parallel and sum their results"
  run := Squares.workflow, sampleInput := some #[1, 2, 3, 4, 5]
  source := some (sites Squares.source #[("parallel", "let squares ←"), ("square", "Cloud.pure")]) }

def programs : Registry := ⟨#[logSummary.register, sumSquares.register]⟩
end LeanCloudRuntime
