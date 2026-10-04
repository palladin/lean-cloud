import LeanCloudRuntime.Program
import LeanCloudRuntime.Demo
import LeanCloudRuntime.Squares

namespace LeanCloudRuntime
open LeanCloud

def logSummary : CloudProgram Demo.Input BlobRef := {
  name := "log-summary", version := "v1", description := "Count ERROR lines in batches of global log files"
  run := Demo.workflow, sampleInput := some { Demo.input with pauseMs := 3000 }
}

def sumSquares : CloudProgram (Array Nat) Nat := {
  name := "sum-squares", version := "v1", description := "Compute squares in parallel and sum their results"
  run := Squares.workflow, sampleInput := some #[1, 2, 3, 4, 5]
}

def programs : Registry := ⟨#[logSummary.register, sumSquares.register]⟩
end LeanCloudRuntime
