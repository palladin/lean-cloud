import LeanVerify.Tools
import LeanCloud.Program

namespace LeanVerify

def program (environment : IO (Tools × LeanCloudRuntime.ObjectStore)) :
    LeanCloud.CloudProgram Request Report := {
  name := "lean-verify"
  version := "v1"
  description := "Check a GitHub Lean project in parallel by module"
  run := fun request => workflow {
    prepare := fun request => do
      let (tools, store) ← environment
      tools.prepare store request
    check := fun request plan module completed => do
      let (tools, store) ← environment
      tools.check store request plan module completed } request }

end LeanVerify
