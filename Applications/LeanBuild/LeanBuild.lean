import LeanBuild.Tools
import LeanCloud.Program

namespace LeanBuild

def program (environment : IO (Tools × LeanCloudRuntime.ObjectStore)) :
    LeanCloud.CloudProgram Request Report := {
  name := "lean-build"
  version := "v2"
  description := "Build GitHub Lean projects in parallel, with optional proof checking"
  run := fun request => workflow {
    prepare := fun request => do
      let (tools, store) ← environment
      tools.prepare store request
    build := fun request plan module completed => do
      let (tools, store) ← environment
      tools.build store request plan module completed
    finish := fun request plan completed => do
      let (tools, store) ← environment
      tools.finish store request plan completed
    check := fun request plan built => do
      let (tools, store) ← environment
      tools.check store request plan built } request }

end LeanBuild
