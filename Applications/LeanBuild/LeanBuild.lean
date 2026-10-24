import LeanBuild.Tools
import LeanCloud.Program

namespace LeanBuild

def program (environment : IO (Tools × LeanCloudRuntime.ObjectStore)) :
    LeanCloud.CloudProgram Request Report := {
  name := "lean-build"
  version := "v4"
  description := "Build GitHub Lean projects in parallel, with optional proof checking"
  run := fun request => workflow {
    prepare := fun env request => do
      let (tools, store) ← environment
      (tools.backend store).prepare env request
    build := fun env request plan modules completed => do
      let (tools, store) ← environment
      (tools.backend store).build env request plan modules completed
    finish := fun env request plan completed => do
      let (tools, store) ← environment
      (tools.backend store).finish env request plan completed
    check := fun env request plan built => do
      let (tools, store) ← environment
      (tools.backend store).check env request plan built } request }

end LeanBuild
