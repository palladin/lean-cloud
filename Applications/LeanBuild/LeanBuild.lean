import LeanBuild.Tools
import LeanCloud.Program

namespace LeanBuild

def program (environment : IO (Tools × LeanCloudRuntime.ObjectStore)) :
    LeanCloud.CloudProgram Request Report := {
  name := "lean-build"
  version := "v6"
  description := "Build GitHub Lean projects in parallel and publish their artifacts"
  run := fun request => workflow {
    prepare := fun env request => do
      let (tools, store) ← environment
      (tools.backend store).prepare env request
    start := Builders.seed
    builder := fun env request plan => do
      let (tools, store) ← environment
      (tools.backend store).builder env request plan
    results := Builders.results
    finish := fun env request plan completed => do
      let (tools, store) ← environment
      (tools.backend store).finish env request plan completed } request }

end LeanBuild
