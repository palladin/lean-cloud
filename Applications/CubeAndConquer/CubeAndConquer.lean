import CubeAndConquer.Workflow
import CubeAndConquer.Tools

namespace CubeAndConquer
open LeanCloudRuntime

instance : LeanCloud.Codec Request := LeanCloud.jsonCodec _ "cube-and-conquer/request/v4"

def backend (tools : Tools) (store : ObjectStore) : Backend IO where
  cube := tools.cube store
  conquer := tools.conquerBatch store
  verify := tools.verifyBatch store
  finish := tools.finish store

/-- The registry can be inspected without credentials. Only workers evaluate
this action, obtaining their already-configured object store and tools. -/
def program (environment : IO (Tools × ObjectStore)) : LeanCloud.CloudProgram Request Report := {
  name := "cube-and-conquer"
  version := "v4"
  description := "Blob CNF → checked SAT model or verified per-cube DRAT proof bundle"
  run := fun request => workflow {
    cube := fun request parent => do let (tools, store) ← environment; tools.cube store request parent
    conquer := fun env request cubes => do let (tools, store) ← environment; tools.conquerBatch store env request cubes
    verify := fun env request results => do let (tools, store) ← environment; tools.verifyBatch store env request results
    finish := fun request results => do let (tools, store) ← environment; tools.finish store request results
  } request
}

end CubeAndConquer
