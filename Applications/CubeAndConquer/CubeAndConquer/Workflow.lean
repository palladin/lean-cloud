import CubeAndConquer.Model
import LeanCloud.Source

namespace CubeAndConquer
open LeanCloud

/-- All file/tool IO stays behind this boundary. Only small cube descriptions
and immutable artifact references cross replay boundaries. -/
structure Backend (m : Type → Type) where
  cube : Request → Cube → m Cubing
  conquer : Request → Cube → m CubeResult
  verify : Request → CubeResult → m CubeResult
  finish : Request → Array CubeResult → m Report

private def conquer [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request)
    (cube : Cube) : Cloud m (Array CubeResult) := cloud {
  let solved ← Cloud.exec (fun _ => backend.conquer request cube) "conquer"
  let checked ← Cloud.exec (fun _ => backend.verify request solved) "verify"
  return #[checked]
}

/-- Each successful split adds at least one decision, so at most `depth` rounds
are needed. The actual path length enforces the total decision budget. -/
private def solve [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) :
    Nat → Cube → Cloud m (Array CubeResult)
  | 0, cube => conquer backend request cube
  | rounds + 1, cube => cloud {
      if cube.length ≥ request.depth then
        conquer backend request cube
      else
        let split ← Cloud.exec (fun _ => backend.cube request cube) "cube"
        match split with
        | .leaf => conquer backend request cube
        | .finished result =>
            if result.cube != cube then Cloud.fail "Cuber returned a different parent cube"
            return #[result]
        | .split children =>
            match validateSplit cube (min request.splitDepth (request.depth - cube.length)) children with
            | .error reason => Cloud.fail reason
            | .ok () =>
                let results ← Cloud.parallel $ (children.map fun child => cloud {
                  solve backend request rounds (cube ++ child)
                })
                return results.flatten
    }

def workflow [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) : Cloud m Report := cloud {
  match request.validate with
  | .ok () => pure ()
  | .error reason => Cloud.fail reason
  let results ← solve backend request request.depth []
  Cloud.exec (fun _ => backend.finish request results) "publish result"
}

end CubeAndConquer
