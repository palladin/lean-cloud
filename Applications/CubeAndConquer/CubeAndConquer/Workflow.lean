import CubeAndConquer.Model
import LeanCloud.Source

namespace CubeAndConquer
open LeanCloud

/-- All file/tool IO stays behind this boundary. Only small cube descriptions
and immutable artifact references cross replay boundaries. -/
structure Backend (m : Type → Type) where
  cube : Request → Cube → m Cubing
  conquer : Environment m → Request → Array Cube → m (Array CubeResult)
  verify : Environment m → Request → Array CubeResult → m (Array CubeResult)
  finish : Request → Array CubeResult → m Report

private def conquer [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request)
    (cubes : Array Cube) : Cloud m (Array CubeResult) := cloud {
  let solved ← Cloud.exec (fun env => backend.conquer env request cubes) "conquer"
  if solved.map (·.cube) != cubes then Cloud.fail "Solver returned different batch cubes"
  let checked ← Cloud.exec (fun env => backend.verify env request solved) "verify"
  if checked.map (·.cube) != cubes then Cloud.fail "Checker returned different batch cubes"
  return checked
}

/-- Batching affects cloud granularity; the executing worker separately chooses
its local concurrency from the live environment. -/
def batches (cubes : Array Cube) (size : Nat) : Array (Array Cube) :=
  let size := max 1 size
  (Array.range ((cubes.size + size - 1) / size)).map fun i =>
    cubes.extract (i * size) ((i + 1) * size)

/-- Each successful split adds at least one decision, so at most `depth` rounds
are needed. The actual path length enforces the total decision budget. -/
private def solve [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) :
    Nat → Cube → Cloud m (Array CubeResult)
  | 0, cube => conquer backend request #[cube]
  | rounds + 1, cube => cloud {
      if cube.length ≥ request.depth then
        conquer backend request #[cube]
      else
        let split ← Cloud.exec (fun _ => backend.cube request cube) "cube"
        match split with
        | .leaf => conquer backend request #[cube]
        | .finished result =>
            if result.cube != cube then Cloud.fail "Cuber returned a different parent cube"
            return #[result]
        | .split children =>
            match validateSplit cube (min request.splitDepth (request.depth - cube.length)) children with
            | .error reason => Cloud.fail reason
            | .ok () =>
                let children := children.map (cube ++ ·)
                let leaves := children.filter (·.length ≥ request.depth)
                let pending := children.filter (·.length < request.depth)
                let jobs := (batches leaves request.cubesPerJob).map (conquer backend request)
                  ++ pending.map (solve backend request rounds)
                let results ← Cloud.parallel jobs
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
