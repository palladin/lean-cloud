import LeanCloud.Source

namespace LeanCloudRuntime.Squares
open LeanCloud

def workflow (numbers : Array Nat) : Cloud IO Nat := cloud {
  let squares ← Cloud.parallel (numbers.map fun n => cloud {
    Cloud.pure (fun _ => n * n) "square"
  })
  return squares.foldl (· + ·) 0
}

def source : ProgramSource := cloud_source%
end LeanCloudRuntime.Squares
