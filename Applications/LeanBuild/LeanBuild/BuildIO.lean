import LeanBuild.BuildError
import LeanCloudRuntime.Parallel

namespace LeanBuild

abbrev BuildIO := ExceptT BuildError IO

namespace BuildIO

/-- Classify at the capability boundary, never by inspecting an error string. -/
def capture (classify : String → BuildError) (action : IO α) : BuildIO α := ExceptT.mk do
  try return .ok (← action) catch error => return .error (classify error.toString)

/-- Also close scopes if an unexpected IO exception escapes a handler. -/
def outcome (action : BuildIO α) : IO (Except BuildError α) := do
  try action.run catch error => return .error (.tool error.toString)

def inspect (action : BuildIO α) : BuildIO (Except BuildError α) := ExceptT.mk do
  return .ok (← outcome action)

def toIO (action : BuildIO α) : IO α := do
  IO.ofExcept (← outcome action)

/-- Adapt the existing bounded IO pools without losing typed errors. The IO
exception only stops pool admission; the original error is stored separately.
The pool joins every started task before returning. -/
private def pool (run : ({α : Type} → BuildIO α → IO α) → IO β) : BuildIO β := ExceptT.mk do
  let failure ← Std.Mutex.new (none : Option BuildError)
  let execute : {α : Type} → BuildIO α → IO α := fun action => do
    match ← outcome action with
    | .ok value => return value
    | .error error =>
      failure.atomically (modify fun first => first.orElse (fun _ => some error))
      throw (IO.userError "Build pool stopped")
  try return .ok (← run execute)
  catch error => return .error ((← failure.atomically get).getD (.tool error.toString))

def parallel (limit : Nat) (items : Array α) (body : α → BuildIO β) : BuildIO (Array β) :=
  pool fun execute => LeanCloudRuntime.Parallel.map limit items fun item => execute (body item)

def all (limit : Nat) (items : Array α) (body : α → BuildIO Bool) : BuildIO Bool :=
  pool fun execute => LeanCloudRuntime.Parallel.all limit items fun item => execute (body item)

end BuildIO
end LeanBuild
