import LeanCloud.Protocol

universe u

namespace LeanCloud

/-- Ordinary computation exceptions become serializable workflow failures.
A node crash is an interruption of the runtime, not an exception returned here. -/
class MonadCloudExec (m : Type → Type u) where
  capture {α : Type} : m α → ExceptT CloudError m α
  /-- Re-raise a capability failure in the user monad, where user code may catch it. -/
  restore {α : Type} : ExceptT CloudError m α → m α

/-- Catch IO exceptions at a user-effect boundary, preserving explicit Cloud errors.
Never apply this to replay-journal or worker-coordination operations. -/
def captureIO {α : Type} (action : ExceptT CloudError IO α) : ExceptT CloudError IO α :=
  ExceptT.mk do
    try action.run
    catch error => return .error ⟨.application, error.toString⟩

instance : MonadCloudExec IO where
  capture action := captureIO (liftM action)
  restore action := do
    match ← action.run with
    | .ok value => pure value
    | .error error => throw (IO.userError error.message)

/-- Error-aware base monads preserve the original error without conversion. -/
instance [Monad m] : MonadCloudExec (ExceptT CloudError m) where
  capture action := ExceptT.mk (ExceptT.mk (do return .ok (← action.run)))
  restore action := do
    match ← action.run with
    | .ok value => pure value
    | .error error => throw error

/-- IO exceptions underneath an explicit Cloud error layer are user failures too. -/
instance (priority := 1100) : MonadCloudExec (ExceptT CloudError IO) where
  capture action := ExceptT.mk (liftM ((captureIO action).run))
  restore action := do
    match ← action.run with
    | .ok value => pure value
    | .error error => throw error

end LeanCloud
