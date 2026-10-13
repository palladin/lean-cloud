import LeanCloud.Protocol

universe u

namespace LeanCloud

/-- Ordinary computation exceptions become serializable workflow failures.
A node crash is an interruption of the runtime, not an exception returned here. -/
class MonadCloudExec (m : Type → Type u) where
  capture {α : Type} : m α → ExceptT CloudError m α

/-- Catch IO exceptions at a user-effect boundary, preserving explicit Cloud errors.
Never apply this to replay-journal or worker-coordination operations. -/
def captureIO {α : Type} (action : ExceptT CloudError IO α) : ExceptT CloudError IO α :=
  ExceptT.mk do
    try action.run
    catch error => return .error ⟨.application, error.toString⟩

instance : MonadCloudExec IO where
  capture action := captureIO (liftM action)

instance : MonadCloudExec Id where
  capture action := ExceptT.mk (.ok action)

end LeanCloud
