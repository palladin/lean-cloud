namespace LeanBuild

/-- Errors remain typed until the outer IO/Cloud boundary. Cleanup preserves the
original cause; callers can inspect `primary` without parsing diagnostic text. -/
inductive BuildError where
  | cancelled
  | network (message : String)
  | tool (message : String)
  | protocol (message : String)
  | cleanup (original : BuildError) (failure : BuildError)
  deriving Repr, BEq, Inhabited

def BuildError.primary : BuildError → BuildError
  | .cleanup original _ => original.primary
  | error => error

/-- Only a bare cancellation may be ignored during shutdown. An attached
cleanup failure must still be reported, even when the primary is cancellation. -/
def BuildError.isCancelled (error : BuildError) : Bool := error == .cancelled

def BuildError.render : BuildError → String
  | .cancelled => "Build cancelled"
  | .network message | .tool message | .protocol message => message
  | .cleanup original failure => original.render ++ "\nCleanup failed: " ++ failure.render

instance : ToString BuildError := ⟨BuildError.render⟩

/-- Retain the first error, including when further cleanup actions also fail. -/
def BuildError.after (result : Except BuildError α) (cleanup : Except BuildError Unit) : Except BuildError α :=
  match result, cleanup with
  | result, .ok () => result
  | .ok _, .error error => .error error
  | .error original, .error error => .error (.cleanup original error)

end LeanBuild
