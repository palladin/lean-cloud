import LeanCloudRuntime
import CubeAndConquer.Command

def main (args : List String) : IO UInt32 := do
  if let "files" :: commands := args then return ← CubeAndConquer.Command.main commands
  try
    let environment ← match args with
      | ["serve-worker", path] => do
        let config ← LeanCloudRuntime.Config.load path
        let tools ← CubeAndConquer.Tools.fromEnvironment
        pure (pure (tools, config.objects))
      | _ => pure (throw (IO.userError "SAT execution requires a configured worker"))
    let program := (CubeAndConquer.program environment).register
    let program := { program with validate := fun input => do
      let request : CubeAndConquer.Request ← Lean.fromJson? input
      request.validate }
    LeanCloudRuntime.Application.main ⟨#[program]⟩ args
  catch error => IO.eprintln s!"{error}"; return 1
