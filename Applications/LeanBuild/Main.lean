import LeanCloudRuntime
import LeanBuild.Command

def main (args : List String) : IO UInt32 := do
  if let "files" :: commands := args then return ← LeanBuild.Command.main commands
  try
    let environment ← match args with
      | ["serve-worker", path] => do
        let config ← LeanCloudRuntime.Config.load path
        let tools ← LeanBuild.Tools.fromEnvironment
        pure (pure (tools, config.objects))
      | _ => pure (throw (IO.userError "Building requires a configured worker"))
    let program := (LeanBuild.program environment).register
    let program := { program with validate := fun input => do
      let request : LeanBuild.Request ← Lean.fromJson? input
      request.validate }
    LeanCloudRuntime.Application.main ⟨#[program]⟩ args
  catch error => IO.eprintln s!"{error}"; return 1
