import LeanCloudRuntime
import LeanVerify.Command

def main (args : List String) : IO UInt32 := do
  if let "files" :: commands := args then return ← LeanVerify.Command.main commands
  try
    let environment ← match args with
      | ["serve-worker", path] => do
        let config ← LeanCloudRuntime.Config.load path
        let tools ← LeanVerify.Tools.fromEnvironment
        pure (pure (tools, config.objects))
      | _ => pure (throw (IO.userError "Verification requires a configured worker"))
    let program := (LeanVerify.program environment).register
    let program := { program with validate := fun input => do
      let request : LeanVerify.Request ← Lean.fromJson? input
      request.validate }
    LeanCloudRuntime.Application.main ⟨#[program]⟩ args
  catch error => IO.eprintln s!"{error}"; return 1
