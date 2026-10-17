import LeanCloudRuntime
import Wiki.Command

def main (args : List String) : IO UInt32 := do
  if let "files" :: commands := args then return ← Wiki.Command.main commands
  try
    let environment : IO LeanCloudRuntime.ObjectStore := do
      match args with
      | ["serve-worker", path] => return (← LeanCloudRuntime.Config.load path).objects
      | _ => throw (IO.userError "Analysis requires a configured worker")
    LeanCloudRuntime.Application.main ⟨Wiki.programs environment⟩ args
  catch error => IO.eprintln s!"{error}"; return 1
