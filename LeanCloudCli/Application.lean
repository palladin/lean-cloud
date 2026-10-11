import LeanCloudCli.Shell

namespace LeanCloudCli

private partial def repl (ctx : Context) : Cli Unit := do
  request (.write "cloud> ")
  request .flush
  let line ← request .readLine
  if line.isEmpty then return
  let (ctx, keepGoing) ← try
    dispatch ctx (← liftExcept (words line))
    catch error => printError (safe error); pure (ctx, true)
  if keepGoing then repl ctx

private def session (ctx : Context) : Cli Unit := do
  if ← request .enterTerminal then Shell.run ctx
  else
    printLine "lean-cloud · terminal console\nUse 'connect NAME URL' to connect; 'help' lists commands."
    repl ctx

/-- The complete application, including startup, the REPL and error reporting.
    Its only effects are the typed host requests in `Cli`. -/
def application (args : List String) : Cli UInt32 := do
  try
    if Help.requested args then Help.display args
    else
      let root := (← Profiles.home) / "connections"
      let ctx ← Profiles.initial { root, project := "disconnected" }
      if !args.isEmpty then
        discard (dispatch ctx args)
      else
        session ctx
    pure 0
  catch error => printError (safe error); pure 1

end LeanCloudCli
