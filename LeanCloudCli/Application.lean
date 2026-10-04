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

/-- The complete application, including startup, the REPL and error reporting.
    Its only effects are the typed host requests in `Cli`. -/
def application (args : List String) : Cli UInt32 := do
  try
    if Help.requested args then Help.display args
    else
      let root ← request (.realPath (← request .currentDir))
      let defaultProject ← if ← request (.exists (Project.manifest root)) then
        pure (← Project.load root).name else pure "lean-cloud-console"
      let project := (← request (.getEnv "LEAN_CLOUD_PROJECT")).getD defaultProject
      validateId project
      unless project == project.toLower do throw "Deployment project must be lowercase"
      let ctx ← Deployments.initial { root, project }
      if !args.isEmpty then
        discard (dispatch ctx args)
      else
        if ← request .enterTerminal then Shell.run ctx
        else
          printLine "lean-cloud · terminal console\nUse 'help' for commands; 'deploy' for first setup."
          repl ctx
    pure 0
  catch error => printError (safe error); pure 1

end LeanCloudCli
