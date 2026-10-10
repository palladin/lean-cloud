import LeanCloudCli.Docker

namespace LeanCloudCli

private def listed (args : Array String) : Cli (Array String) := do
  let output ← docker args
  return (output.stdout.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)).toArray

private def unique (values : Array String) : Array String :=
  values.foldl (fun result value => if result.contains value then result else result.push value) #[]

/-- Keep the local manifest until remote cleanup has completed. The scheduler
retains the removed ID permanently, so stale submissions cannot resurrect it. -/
def Context.removeRun (ctx : Context) (id : String) : Cli Unit := do
  validateId id
  ctx.withDeploymentLock do
    printLine s!"Removing finished run {id} and its replay records; user blobs are preserved…"
    discard <| ctx.execApp #["remove", "/etc/lean-cloud/config.json", id]
    request (.removeTree (ctx.directory id))
    printLine s!"Removed {id}. Its ID cannot be reused."

/-- Complete removal of one deployment. Discover before deleting; retain the
local recovery information until all Docker removals have succeeded. Retrying
uses fresh inventories, including after an interrupted or failed deployment. -/
def Context.clean (ctx : Context) : Cli Unit := do
  validateId ctx.project
  Deployments.checkOwnership ctx
  ctx.withDeploymentLock do
    printStyled (Styled.text s!"Removing deployment {ctx.project}, including all stored workflows, results, and blobs…" .red)
    try
      let label := "label=com.docker.compose.project=" ++ ctx.project
      let actors ← listed #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project]
      let composed ← listed #["ps", "-aq", "--filter", label]
      let containers := unique (actors ++ composed)
      let networks ← listed #["network", "ls", "-q", "--filter", label]
      let composedVolumes ← listed #["volume", "ls", "-q", "--filter", label]
      let poolVolumes := (← listed #["volume", "ls", "-q"]).filter (isDeploymentVolume ctx.project)
      let volumes := unique (composedVolumes ++ poolVolumes)
      let repository := ctx.project ++ "-app"
      let images := (← listed #["image", "ls", "--format", "{{.Repository}}:{{.Tag}}", repository]).filter
        (fun tag => tag.startsWith (repository ++ ":") && !tag.endsWith ":<none>")
      for container in containers do discard <| docker #["stop", container]
      for container in containers do discard <| docker #["rm", container]
      for network in unique networks do discard <| docker #["network", "rm", network]
      for volume in volumes do discard <| docker #["volume", "rm", volume]
      -- Remove our tags, not shared image IDs or Docker's global build cache.
      for tag in unique images do discard <| docker #["image", "rm", tag]
      request (.removeTree ctx.home)
      Deployments.forget ctx
      printStyled (Styled.text s!"Removed deployment {ctx.project}. Use 'deploy' to create a fresh deployment." .green)
    catch error =>
      throw s!"Cleanup incomplete for {ctx.project}: {error}\nRun 'clean' again to finish."

end LeanCloudCli
