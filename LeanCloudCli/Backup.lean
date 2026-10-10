import LeanCloudCli.Docker

namespace LeanCloudCli.Backup
open Lean LeanCloud

private def runFiles := #["input.json", "control.json", "timing.json", "watch.json", "watch-status.json"]

structure SavedRun where
  run : Run
  files : Array (String × String)
  deriving ToJson, FromJson

structure Archive where
  file : String
  sha256 : String
  deriving ToJson, FromJson

structure Manifest where
  formatVersion : Nat := 1
  deployment : Deployment
  config : Json
  blobService : Json
  bindings : Array (String × String)
  images : Array String
  runs : Array SavedRun
  archives : Array Archive
  deriving ToJson, FromJson

private def digest (path : System.FilePath) : Cli String := do
  let output ← request (.process "openssl" #["dgst", "-sha256", "-r", path.toString] none)
  let hash := (output.stdout.splitOn " ").head!
  unless output.exitCode == 0 && hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw s!"Cannot checksum {path}"
  return hash

private def imageId (name : String) : Cli String := do
  return (← docker #["image", "inspect", name, "--format", "{{.Id}}"]).stdout.trimAscii.toString

private def stopped (ctx : Context) (volumes : Array String) : Cli Unit := do
  for label in #["lean-cloud.project=" ++ ctx.project, "com.docker.compose.project=" ++ ctx.project] do
    unless (← docker #["ps", "-aq", "--filter", "label=" ++ label]).stdout.trimAscii.isEmpty do
      throw "Stop this deployment with 'down' before making a backup"
  for volume in volumes do
    unless (← docker #["ps", "-aq", "--filter", "volume=" ++ ctx.project ++ "_" ++ volume]).stdout.trimAscii.isEmpty do
      throw s!"Volume {volume} still belongs to a container; remove it before backup"

private def tarVolume (image volume directory file : String) (restore := false) : Cli Unit := do
  discard <| docker #["run", "--rm", "--network", "none", "--read-only", "--user", "0:0", "--entrypoint", "tar",
    "--mount", s!"type=volume,source={volume},target=/data" ++ (if restore then "" else ",readonly"),
    "--mount", s!"type=bind,source={directory},target=/backup" ++ (if restore then ",readonly" else ""),
    image, (if restore then "-xf" else "-cf"), "/backup/" ++ file, "-C", "/data", "."]

def save (ctx : Context) (destination : String) : Cli Unit := ctx.withDeploymentLock do
  let deployment ← ctx.deployment
  let volumes := deploymentVolumes deployment.retainedCount
  stopped ctx volumes
  let path := ctx.root / destination
  let some name := path.fileName | throw "Backup destination needs a directory name"
  unless name != "." && name != ".." do throw "Choose a new backup directory"
  let parent ← request (.realPath (path.parent.getD ctx.root))
  let directory := parent / name
  unless directory.isAbsolute && !directory.toString.contains ',' do throw "Backup path must be absolute and contain no commas"
  let home ← request (.realPath ctx.home)
  if directory.toString == home.toString || directory.toString.startsWith (home.toString ++ "/") then
    throw "Place the backup outside the deployment directory so 'clean' cannot remove it"
  if ← request (.exists directory) then throw "Backup destination already exists; choose a new directory"
  let config ← readJson (α := Json) (← ctx.configFile)
  discard <| liftExcept (Project.runtimeConfig config deployment.retainedCount)
  unless (config.getObjVal? "blobs" >>= (·.getObjValAs? String "endpoint")).toOption == some "http://blobs:8333" do
    throw "Backup currently requires the bundled local blob service"
  for volume in volumes do discard <| docker #["volume", "inspect", ctx.project ++ "_" ++ volume]
  let compose ← ctx.compose #["config", "--format", "json"]
  let blobService ← liftExcept (Json.parse compose.stdout >>= (·.getObjVal? "services") >>= (·.getObjVal? "blobs"))
  unless ← request (.exists (ctx.home / "blob-image.json")) do
    throw "Blob image identity is missing. Run 'up', then 'down' before backing up this deployment."
  let blobImage : String ← readJson (ctx.home / "blob-image.json")
  let mounts ← liftExcept (blobService.getObjValAs? (Array Json) "volumes")
  let mut bindings := #[]
  for mount in mounts do
    if (mount.getObjValAs? String "type").toOption == some "bind" then
      let target ← liftExcept (mount.getObjValAs? String "target")
      unless #["/etc/seaweedfs/s3.json", "/etc/seaweedfs/filer.toml"].contains target do
        throw s!"Unsupported blob-service bind mount: {target}"
      let source ← liftExcept (mount.getObjValAs? String "source")
      bindings := bindings.push (target, ← request (.readFile source))
  let mut images := #[deployment.image, blobImage]
  let runs ← (← ctx.allRuns).mapM fun run => do
    let mut files := #[]
    for name in runFiles do
      if ← request (.exists (ctx.directory run.id / name)) then
        files := files.push (name, ← request (.readFile (ctx.directory run.id / name)))
    return ({ run, files } : SavedRun)
  for run in runs do
    unless images.contains run.run.image do images := images.push run.run.image
  for image in images do
    unless (← imageId image) == image do throw "Backup requires immutable image IDs"
  request (.createDir directory)
  printLine s!"Saving {volumes.size} volumes and {images.size} images to {directory}…"
  request .flush
  discard <| docker (#["image", "save", "-o", (directory / "images.tar").toString] ++ images)
  let mut archives := #[({ file := "images.tar", sha256 := ← digest (directory / "images.tar") } : Archive)]
  for (volume, index) in volumes.zipIdx do
    let file := s!"volume-{index}.tar"
    tarVolume deployment.image (ctx.project ++ "_" ++ volume) directory.toString file
    archives := archives.push ⟨file, ← digest (directory / file)⟩
  let manifest : Manifest := {
    deployment, config, blobService := blobService.setObjVal! "image" (toJson blobImage)
    bindings, images, runs, archives }
  -- The manifest is the completion marker; failed backups are never restorable.
  saveJson (directory / "backup.json") manifest
  printLine "Backup complete. The deployment remains stopped; use 'up' when ready."

def validate (manifest : Manifest) : Except String Unit := do
  unless manifest.formatVersion == 1 do throw "Unsupported backup format"
  let deployment := manifest.deployment
  unless validId deployment.project && deployment.project == deployment.project.toLower do throw "Invalid backup project"
  let images := manifest.images
  unless images.contains deployment.image && images.all (fun image =>
      image.startsWith "sha256:" && image.length == 71 &&
      (image.drop 7).toString.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))) do
    throw "Backup has invalid image identities"
  let blobImage ← manifest.blobService.getObjValAs? String "image"
  unless images.contains blobImage do throw "Blob-service image is missing"
  let expected := #["images.tar"] ++ (Array.range (deploymentVolumes deployment.retainedCount).size).map (s!"volume-{·}.tar")
  unless manifest.archives.map (·.file) == expected do throw "Backup archive list is incomplete or invalid"
  for archive in manifest.archives do
    unless archive.sha256.length == 64 && archive.sha256.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      throw "Invalid archive checksum"
  let mut ids := #[]
  for saved in manifest.runs do
    unless validId saved.run.id && !ids.contains saved.run.id && images.contains saved.run.image do throw "Invalid saved run"
    ids := ids.push saved.run.id
    let mut names := #[]
    for (name, _) in saved.files do
      unless runFiles.contains name && !names.contains name do throw "Invalid saved run file"
      names := names.push name
  for (target, _) in manifest.bindings do
    unless #["/etc/seaweedfs/s3.json", "/etc/seaweedfs/filer.toml"].contains target do throw "Invalid blob-service binding"
  discard <| Project.runtimeConfig manifest.config deployment.retainedCount

/-- Restore into fresh volumes. Failed imports remain stopped and are owned by
this deployment; 'clean' removes them before a retry. No partial restore starts. -/
def restore (root : System.FilePath) (source : String) : Cli Context := do
  let directory ← request (.realPath (root / source))
  unless directory.isAbsolute && !directory.toString.contains ',' do throw "Backup path must be absolute and contain no commas"
  let manifest : Manifest ← readJson (directory / "backup.json")
  liftExcept (validate manifest)
  let ctx : Context := ⟨root, manifest.deployment.project⟩
  ctx.withDeploymentLock do
    if ← request (.exists ctx.home) then throw "Restore needs a fresh deployment directory; existing data is never overwritten"
    Deployments.checkOwnership ctx
    let volumes := deploymentVolumes manifest.deployment.retainedCount
    let existing ← docker #["volume", "ls", "--format", "{{.Name}}"]
    if (existing.stdout.splitOn "\n").any (isDeploymentVolume ctx.project) then
      throw "Restore needs fresh volumes, including retired workers. Existing deployment data is never overwritten"
    let labeled ← docker #["volume", "ls", "-q", "--filter", "label=com.docker.compose.project=" ++ ctx.project]
    unless labeled.stdout.trimAscii.isEmpty do throw "Restore destination still has deployment volumes"
    for label in #["lean-cloud.project=" ++ ctx.project, "com.docker.compose.project=" ++ ctx.project] do
      unless (← docker #["ps", "-aq", "--filter", "label=" ++ label]).stdout.trimAscii.isEmpty do
        throw "Restore destination still has containers"
    for archive in manifest.archives do
      unless (← digest (directory / archive.file)) == archive.sha256 do throw s!"Backup checksum mismatch: {archive.file}"
    -- Register before resource creation, so an interrupted restore can be cleaned.
    Deployments.remember ctx
    request (.createDir ctx.home)
    saveJson (ctx.home / "catalog-owner.json") (← Deployments.home).toString
    saveJson (ctx.home / "restore-incomplete.json") true
    discard <| docker #["image", "load", "-i", (directory / "images.tar").toString]
    for image in manifest.images do
      unless (← imageId image) == image do throw "Restored image does not match its identity"
    for image in #[manifest.deployment.image] ++ manifest.runs.map (·.run.image) do
      discard <| docker #["tag", image, ctx.project ++ "-app:" ++ (image.drop 7).toString]
    for (volume, index) in volumes.zipIdx do
      let name := ctx.project ++ "_" ++ volume
      discard <| docker #["volume", "create", "--label", "com.docker.compose.project=" ++ ctx.project, name]
      tarVolume manifest.deployment.image name directory.toString s!"volume-{index}.tar" true
    request (.createDir (Project.assets ctx))
    saveJson (Project.assets ctx / "config.json") manifest.config
    saveJson (ctx.home / "blob-image.json") (← liftExcept (manifest.blobService.getObjValAs? String "image"))
    let mut mounts := #[toJson "blob-data:/data"]
    for ((target, text), index) in manifest.bindings.zipIdx do
      let path := Project.assets ctx / s!"blob-bind-{index}.txt"
      request (.writeFile path text)
      mounts := mounts.push (Json.mkObj [("type", toJson "bind"), ("source", toJson path.toString),
        ("target", toJson target), ("read_only", toJson true)])
    let blobService := manifest.blobService.setObjVal! "volumes" (toJson mounts)
    saveJson (Project.assets ctx / "compose.json") (Json.mkObj [
      ("services", Json.mkObj [("blobs", blobService)]), ("volumes", Json.mkObj [("blob-data", Json.mkObj [])])])
    for saved in manifest.runs do
      request (.createDir (ctx.directory saved.run.id))
      saveJson (ctx.directory saved.run.id / "run.json") saved.run
      for (name, text) in saved.files do request (.writeFile (ctx.directory saved.run.id / name) text)
    saveJson (ctx.home / "deployment.json") manifest.deployment
    request (.removeTree (ctx.home / "restore-incomplete.json"))
    printLine s!"Restored {ctx.project}. Use 'up' to start the saved application; active runs recover from their records."
    return ctx

end LeanCloudCli.Backup
