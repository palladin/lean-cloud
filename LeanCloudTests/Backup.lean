import LeanCloudTests.ConsoleModel
import LeanCloudTests.Support

namespace LeanCloudTests.Backup
open Lean LeanCloud LeanCloudCli
open ConsoleModel (World Invocation)

private def image := "sha256:" ++ String.ofList (List.replicate 64 'a')
private def checksum := String.ofList (List.replicate 64 'b')
private def ctx : Context := ⟨"/work", "demo"⟩
private def deployment : Deployment := ⟨ctx.project, image, #[], 1, 1⟩

private def output (text := "") : Except String ProcessOutput := .ok { stdout := text }

private def process (call : Invocation) : Except String ProcessOutput := do
  if call.command == "openssl" then return { stdout := checksum ++ " file" }
  unless call.command == "docker" do throw "Unexpected host command"
  match call.args.toList with
  | ["image", "inspect", _, "--format", "{{.Id}}"] => output image
  | "compose" :: _ => output (Json.mkObj [("services", Json.mkObj [("blobs", Json.mkObj [
      ("image", toJson image), ("volumes", toJson (#[] : Array Json))])])]).compress
  | "ps" :: _ | "volume" :: _ | "image" :: _ | "run" :: _ | "tag" :: _ => output
  | _ => throw s!"Unexpected backup command: {reprStr call.args}"

private def initial : World :=
  ({ process, directories := #["/work", ctx.home.toString] } : World)
    |>.json (ctx.home / "deployment.json") deployment
    |>.json (ctx.home / "blob-image.json") image
    |>.json "/work/deploy/config.json" Project.defaultConfig

private def fixture : IO (LeanCloudCli.Backup.Manifest × World) := do
  let (result, world) := ConsoleModel.run (LeanCloudCli.Backup.save ctx "/backups/archive") initial
  discard (unwrap result)
  let some text := world.file "/backups/archive/backup.json" | throw (IO.userError s!"Missing backup manifest: {world.stdout}")
  let manifest ← unwrap (Json.parse text >>= fromJson?)
  return (manifest, world)

def cases : Array TestCase := #[
  ⟨"console.backup.interrupted-export-and-import", do
    let exportFailure := { initial with
      process := fun call => if call.args.toList.take 2 == ["image", "save"] then .error "interrupted"
        else process call }
    let (result, after) := ConsoleModel.run (LeanCloudCli.Backup.save ctx "/backups/archive") exportFailure
    assertTrue result.toOption.isNone "Export failure was ignored"
    assertTrue (after.file "/backups/archive/backup.json").isNone "Incomplete backup was marked complete"
    assertTrue after.locks.isEmpty "Export leaked lock"
    let (_, world) ← fixture
    let clean := { world with
      files := world.files.filter (fun (name, _) => !name.startsWith "/work/")
      directories := #["/new", "/backups/archive"], processes := #[]
      process := fun call => if call.args.contains "-xf" then .error "interrupted" else process call }
    let (result, after) := ConsoleModel.run (LeanCloudCli.Backup.restore "/new" "/backups/archive") clean
    assertTrue result.toOption.isNone "Import failure was ignored"
    let target : Context := ⟨"/new", "demo"⟩
    assertTrue (after.file (target.home / "restore-incomplete.json")).isSome "Partial import lost its marker"
    let (started, after) := ConsoleModel.run target.up { after with processes := #[] }
    assertTrue (started.toOption.isNone && after.processes.isEmpty) "Partial import started nodes"
    assertTrue after.locks.isEmpty "Import leaked lock"⟩,
  ⟨"console.backup.uses-deployed-blob-image", do
    let stored := initial
    let changedTag := { stored with
      process := fun call =>
        if call.args[0]? == some "compose" then output (Json.mkObj [("services", Json.mkObj [
          ("blobs", Json.mkObj [("image", toJson "seaweedfs:mutable"),
            ("volumes", toJson (#[] : Array Json))])])]).compress
        else if call.args.toList.take 2 == ["image", "inspect"] && !call.args.contains image then
          .error "Mutable image tag was consulted" else process call }
    let (result, _) := ConsoleModel.run (LeanCloudCli.Backup.save ctx "/backups/archive") changedTag
    discard (unwrap result)
    let missing := { stored with files := stored.files.filter (·.1 != (ctx.home / "blob-image.json").toString) }
    let (result, _) := ConsoleModel.run (LeanCloudCli.Backup.save ctx "/backups/archive") missing
    assertTrue result.toOption.isNone "Backup guessed an unknown deployed image"⟩,
  ⟨"console.backup.reject-retired-worker-storage", do
    let (_, world) ← fixture
    let clean := { world with
      files := world.files.filter (fun (name, _) => !name.startsWith "/work/")
      directories := #["/new", "/backups/archive"], processes := #[]
      process := fun call => if call.args.toList.take 2 == ["volume", "ls"] then
          output "demo_worker99-mailbox-data\n" else process call }
    let (result, after) := ConsoleModel.run (LeanCloudCli.Backup.restore "/new" "/backups/archive") clean
    assertTrue result.toOption.isNone "Restore accepted an old retired-worker volume"
    assertTrue (!after.processes.any (fun call => call.args.contains "load" || call.args.contains "create"))
      "Restore mutated data before detecting retained storage"⟩,
  ⟨"console.backup.stopped-snapshot-and-fresh-restore", do
    let (manifest, world) ← fixture
    assertEq manifest.archives.size 5 "Backup omitted a retained volume"
    let clean := { world with
      files := world.files.filter (fun (name, _) => !name.startsWith "/work/")
      directories := #["/new", "/backups/archive"], processes := #[] }
    let (result, restored) := ConsoleModel.run (LeanCloudCli.Backup.restore "/new" "/backups/archive") clean
    let selected ← unwrap result
    assertEq selected.root.toString "/new"
    assertEq selected.project "demo"
    assertTrue (restored.file (selected.home / "deployment.json")).isSome "Restore omitted deployment metadata"
    assertTrue (restored.file (selected.home / "restore-incomplete.json")).isNone "Restore remained incomplete"
    assertTrue (!restored.processes.any (fun call => call.args.contains "up" || call.args.contains "serve-worker"))
      "Restore started a partially imported deployment"⟩,
  ⟨"console.backup.reject-running-and-existing-data", do
    let live := { initial with
      process := fun call =>
        if call.args[0]? == some "ps" then output "running-container" else process call }
    let (result, after) := ConsoleModel.run (LeanCloudCli.Backup.save ctx "/backups/archive") live
    assertTrue result.toOption.isNone "Backup accepted a running deployment"
    assertTrue (!after.processes.any (·.args.contains "save")) "Backup copied changing storage"
    let (_, world) ← fixture
    let (result, after) := ConsoleModel.run (LeanCloudCli.Backup.restore "/work" "/backups/archive") { world with processes := #[] }
    assertTrue result.toOption.isNone "Restore overwrote existing deployment files"
    assertTrue after.processes.isEmpty "Restore imported before checking destination"⟩,
  ⟨"console.backup.reject-corruption-before-import", do
    let (_, world) ← fixture
    let clean := { world with
      files := world.files.filter (fun (name, _) => !name.startsWith "/work/")
      directories := #["/new", "/backups/archive"], processes := #[]
      process := fun call => if call.command == "openssl" then output (String.ofList (List.replicate 64 '0') ++ " file")
        else process call }
    let (result, after) := ConsoleModel.run (LeanCloudCli.Backup.restore "/new" "/backups/archive") clean
    assertTrue result.toOption.isNone "Corrupt archive was imported"
    assertTrue (!after.processes.any (fun call => call.args.contains "load" || call.args.contains "create"))
      "Failed validation mutated Docker storage"⟩,
  ⟨"console.backup.reject-future-format-and-unsafe-files", do
    let (manifest, _) ← fixture
    assertTrue (LeanCloudCli.Backup.validate { manifest with formatVersion := 999 }).toOption.isNone
      "Future backup was accepted"
    assertTrue (LeanCloudCli.Backup.validate { manifest with archives := #[⟨"../other", checksum⟩] }).toOption.isNone
      "Unsafe archive paths were accepted"⟩]

end LeanCloudTests.Backup
