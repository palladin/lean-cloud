import LeanVerify
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay

open Lean LeanCloud LeanCloudRuntime LeanVerify

private def check (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def noBlobs : BlobStorage IO where
  putBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  readBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  resolveBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩

private def journal (ref : IO.Ref (List (String × ReplayRecord))) : ReplayStore IO where
  read key := return (← ref.get).lookup key
  create key value := ref.modifyGet fun saved =>
    match saved.lookup key with
    | some old => (old, saved)
    | none => (value, (key, value) :: saved)

private def objects (ref : IO.Ref (Std.HashMap String ByteArray)) : ObjectStore where
  ensureContainer := pure ()
  read key := return (← ref.get)[key]?
  create key bytes := ref.modifyGet fun saved => match saved[key]? with
    | some old => (old, saved)
    | none => (bytes, saved.insert key bytes)
  erase key := ref.modify (·.erase key)
  list _ := return #[]

private def request : LeanVerify.Request := {
  repository := "https://github.com/palladin/lean-cloud"
  revision := "main", modules := #["Fixture.Final"], theorems := #["Fixture.result"] }

private def generatedTests : IO Unit := do
  let minimal : LeanVerify.Request ← IO.ofExcept (fromJson? (Json.mkObj [
    ("repository", toJson request.repository), ("revision", toJson "main"),
    ("modules", toJson #["Fixture.Final"])]))
  check (minimal.allowedAxioms.size == 3 && minimal.theorems.isEmpty && minimal.limits.seconds == 600)
    "Minimal JSON request did not receive defaults"
  for seed in [:80] do
    let modules := (Array.range (4 + seed % 12)).map fun i => {
      name := s!"M{i}"
      imports := ((Array.range i).filter fun j => (i * 37 + j * 7 + seed) % 3 == 0).map (s!"M{·}") : LeanVerify.Module }
    IO.ofExcept (validateModules modules)
    let counts ← IO.mkRef (#[] : Array String)
    let plan : Plan := { commit := "fixture", toolchain := "fixture", source := default, modules }
    let backend : Backend IO := {
      prepare := fun _ => pure { plan := some plan }
      check := fun _ _ m done => do
        check (m.imports.all fun name => done.any fun r => r.name == name && r.status == .checked)
          "A module ran before its dependencies were checked"
        counts.modify (·.push m.name)
        return { name := m.name, status := if seed % 2 == 0 && m.name == "M1" then .failed else .checked } }
    let req := { request with modules := modules.map (·.name), theorems := #[] }
    let direct ← (DirectInterpreter.interpret noBlobs (workflow backend) req).run
    let saved ← IO.mkRef []
    let actual ← (SequentialReplay.interpret (journal saved) noBlobs 10000 (workflow backend) req).run
    check ((toJson direct).compress == (toJson actual).compress) "Direct/replay verification reports differ"
    let before ← counts.get
    discard <| (SequentialReplay.interpret (journal saved) noBlobs 10000 (workflow backend) req).run
    check ((← counts.get) == before) "Replay reran completed check jobs"
  check ((validateModules #[⟨"A", #["B"]⟩, ⟨"B", #["A"]⟩]).toOption.isNone) "Cycle accepted"
  check ((validateModules #[⟨"A", #[]⟩, ⟨"A", #[]⟩]).toOption.isNone) "Duplicate accepted"
  check (({ request with repository := "https://github.com/a/../b" }.validate).toOption.isNone) "Unsafe URL"
  check (({ request with revision := "--upload-pack=evil" }.validate).toOption.isNone) "Git flag accepted"
  check (({ request with allowedAxioms := #["sorryAx"] }.validate).toOption.isNone) "sorryAx allowed"
  for path in ["/etc/passwd", "../escape", "a/../../escape", "a//b"] do
    check (!Bundle.safePath path) "Unsafe artifact path accepted"
  IO.println "PASS 80 generated module DAGs: ordering, failures, direct/replay agreement and replay reuse"

private def restartTest : IO Unit := do
  let saved ← IO.mkRef []
  let calls ← IO.mkRef (#[] : Array String)
  let stop ← IO.mkRef true
  let plan : Plan := {
    commit := "fixture", toolchain := "fixture", source := default
    modules := #[⟨"Base", #[]⟩, ⟨"Final", #["Base"]⟩] }
  let backend : Backend IO := {
    prepare := fun _ => pure { plan := some plan }
    check := fun _ _ m _ => do
      calls.modify (·.push m.name)
      if m.name == "Final" then
        if ← stop.modifyGet fun old => (old, false) then
          throw (IO.userError "Injected worker stop")
      return { name := m.name, status := .checked } }
  let req := { request with modules := #["Final"], theorems := #[] }
  let run := (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) req).run
  let interrupted ← try discard run; pure false catch _ => pure true
  check interrupted "Worker stop did not interrupt verification"
  let .ok report ← run | throw (IO.userError "Restart failed")
  check (report.success && (← calls.get) == #["Base", "Final", "Final"])
    "Restart repeated a recorded prerequisite or lost the interrupted job"
  IO.println "PASS interrupted module retries while checked prerequisites are replayed"

private def copyFixture (source destination : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "cp", args := #["-R", source.toString ++ "/.", destination.toString] }
  check (out.exitCode == 0) "Fixture copy failed"
  -- Existing local outputs must never enter a clean source-checking test.
  if ← (destination / ".lake").pathExists then IO.FS.removeDirAll (destination / ".lake")

private def nativeTest (tools : Tools) (store : ObjectStore) (fixture : System.FilePath)
    (change : System.FilePath → IO Unit) (req : LeanVerify.Request := request) : IO LeanVerify.Report :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    change directory
    let prepared ← tools.prepareDirectory store req directory "fixture-commit"
    let backend := { tools.backend store with prepare := fun _ => pure prepared }
    let .ok report ← (DirectInterpreter.interpret noBlobs (workflow backend) req).run
      | throw (IO.userError "Native workflow failed")
    return report

private def nativeTests : IO Unit := do
  let tools ← Tools.fromEnvironment
  let fixture ← IO.FS.realPath "fixtures/Diamond"
  let store := objects (← IO.mkRef {})
  IO.FS.withTempDir fun directory => do
    let start ← IO.monoMsNow
    let result ← LeanCloudRuntime.Process.runFiles {
      cmd := "/bin/sh", args := #["-c", "sleep 10 & exit 0"] }
      500 (directory / "out") (directory / "err") 1024
    check (result.exitCode == 0 && (← IO.monoMsNow) - start < 5000)
      "A background child held output pipes open after its parent exited"
  let report ← nativeTest tools store fixture (fun _ => pure ())
  unless report.success do
    for m in report.modules do
      IO.eprintln s!"{m.name}: {m.message}"
      if let some diagnostics := m.diagnostics then IO.eprintln (← Files.readText store diagnostics)
    throw (IO.userError "Diamond verification failed")
  check (report.modules.size == 4) "Wrong module closure"
  check (report.modules.flatMap (·.theorems.map (·.name)) == #["Fixture.result"]) "Theorem missing"
  let leanConfig ← nativeTest tools store fixture (fun d => do
    IO.FS.removeFile (d / "lakefile.toml")
    IO.FS.writeFile (d / "lakefile.lean") "import Lake\nopen Lake DSL\npackage verify_fixture\nlean_lib Fixture\n")
  unless leanConfig.success do throw (IO.userError s!"Lean Lake config failed: {repr leanConfig}")
  for m in report.modules do
    let some ref := m.artifacts | throw (IO.userError "No module artifacts")
    let entries : Bundle.Manifest ← Files.readJson store ref
    check (entries.any (·.path.endsWith (m.name.replace "." "/" ++ ".olean"))) "Missing olean"
  let sorryReport ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nnamespace Fixture\ntheorem left : twice 1 = 2 := by sorry\n")
  check (!sorryReport.success && sorryReport.modules.any (fun m => m.name == "Fixture.Left" && m.status == .failed) &&
    sorryReport.modules.any (fun m => m.name == "Fixture.Right" && m.status == .checked) &&
    sorryReport.modules.any (fun m => m.name == "Fixture.Final" && m.status == .blocked)) "sorry failure propagation incorrect"
  let bad ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nexample : False := True.intro\n")
  check (!bad.success) "Invalid proof accepted"
  let missing ← nativeTest tools store fixture (fun _ => pure ())
    { request with theorems := #["Fixture.missing"] }
  check (!missing.success && missing.message.startsWith "Missing theorem") "Missing theorem accepted"
  let notTheorem ← nativeTest tools store fixture (fun _ => pure ())
    { request with theorems := #["Fixture.twice"] }
  check (!notTheorem.success) "Definition accepted as theorem"
  let privateSorry ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean")
      "module\npublic import Fixture.Base\nprivate theorem hidden : False := by sorry\nnamespace Fixture\npublic theorem left : twice 1 = 2 := rfl\n")
  check (!privateSorry.success && privateSorry.modules.any (fun m =>
    m.name == "Fixture.Left" && m.status == .failed)) "Private sorry escaped verification"
  let assumption ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean")
      "import Fixture.Base\nnamespace Fixture\naxiom assumeLeft : twice 1 = 2\ntheorem left : twice 1 = 2 := assumeLeft\n")
  check (!assumption.success) "Undeclared axiom assumption accepted"
  let mismatch ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "lean-toolchain") "leanprover/lean4:v0.0.0\n")
  check (!mismatch.success && mismatch.modules.size == 1) "Mismatched toolchain accepted"
  IO.println "PASS native diamond build, kernel recheck, immutable artifacts, sorry/invalid proof, missing theorem and toolchain failures"

def main (args : List String) : IO Unit := do
  generatedTests
  restartTest
  if args.contains "--native" then nativeTests
