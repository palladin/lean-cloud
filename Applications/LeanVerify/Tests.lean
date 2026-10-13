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
  for version in ["4.35.0", "4.35.1", "4.36.0", "4.100.0", "5.0.0"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption == some version)
      s!"Supported source release rejected: {version}"
  for version in ["3.99.0", "4.9.0", "4.34.99", "4.35", "04.35.0", "4.035.0",
      "4.35.00", "4.35.0-rc1", "4.35.0+local", "nightly", "4.35.0\n"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption.isNone)
      s!"Unsupported source release accepted: {version}"
  check ((Tools.sourceRelease "other/lean4:v4.35.0").toOption.isNone)
    "Unofficial source toolchain accepted"
  let minimal : LeanVerify.Request ← IO.ofExcept (fromJson? (Json.mkObj [
    ("repository", toJson request.repository), ("revision", toJson "main"),
    ("modules", toJson #["Fixture.Final"])]))
  check (minimal.allowedAxioms.size == 3 && minimal.theorems.isEmpty &&
    !minimal.paranoid && minimal.limits.seconds == 600)
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
  check (({ request with allowedAxioms := #["Custom.axiom"] }.validate).toOption.isNone)
    "Unsupported lake check axiom policy accepted"
  check (({ request with allowedAxioms := #[] }.validate).toOption.isSome) "Stricter axiom policy rejected"
  for path in ["/etc/passwd", "../escape", "a/../../escape", "a//b"] do
    check (!Bundle.safePath path) "Unsafe artifact path accepted"
  IO.println "PASS 80 generated module DAGs: ordering, failures, direct/replay agreement and replay reuse"

private def executionFailureTest : IO Unit := do
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
          throw (IO.userError "Verifier failed")
      return { name := m.name, status := .checked } }
  let req := { request with modules := #["Final"], theorems := #[] }
  let run := (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) req).run
  for _ in [:2] do
    let .error error ← run | throw (IO.userError "Throwing verifier did not fail the workflow")
    check (error == ⟨.application, "Verifier failed"⟩) "Wrong execution failure"
  check ((← calls.get) == #["Base", "Final"])
    "Replay retried a failed verifier or repeated a recorded prerequisite"
  IO.println "PASS verifier exceptions are recorded once; replay never retries them"

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

private def publicationTests (tools : Tools) (store : ObjectStore)
    (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    let sourceBytes ← IO.FS.readBinFile (directory / "Fixture/Base.lean")
    let req := { request with modules := #["Fixture.Base"], theorems := #["Fixture.twice_zero"] }
    for artifact in [false, true] do
      let pending ← IO.mkRef true
      let flaky := { store with create := fun key bytes => do
        let saved ← store.create key bytes
        let target := if artifact then bytes.extract 0 5 == "olean".toUTF8 else bytes == sourceBytes
        if target then
          if ← pending.modifyGet fun old => (old, false) then
            throw (IO.userError "Injected publication failure")
        return saved }
      let prepares ← IO.mkRef (0 : Nat)
      let checks ← IO.mkRef (0 : Nat)
      let backend : Backend IO := {
        prepare := fun request => do
          prepares.modify (· + 1)
          tools.prepareDirectory flaky request directory "fixture-commit"
        check := fun request plan module completed => do
          checks.modify (· + 1)
          tools.check flaky request plan module completed }
      let saved ← IO.mkRef []
      let run := (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) req).run
      for _ in [:2] do
        let .error error ← run | throw (IO.userError "Publication failure did not fail the workflow")
        check (error == ⟨.application, "Injected publication failure"⟩) "Wrong publication failure"
      check (!(← pending.get)) "Publication fault did not reach the intended blob"
      check ((← prepares.get) == 1 && (← checks.get) == (if artifact then 1 else 0))
        "Replay retried failed publication after storage became healthy"
    IO.println "PASS publication exceptions are execution failures, not crashes or proof rejections"

private def nativeTests : IO Unit := do
  let tools ← Tools.fromEnvironment
  let fixture ← IO.FS.realPath "fixtures/Diamond"
  let store := objects (← IO.mkRef {})
  let runtimeCode ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Base.lean")
      "namespace Fixture\ndef twice (n : Nat) := n + n\nunsafe def castValue (n : Nat) : Int := unsafeCast n\npartial def loop (n : Nat) : Nat := loop (n + 1)\ntheorem twice_zero : twice 0 = 0 := rfl\n")
    { request with modules := #["Fixture.Base"], theorems := #["Fixture.twice_zero"] }
  check runtimeCode.success s!"Unsafe runtime code prevented proof verification: {repr runtimeCode}"
  publicationTests tools store fixture
  let oversized ← nativeTest tools store fixture (fun _ => pure ())
    { request with limits := { request.limits with bytes := 1 } }
  check (!oversized.success && (oversized.message.splitOn "artifact byte limit").length > 1)
    "A workspace validation error escaped instead of producing a failed report"
  IO.FS.withTempDir fun root => do
    let source := root / "source"
    IO.FS.createDir source
    IO.FS.writeFile (source / "original") "linked content"
    let linked ← IO.Process.output {
      cmd := "ln", args := #["-s", "original", (source / "link").toString] }
    check (linked.exitCode == 0) "Cannot create source symlink fixture"
    let manifest ← (← Bundle.prepare source 10000 false).publish store
    let restored := root / "restored"
    Bundle.restore store restored manifest 10000
    check ((← IO.FS.readFile (restored / "link")) == "linked content" &&
      (← (restored / "link").symlinkMetadata).type == .file) "Safe file link was not materialized"
    IO.FS.removeFile (source / "link")
    for target in ["../restored/original", "."] do
      let linked ← IO.Process.output {
        cmd := "ln", args := #["-s", target, (source / "link").toString] }
      check (linked.exitCode == 0) "Cannot create rejected symlink fixture"
      let rejected ← try
        discard <| Bundle.prepare source 10000 false
        pure false
      catch _ => pure true
      check rejected "Snapshot followed a directory or external symlink"
      IO.FS.removeFile (source / "link")
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
  check (report.checker == "lake check" && !report.paranoid &&
    report.toolchain == "leanprover/lean4:v4.35.0") "Wrong verification provenance"
  let leanConfig ← nativeTest tools store fixture (fun d => do
    IO.FS.removeFile (d / "lakefile.toml")
    IO.FS.writeFile (d / "lakefile.lean") "import Lake\nopen Lake DSL\npackage verify_fixture\nlean_lib Fixture\n")
  unless leanConfig.success do throw (IO.userError s!"Lean Lake config failed: {repr leanConfig}")
  for m in report.modules do
    let some ref := m.artifacts | throw (IO.userError "No module artifacts")
    let entries : Bundle.Manifest ← Files.readJson store ref
    check (entries.any (·.path.endsWith (m.name.replace "." "/" ++ ".olean"))) "Missing olean"
    let some exportRef := m.exportFile | throw (IO.userError "No verified export")
    check (exportRef.size > 0) "Empty export artifact"
    let some diagnostics := m.diagnostics | throw (IO.userError "No checker diagnostics")
    check (((← Files.readText store diagnostics).splitOn "Lean default kernel accepts").length > 1)
      "Module was accepted without running lake check"
  -- Corrupt a proof in valid NDJSON: the official kernel, not just the JSON
  -- parser or compiler, must reject it. The source project is absent here.
  IO.FS.withTempDir fun root => do
    let directory := root / "check"
    IO.FS.createDir directory
    let some finalModule := report.modules.back? | throw (IO.userError "No final module")
    let some exportRef := finalModule.exportFile | throw (IO.userError "No final export")
    let path := root / "proof.ndjson"
    Files.download store exportRef path request.limits.bytes
    let accepted ← tools.verifyExport directory request.limits path
    check accepted.isOk "Published export cannot be checked independently"
    if System.Platform.isOSX then
      let unavailable ← { tools with sandbox := true }.verifyExport directory request.limits path
      check (!unavailable.isOk) "Unavailable sandbox silently fell back to unsandboxed checking"
    let mut changed := false
    let mut lines : Array String := #[]
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.isEmpty then continue
      let json ← IO.ofExcept (Json.parse line)
      match json.getObjVal? "thm" with
      | .error _ => lines := lines.push line
      | .ok declaration =>
        changed := true
        let fields ← IO.ofExcept declaration.getObj?
        let type ← IO.ofExcept (declaration.getObjVal? "type")
        lines := lines.push (Json.mkObj [("thm", .obj (fields.insert "value" type))]).compress
    check changed "Export corruption test did not find a theorem"
    IO.FS.writeFile path (String.intercalate "\n" lines.toList ++ "\n")
    let rejected ← tools.verifyExport directory request.limits path
    check (!rejected.isOk) "lake check accepted a corrupt proof"
    let diagnostics ← IO.FS.readFile (root / "check.stdout")
    check ((diagnostics.splitOn "Lean default kernel rejected").length > 1)
      "Corrupt proof did not reach the kernel"
    -- The first line is exporter metadata; malformed declarations follow it.
    IO.FS.writeFile path "{}\nnot NDJSON\n"
    check (!(← tools.verifyExport directory request.limits path).isOk) "Malformed export accepted"
  let paranoid ← nativeTest tools store fixture (fun _ => pure ())
    { request with modules := #["Fixture.Base"], theorems := #[], paranoid := true }
  unless paranoid.success do throw (IO.userError s!"Paranoid verification failed: {repr paranoid}")
  check paranoid.paranoid "Paranoid mode was not recorded"
  let some paranoidModule := paranoid.modules[0]? | throw (IO.userError "Missing paranoid module")
  let some paranoidLog := paranoidModule.diagnostics | throw (IO.userError "Missing paranoid log")
  let paranoidText ← Files.readText store paranoidLog
  for name in ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"] do
    check ((paranoidText.splitOn s!"{name} kernel accepts").length > 1)
      s!"Paranoid mode skipped {name}"
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
  let tighter ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Base.lean")
      "namespace Fixture\ndef twice (n : Nat) := n + n\ntheorem standardAxiom (p q : Prop) (h : p ↔ q) : p = q := propext h\n")
    { request with allowedAxioms := #[] }
  check (!tighter.success) "Stricter axiom policy ignored"
  for version in ["4.34.1", "4.36.0"] do
    let mismatch ← nativeTest tools store fixture (fun d =>
      IO.FS.writeFile (d / "lean-toolchain") s!"leanprover/lean4:v{version}\n")
    check (!mismatch.success && mismatch.modules.size == 1) "Mismatched toolchain accepted"
    if version == "4.36.0" then
      check ((mismatch.message.splitOn "exact Lean toolchain").length > 1)
        "Newer source release did not reach the exact deployed-toolchain check"
  IO.println "PASS lake check: diamond build, safe source snapshots, published exports, corrupt proof rejection, all paranoid checkers, private sorry, axiom policies and toolchain failures"

def main (args : List String) : IO Unit := do
  generatedTests
  executionFailureTest
  if args.contains "--native" then nativeTests
