import LeanBuild
import LeanCloud.DirectInterpreter
import LeanCloud.SequentialReplay

open Lean LeanCloud LeanCloudRuntime LeanBuild

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

private def request : LeanBuild.Request := {
  repository := "https://github.com/palladin/lean-cloud"
  revision := "main", targets := #["+Fixture.Final"] }

private def fixturePlan : Plan := {
  commit := "fixture", toolchain := "fixture", platform := "fixture", source := default
  modules := #[⟨"Base", #[]⟩, ⟨"Final", #["Base"]⟩] }

private def stub : Backend IO := {
  prepare := fun _ => pure { plan := some fixturePlan }
  build := fun _ _ m _ => pure { name := m.name, status := .built }
  finish := fun _ _ _ => pure { name := "targets", status := .built }
  check := fun r _ _ => pure { mode := r.check.mode, success := true } }

private def generatedTests : IO Unit := do
  for version in ["4.35.0", "4.35.1", "4.36.0", "5.0.0"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption == some version) "Supported release rejected"
  for version in ["3.99.0", "4.34.99", "4.35", "04.35.0", "4.35.0-rc1", "nightly"] do
    check ((Tools.sourceRelease s!"leanprover/lean4:v{version}").toOption.isNone) "Unsupported release accepted"
  let minimal : LeanBuild.Request ← IO.ofExcept (fromJson? (Json.mkObj [
    ("repository", toJson request.repository), ("revision", toJson "main")]))
  check (minimal.targets.isEmpty && minimal.check.mode == .none && minimal.cache == .rebuild &&
    minimal.options.isEmpty && minimal.subdirectory == ".") "Wrong request defaults"
  let encoded ← IO.ofExcept (Json.parse "{\"repository\":\"https://github.com/a/b\",\"revision\":\"main\",\"options\":{\"greeting\":\"42\"},\"check\":{\"mode\":\"kernel\"}}")
  let decoded : LeanBuild.Request ← IO.ofExcept (fromJson? encoded)
  check (decoded.options["greeting"]? == some "42" && decoded.check.mode == .kernel) "JSON options/check mode"
  for seed in [:80] do
    let modules := (Array.range (4 + seed % 12)).map fun i => {
      name := s!"M{i}"
      imports := ((Array.range i).filter fun j => (i * 37 + j * 7 + seed) % 3 == 0).map (s!"M{·}") : LeanBuild.Module }
    IO.ofExcept (validateModules modules)
    let calls ← IO.mkRef (#[] : Array String)
    let plan := { fixturePlan with modules }
    let backend := { stub with
      prepare := fun _ => pure { plan := some plan }
      build := fun _ _ m done => do
        check (m.imports.all fun name => done.any fun r => r.name == name && r.status == .built)
          "Module ran before prerequisites"
        calls.modify (·.push m.name)
        return { name := m.name, status := if seed % 2 == 0 && m.name == "M1" then .failed else .built }
      finish := fun _ _ done => do
        check (done.size == modules.size && done.all (·.status == .built)) "Premature target completion"
        calls.modify (·.push "finish")
        return { name := "targets", status := .built }
      check := fun r _ _ => do
        calls.modify (·.push "check")
        return { mode := r.check.mode, success := true } }
    let req := { request with check := { mode := if seed % 3 == 0 then .kernel else .none } }
    let direct ← (DirectInterpreter.interpret noBlobs (workflow backend) req).run
    let saved ← IO.mkRef []
    let run := (SequentialReplay.interpret (journal saved) noBlobs 10000 (workflow backend) req).run
    let actual ← run
    check ((toJson direct).compress == (toJson actual).compress) "Direct/replay reports differ"
    let before ← calls.get
    discard run
    check ((← calls.get) == before) "Replay reran recorded jobs"
    if req.check.mode == .none then check (!before.contains "check") "Build-only invoked proof checker"
  for stage in ["prepare", "build", "finish", "check"] do
    let calls ← IO.mkRef (0 : Nat)
    let fail : IO Unit := do calls.modify (· + 1); throw (IO.userError "Job exception")
    let backend := { stub with
      prepare := fun r => do
        if stage == "prepare" then fail
        stub.prepare r
      build := fun r p m done => do
        if stage == "build" then fail
        stub.build r p m done
      finish := fun r p done => do
        if stage == "finish" then fail
        stub.finish r p done
      check := fun r p b => do
        if stage == "check" then fail
        stub.check r p b }
    let saved ← IO.mkRef []
    let req := { request with check := { mode := .kernel } }
    for _ in [:2] do
      let .error error ← (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) req).run
        | throw (IO.userError s!"{stage} exception not propagated")
      check (error == ⟨.application, "Job exception"⟩) "Wrong exception outcome"
    check ((← calls.get) == 1) s!"{stage} exception retried as a crash"
  for req in [
      { request with repository := "https://github.com/a/../b" },
      { request with revision := "--upload-pack=evil" },
      { request with subdirectory := "../escape" },
      { request with targets := #["--run=evil"] },
      { request with check := { mode := .kernel, allowedAxioms := #["sorryAx"] } }] do
    check req.validate.toOption.isNone "Invalid request accepted"
  for path in ["/etc/passwd", "../escape", "a/../../escape", "a//b"] do
    check (!Bundle.safePath path) "Unsafe artifact path accepted"
  check ((validateModules #[⟨"A", #["B"]⟩, ⟨"B", #["A"]⟩]).toOption.isNone) "Cycle accepted"
  check ((validateModules #[⟨"A", #[]⟩, ⟨"A", #[]⟩]).toOption.isNone) "Duplicate accepted"
  IO.println "PASS 80 generated DAGs: dependencies, direct/replay agreement, optional checking, durable exceptions"

private def copyFixture (source destination : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "cp", args := #["-R", source.toString ++ "/.", destination.toString] }
  check (out.exitCode == 0) "Fixture copy failed"
  if ← (destination / ".lake").pathExists then IO.FS.removeDirAll (destination / ".lake")
  if ← (destination / "Generated.lean").pathExists then IO.FS.removeFile (destination / "Generated.lean")

private def nativeTest (tools : Tools) (store : ObjectStore) (fixture : System.FilePath)
    (change : System.FilePath → IO Unit := fun _ => pure ())
    (req : LeanBuild.Request := request) : IO LeanBuild.Report :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    let cwd := if req.subdirectory == "." then directory else directory / req.subdirectory
    IO.FS.createDirAll cwd
    copyFixture fixture cwd
    change cwd
    let prepared ← tools.prepareDirectory store req directory "fixture-commit"
    let backend := { tools.backend store with prepare := fun _ => pure prepared }
    let result ← (DirectInterpreter.interpret noBlobs (workflow backend) req).run
    let .ok report := result | throw (IO.userError s!"Native workflow failed: {repr result}")
    return report

private def requireSuccess (report : LeanBuild.Report) : IO Unit :=
  check report.success s!"Build failed: {repr report}"

private def publicationTests (tools : Tools) (store : ObjectStore) (fixture : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    copyFixture fixture directory
    let sourceBytes ← IO.FS.readBinFile (directory / "Fixture/Base.lean")
    for artifact in [false, true] do
      let pending ← IO.mkRef true
      let flaky := { store with create := fun key bytes => do
        let saved ← store.create key bytes
        let target := if artifact then bytes.extract 0 5 == "olean".toUTF8 else bytes == sourceBytes
        if target then
          if ← pending.modifyGet fun old => (old, false) then throw (IO.userError "Publication failure")
        return saved }
      let backend := { tools.backend flaky with
        prepare := fun r => tools.prepareDirectory flaky r directory "fixture" }
      let saved ← IO.mkRef []
      for _ in [:2] do
        let .error error ← (SequentialReplay.interpret (journal saved) noBlobs 1000 (workflow backend) request).run
          | throw (IO.userError "Publication failure was swallowed")
        check (error == ⟨.application, "Publication failure"⟩) "Wrong publication error"
      check (!(← pending.get)) "Publication fault was not exercised"

private def bundleTests (store : ObjectStore) : IO Unit :=
  IO.FS.withTempDir fun root => do
    let source := root / "source"
    IO.FS.createDir source
    IO.FS.writeFile (source / "original") "linked content"
    let linked ← IO.Process.output {
      cmd := "ln", args := #["-s", "original", (source / "link").toString] }
    check (linked.exitCode == 0) "Cannot create source symlink fixture"
    let manifest ← (← Bundle.snapshot source 10000).publish store
    let restored := root / "restored"
    Bundle.restore store restored manifest 10000
    check ((← IO.FS.readFile (restored / "link")) == "linked content" &&
      (← (restored / "link").symlinkMetadata).type == .file) "Safe file link was not materialized"
    for action in [IO.FS.writeFile (restored / "original") "changed", IO.FS.removeFile (restored / "original")] do
      action
      let rejected ← try
        discard <| Bundle.delta restored 10000 manifest manifest
        pure false
      catch _ => pure true
      check rejected "A prerequisite was overwritten or deleted"
      Bundle.restore store restored manifest 10000
    let oversized ← try
      discard <| Bundle.delta restored 1 manifest
      pure false
    catch _ => pure true
    check oversized "Unchanged files did not count toward workspace size"
    IO.FS.removeFile (restored / "original")
    IO.FS.createDir (restored / "original")
    let replaced ← try
      discard <| Bundle.delta restored 10000 manifest manifest
      pure false
    catch _ => pure true
    check replaced "A prerequisite file was replaced by a directory"
    IO.FS.removeDir (restored / "original")
    Bundle.restore store restored manifest 10000
    IO.FS.removeFile (source / "link")
    for target in ["../restored/original", "."] do
      let linked ← IO.Process.output {
        cmd := "ln", args := #["-s", target, (source / "link").toString] }
      check (linked.exitCode == 0) "Cannot create rejected symlink fixture"
      let rejected ← try
        discard <| Bundle.snapshot source 10000
        pure false
      catch _ => pure true
      check rejected "Snapshot followed a directory or external symlink"
      IO.FS.removeFile (source / "link")
    let some first := manifest[0]? | throw (IO.userError "Missing snapshot entry")
    let other := { first with file := ← Files.putText store "conflicting" }
    check ((Bundle.merge #[first] #[other]).toOption.isNone) "Parallel artifact conflict accepted"

private def nativeTests : IO Unit := do
  let tools ← Tools.fromEnvironment
  let fixture ← IO.FS.realPath "fixtures/Diamond"
  let full ← IO.FS.realPath "fixtures/FullBuild"
  let store := objects (← IO.mkRef {})
  bundleTests store
  let built ← nativeTest tools store fixture
  requireSuccess built
  check (built.modules.size == 4 && built.verification.isNone && built.build.status == .built)
    "Build-only report is incorrect"
  let defaults ← nativeTest tools store fixture (req := { request with targets := #[] })
  requireSuccess defaults
  let reused ← nativeTest tools store fixture (req := { request with cache := .reuse, targets := #["+Fixture.Final:olean"] })
  requireSuccess reused
  let qualified ← nativeTest tools store fixture (req := { request with targets := #["@build_fixture/Fixture"] })
  requireSuccess qualified
  let oversized ← nativeTest tools store fixture (req := { request with limits := { request.limits with bytes := 1 } })
  check (!oversized.success && (oversized.message.splitOn "artifact byte limit").length > 1) "Oversized workspace accepted"
  let req := { request with check := { mode := .kernel, theorems := #["Fixture.result"] } }
  let report ← nativeTest tools store fixture (req := req)
  requireSuccess report
  let cached ← nativeTest tools store fixture (fun d => do
    IO.FS.writeFile (d / "Fixture/Unrelated.lean") "theorem unrelated : False := by sorry\n"
    let result ← IO.Process.output {
      cmd := (tools.toolchain / "bin/lake").toString
      cwd := d, args := #["--no-cache", "build", "+Fixture.Unrelated"] }
    check (result.exitCode == 0) "Cannot prepare unrelated cached module")
    { req with cache := .reuse }
  requireSuccess cached
  check (!cached.build.builtModules.contains "Fixture.Unrelated" && cached.build.builtModules.size == 4)
    "Unrelated cached modules entered the verification closure"
  let some verified := report.verification | throw (IO.userError "No verification report")
  check (verified.theorems.map (·.name) == #["Fixture.result"] && verified.exportFile.isSome)
    "Missing theorem or combined export"
  let some ref := report.build.artifacts | throw (IO.userError "No completed artifacts")
  let manifest : Bundle.Manifest ← Files.readJson store ref
  check (manifest.any (·.path.endsWith "Fixture/Final.olean")) "No final olean"
  publicationTests tools store fixture
  -- Native output must agree with an ordinary Lake build, including -K options,
  -- generated sources, default executable targets, C FFI and project subdirectories.
  for subdir in [".", "packages/app"] do
    let req := { request with targets := #[], subdirectory := subdir, options := ({} : Std.TreeMap String String).insert "greeting" "51" }
    let native ← nativeTest tools store full (req := req)
    requireSuccess native
    IO.FS.withTempDir fun root => do
      let actual := root / "actual"
      let some ref := native.build.artifacts | throw (IO.userError "Missing executable bundle")
      Bundle.restore store actual (← Files.readJson store ref) req.limits.bytes
      let binary := (if subdir == "." then actual else actual / subdir) / ".lake/build/bin/fixture_app"
      let actualRun ← IO.Process.output { cmd := binary.toString }
      let expected := root / "expected"
      IO.FS.createDir expected
      copyFixture full expected
      let built ← IO.Process.output {
        cmd := (tools.toolchain / "bin/lake").toString
        cwd := expected, args := #["--no-cache", "-Kgreeting=51", "build"] }
      check (built.exitCode == 0) s!"Reference Lake failed: {built.stderr}"
      let expectedRun ← IO.Process.output { cmd := (expected / ".lake/build/bin/fixture_app").toString }
      check (actualRun.exitCode == 0 && actualRun.stdout == expectedRun.stdout && actualRun.stdout == "52\n")
        "Distributed executable differs from ordinary Lake"
  let custom ← nativeTest tools store full (req := { request with targets := #["receipt"] })
  requireSuccess custom
  check custom.modules.isEmpty "Opaque custom target was treated as a Lean module"
  let some ref := custom.build.artifacts | throw (IO.userError "Custom artifact missing")
  let entries : Bundle.Manifest ← Files.readJson store ref
  let some entry := entries.find? (·.path == "receipt.txt") | throw (IO.userError "Output outside .lake/build lost")
  check ((← Files.readText store entry.file) == "built 41\n") "Wrong custom output"
  let replacement ← nativeTest tools store full (fun d => do
    IO.FS.writeFile (d / "replaced") "old file"
    IO.FS.writeFile (d / "deleted") "old file"
    let config ← IO.FS.readFile (d / "lakefile.lean")
    IO.FS.writeFile (d / "lakefile.lean") (config ++
      "\ntarget replaceFile pkg : FilePath := do\n  IO.FS.removeFile (pkg.dir / \"replaced\")\n  IO.FS.removeFile (pkg.dir / \"deleted\")\n  IO.FS.createDir (pkg.dir / \"replaced\")\n  let output := pkg.dir / \"replaced\" / \"result\"\n  IO.FS.writeFile output \"new file\"\n  return Job.pure output\n"))
    { request with targets := #["replaceFile"] }
  requireSuccess replacement
  IO.FS.withTempDir fun root => do
    let some ref := replacement.build.artifacts | throw (IO.userError "Missing replaced artifact")
    Bundle.restore store root (← Files.readJson store ref) request.limits.bytes
    check ((← IO.FS.readFile (root / "replaced/result")) == "new file" && !(← (root / "deleted").pathExists))
      "Final manifest resurrected replaced or deleted files"
  let overlap ← nativeTest tools store full (fun d => do
    let config ← IO.FS.readFile (d / "lakefile.lean")
    IO.FS.writeFile (d / "lakefile.lean") (config.replace "package full_build_fixture"
      "package full_build_fixture where\n  buildDir := \"../..\""))
    { request with subdirectory := "packages/app", targets := #[] }
  check (!overlap.success && (overlap.message.splitOn "must not contain a package").length > 1)
    "An overlapping build directory was cleaned"
  let unknown ← nativeTest tools store fixture (req := { request with targets := #["missing"] })
  check (!unknown.success) "Unknown Lake target accepted"
  let noProofs ← nativeTest tools store full (req := { request with targets := #["receipt"], check := { mode := .kernel } })
  check (!noProofs.success && noProofs.build.status == .built) "Vacuous proof-check success on a native-only target"
  let changedInput ← nativeTest tools store fixture (fun d => do
    IO.FS.writeFile (d / "prepared-input") "original"
    let code ← IO.FS.readFile (d / "Fixture/Base.lean")
    IO.FS.writeFile (d / "Fixture/Base.lean")
      ("import Lean\nrun_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile \"prepared-input\" \"changed\")\n" ++ code))
  check (!changedInput.success && changedInput.modules.any (fun m =>
    m.name == "Fixture.Base" && (m.message.splitOn "changed a prerequisite").length > 1))
    "A module job silently changed prepared inputs"
  let leanConfig ← nativeTest tools store fixture (fun d => do
    IO.FS.removeFile (d / "lakefile.toml")
    IO.FS.writeFile (d / "lakefile.lean") "import Lake\nopen Lake DSL\npackage build_fixture\nlean_lib Fixture\n")
  requireSuccess leanConfig
  let customDefaults ← nativeTest tools store fixture (fun d => do
    IO.FS.removeFile (d / "lakefile.toml")
    IO.FS.writeFile (d / "lakefile.lean")
      "import Lake\nopen Lake DSL\npackage build_fixture\nlean_lib Fixture where\n  defaultFacets := #[]\n"
    IO.FS.writeFile (d / "Fixture.lean") "This source is intentionally invalid.\n")
    { request with targets := #["Fixture"] }
  requireSuccess customDefaults
  check customDefaults.modules.isEmpty "Custom library defaults forced an unrelated Lean compilation"
  let runtime ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Base.lean")
      "namespace Fixture\ndef twice (n : Nat) := n + n\nunsafe def castValue (n : Nat) : Int := unsafeCast n\npartial def loop (n : Nat) : Nat := loop (n + 1)\ntheorem twice_zero : twice 0 = 0 := rfl\n")
  requireSuccess runtime
  let sorryReport ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nnamespace Fixture\ntheorem left : twice 1 = 2 := by sorry\n") req
  check (!sorryReport.success && sorryReport.build.status == .built &&
    sorryReport.verification.any (!·.success)) "Build success and proof rejection conflated"
  let bad ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean") "import Fixture.Base\nexample : False := True.intro\n")
  check (!bad.success && bad.modules.any (fun m => m.name == "Fixture.Final" && m.status == .blocked)) "Invalid proof accepted"
  for name in ["Fixture.missing", "Fixture.twice"] do
    let missing ← nativeTest tools store fixture (req := { req with check := { mode := .kernel, theorems := #[name] } })
    check (!missing.success && missing.build.status == .built) "Missing/non-theorem requirement accepted"
  let privateSorry ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean")
      "module\npublic import Fixture.Base\nprivate theorem hidden : False := by sorry\nnamespace Fixture\npublic theorem left : twice 1 = 2 := rfl\n") req
  check (!privateSorry.success) "Private sorry escaped verification"
  let assumption ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Left.lean")
      "import Fixture.Base\nnamespace Fixture\naxiom assumeLeft : twice 1 = 2\ntheorem left : twice 1 = 2 := assumeLeft\n") req
  check (!assumption.success) "Undeclared axiom accepted"
  let tighter ← nativeTest tools store fixture (fun d =>
    IO.FS.writeFile (d / "Fixture/Base.lean")
      "namespace Fixture\ndef twice (n : Nat) := n + n\ntheorem standardAxiom (p q : Prop) (h : p ↔ q) : p = q := propext h\n")
    { req with check := { mode := .kernel, allowedAxioms := #[] } }
  check (!tighter.success) "Stricter axiom policy ignored"
  let paranoid ← nativeTest tools store fixture (req := { req with targets := #["+Fixture.Base"], check := { mode := .paranoid } })
  requireSuccess paranoid
  let some verifiedParanoid := paranoid.verification | throw (IO.userError "Missing paranoid result")
  let some log := verifiedParanoid.diagnostics | throw (IO.userError "Missing checker log")
  let text ← Files.readText store log
  for name in ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"] do
    check ((text.splitOn s!"{name} kernel accepts").length > 1) s!"Skipped checker {name}"
  -- Corrupt an exported proof: it must reach the kernel and be rejected.
  IO.FS.withTempDir fun root => do
    let directory := root / "check"
    IO.FS.createDir directory
    let some exportRef := verified.exportFile | throw (IO.userError "No export")
    let path := root / "proof.ndjson"
    Files.download store exportRef path req.limits.bytes
    check (← tools.verifyExport directory req.limits path).isOk "Published export cannot be rechecked"
    if System.Platform.isOSX then
      check (!(← { tools with sandbox := true }.verifyExport directory req.limits path).isOk) "Sandbox silently bypassed"
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
    check changed "No theorem to corrupt"
    IO.FS.writeFile path (String.intercalate "\n" lines.toList ++ "\n")
    check (!(← tools.verifyExport directory req.limits path).isOk) "Corrupt proof accepted"
    check (((← IO.FS.readFile (root / "check.stdout")).splitOn "Lean default kernel rejected").length > 1)
      "Corrupt proof did not reach kernel"
    IO.FS.writeFile path "{}\nnot NDJSON\n"
    check (!(← tools.verifyExport directory req.limits path).isOk) "Malformed export accepted"
  for version in ["4.34.1", "4.36.0"] do
    let mismatch ← nativeTest tools store fixture (fun d =>
      IO.FS.writeFile (d / "lean-toolchain") s!"leanprover/lean4:v{version}\n")
    check (!mismatch.success && mismatch.build.status == .failed) "Toolchain mismatch accepted"
  IO.println "PASS native Lake builds, executable/FFI/generated/custom targets, subdirectories, exports and kernel rejection"

def main (args : List String) : IO Unit := do
  generatedTests
  if args.contains "--native" then nativeTests
