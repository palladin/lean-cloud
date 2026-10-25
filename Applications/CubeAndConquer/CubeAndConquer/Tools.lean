import CubeAndConquer.Dimacs
import CubeAndConquer.Process
import CubeAndConquer.Input

namespace CubeAndConquer
open Lean LeanCloud LeanCloudRuntime

/-- Deployment policy; submitted jobs cannot choose executable paths. -/
structure Limits where
  inputBytes : Nat := 1024 * 1024 * 1024
  proofBytes : Nat := 16 * 1024 * 1024 * 1024
  logBytes : Nat := 256 * 1024 * 1024
  variables : Nat := 10000000

structure Tools where
  directory : System.FilePath
  identity : Toolchain
  limits : Limits := {}
  cache : Option System.FilePath := none

private def limitEnv (name : String) (fallback : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => return fallback
  | some text =>
    let some value := text.toNat? | throw (IO.userError s!"{name} must be positive")
    unless value > 0 do throw (IO.userError s!"{name} must be positive")
    return value

def Tools.fromEnvironment : IO Tools := do
  let some directory ← IO.getEnv "LEAN_CLOUD_SAT_TOOLS"
    | throw (IO.userError "Set LEAN_CLOUD_SAT_TOOLS to the pinned tools directory")
  let directory ← IO.FS.realPath directory
  let lock ← IO.FS.readFile (directory / ".." / "tools.lock")
  let identity : Toolchain := { binaries := ← IO.FS.readFile (directory / ".." / "bin.sha256") }
  for (key, revision) in [("KISSAT_REV", identity.kissat), ("MARCH_REV", identity.march), ("DRAT_REV", identity.checker)] do
    unless (lock.splitOn "\n").contains s!"{key}={revision}" do
      throw (IO.userError "SAT tools do not match the application's pinned revisions")
  for executable in ["march_cu", "kissat", "drat-trim"] do
    let hash ← Files.digest (directory / executable)
    unless (identity.binaries.splitOn "\n").contains s!"{hash} {executable}" do
      throw (IO.userError s!"{executable} differs from its recorded build digest")
  let limits : Limits := {
    inputBytes := ← limitEnv "LEAN_CLOUD_SAT_INPUT_BYTES" ({} : Limits).inputBytes
    proofBytes := ← limitEnv "LEAN_CLOUD_SAT_PROOF_BYTES" ({} : Limits).proofBytes
    logBytes := ← limitEnv "LEAN_CLOUD_SAT_LOG_BYTES" ({} : Limits).logBytes
    variables := ← limitEnv "LEAN_CLOUD_SAT_VARIABLES" ({} : Limits).variables }
  let cache := (← IO.getEnv "LEAN_CLOUD_SAT_CACHE").filter (!·.isEmpty) |>.map System.FilePath.mk
  return { directory, identity, limits, cache }

private def withInput (tools : Tools) (store : ObjectStore) (request : Request)
    (concurrency : Nat) (action : System.FilePath → Dimacs.Info → IO α) : IO α := do
  IO.ofExcept request.validate
  Input.withFile store tools.cache request.cnf tools.limits.inputBytes concurrency fun path => do
    let info ← Dimacs.scan path
    unless info.variables ≤ tools.limits.variables do throw (IO.userError "CNF exceeds configured variable limit")
    action path info

private def solverStatus (path : System.FilePath) : IO String := do
  let statuses ← IO.mkRef (#[] : Array String)
  Dimacs.lines path fun line => do
    match (words line).toList with
    | ["s", status] => statuses.modify (·.push status)
    | _ => pure ()
  let #[status] ← statuses.get | throw (IO.userError "Expected exactly one solver status")
  return status

private def saveModel (store : ObjectStore) (tools : Tools) (original output : System.FilePath)
    (info : Dimacs.Info) (cube : Cube) (directory : System.FilePath) : IO Answer := do
  let checked ← try
    let model ← Dimacs.model output info.variables
    discard <| Dimacs.scan original (some model)
    unless cube.all (literalHolds model) do throw (IO.userError "Model violates cube assumptions")
    pure (.ok model : Except String (Array Bool))
  catch error => pure (.error s!"Invalid SAT model: {error}")
  let .ok model := checked | return .error "Invalid SAT model; see solver log"
  let path := directory / "model.sat"
  Dimacs.writeModel path model
  return .sat (← Files.upload store path tools.limits.logBytes)

/-- A checker must return both success and its verification marker. Its timeout,
crash, malformed proof or exhausted budget cannot turn into UNSAT. -/
def Tools.verifyProof (tools : Tools) (formula proof : System.FilePath) (seconds : Nat)
    (directory : System.FilePath) : IO (Bool × System.FilePath) := do
  let output := directory / "checker.stdout"
  let errors := directory / "checker.stderr"
  let result ← Process.runFiles {
    cmd := (tools.directory / "drat-trim").toString
    args := #[formula.toString, proof.toString, "-t", toString seconds]
    cwd := some directory } (seconds * 1000 + 1000) output errors tools.limits.logBytes
  let verified := (result.stdout.splitOn "\n").any (fun line => line.trimAscii.toString == "s VERIFIED")
  -- Pinned drat-trim's main returns 1 when parsing alone finds an empty clause:
  -- it prints VERIFIED but leaves `sts` unset (upstream drat-trim.c:1478–1500).
  -- Accept only that exact verified path, never a generic nonzero exit.
  let trivial := (result.stdout.splitOn "\n").any (fun line => line.trimAscii.toString == "c trivial UNSAT")
  let acceptedExit := result.exitCode == 0 || (result.exitCode == 1 && trivial)
  return (!result.stopped && acceptedExit && verified, output)

private def loadPlan (store : ObjectStore) (request : Request) (ref : FileRef) : IO CubePlan := do
  let plan : CubePlan ← Files.readJson store ref
  unless plan.input == request.cnf && plan.cubes.size ≤ request.maxCubes &&
      plan.cubes.all (fun cube => cube.length ≤ request.depth) do
    throw (IO.userError "Cube plan does not match the request")
  IO.ofExcept (validateCubes plan.variables plan.cubes)
  return plan

private def conquerFromFile (tools : Tools) (store : ObjectStore) (request : Request)
    (original : System.FilePath) (info : Dimacs.Info) (cube : Cube) : IO CubeResult :=
  IO.FS.withTempDir fun directory => do
    IO.ofExcept (validateCube info.variables cube)
    let formula := directory / "cube.cnf"
    let proof := directory / "proof.drat"
    let output := directory / "solver.stdout"
    let errors := directory / "solver.stderr"
    Dimacs.withCube original formula info cube
    let result ← Process.runFiles {
      cmd := (tools.directory / "kissat").toString
      args := #[s!"--time={request.seconds}", formula.toString, proof.toString]
      cwd := some directory } (request.seconds * 1000 + 1000) output errors tools.limits.logBytes
        #[(proof, tools.limits.proofBytes)]
    let log ← Files.putJson store (Json.mkObj [
      ("stdout", toJson (← Files.upload store output tools.limits.logBytes)),
      ("stderr", toJson (← Files.upload store errors tools.limits.logBytes)),
      ("exitCode", toJson result.exitCode.toNat), ("stopped", toJson result.stopped)])
    let answer : Answer ← (do
      if result.stopped then return .unknown "Solver deadline or file limit reached"
      let status ← try pure (.ok (← solverStatus output) : Except String String)
        catch error => pure (.error error.toString)
      let .ok status := status | return .error "Missing or conflicting solver status; see task log"
      match result.exitCode, status with
      | 10, "SATISFIABLE" => saveModel store tools original output info cube directory
      | 20, "UNSATISFIABLE" => do
          unless ← proof.pathExists do return .error "Solver omitted its UNSAT proof"
          return .unverified (← Files.upload store formula (tools.limits.inputBytes + 1024 * 1024))
            (← Files.upload store proof tools.limits.proofBytes)
      | 0, "UNKNOWN" => pure (.unknown "Solver returned UNKNOWN")
      | code, _ => pure (.error s!"Unexpected Kissat exit/status: {code}/{status}"))
    return { cube, answer, log }

def Tools.conquer (tools : Tools) (store : ObjectStore) (request : Request)
    (cube : Cube) : IO CubeResult :=
  withInput tools store request 1 fun original info =>
    conquerFromFile tools store request original info cube

/-- One private solver workspace per cube. The shared CNF remains read-only,
and the bounded pool joins every started task before releasing it. -/
def Tools.conquerBatch (tools : Tools) (store : ObjectStore) (env : Environment IO)
    (request : Request) (cubes : Array Cube) : IO (Array CubeResult) :=
  withInput tools store request env.currentWorker.cpus fun original info =>
    Parallel.map env.currentWorker.cpus cubes (conquerFromFile tools store request original info)

/-- A separate durable action reuses the published certificate after a node
crashes during checking. No solver workspace or local pathname crosses this boundary. -/
private def verifyFromFile (tools : Tools) (store : ObjectStore) (request : Request)
    (original : System.FilePath) (info : Dimacs.Info) (result : CubeResult) : IO CubeResult := do
  let .unverified formula proof := result.answer | return result
  IO.FS.withTempDir fun directory => do
    let cnf := directory / "cube.cnf"
    let certificate := directory / "proof.drat"
    let expected := directory / "expected.cnf"
    IO.ofExcept (validateCube info.variables result.cube)
    Dimacs.withCube original expected info result.cube
    unless formula.sha256 == (← Files.digest expected) do
      return { result with answer := .error "Proof formula does not match input and cube" }
    Files.download store formula cnf (tools.limits.inputBytes + 1024 * 1024)
    Files.download store proof certificate tools.limits.proofBytes
    let (verified, output) ← tools.verifyProof cnf certificate request.verifySeconds directory
    let verification ← Files.upload store output tools.limits.logBytes
    let errors ← Files.upload store (directory / "checker.stderr") tools.limits.logBytes
    let log ← Files.putJson store (Json.mkObj [
      ("solver", toJson result.log), ("formula", toJson formula), ("proof", toJson proof),
      ("checker", toJson verification), ("checkerErrors", toJson errors), ("verified", toJson verified)])
    return { result with
      log := log
      answer := if verified then .unsat formula proof verification
        else .unknown "UNSAT proof verification failed or exceeded its budget; see task log" }

def Tools.verify (tools : Tools) (store : ObjectStore) (request : Request)
    (result : CubeResult) : IO CubeResult := do
  let .unverified .. := result.answer | return result
  withInput tools store request 1 fun original info =>
    verifyFromFile tools store request original info result

def Tools.verifyBatch (tools : Tools) (store : ObjectStore) (env : Environment IO)
    (request : Request) (results : Array CubeResult) : IO (Array CubeResult) := do
  unless results.any (fun result => match result.answer with | .unverified .. => true | _ => false) do
    return results
  withInput tools store request env.currentWorker.cpus fun original info =>
    Parallel.map env.currentWorker.cpus results (verifyFromFile tools store request original info)

/-- Cubing is local to the supplied assumptions. Its output contains only new
choices; the workflow appends them to the parent before dispatching children. -/
def Tools.cube (tools : Tools) (store : ObjectStore) (request : Request) (parent : Cube) : IO Cubing :=
  withInput tools store request 1 fun original info =>
  IO.FS.withTempDir fun directory => do
    IO.ofExcept (validateCube info.variables parent)
    let depth := min request.splitDepth (request.depth - parent.length)
    if depth == 0 || info.variables == 0 then return .leaf
    let input := directory / "parent.cnf"
    Dimacs.withCube original input info parent
    let output := directory / "cubes.icnf"
    let stdout := directory / "cuber.stdout"
    let stderr := directory / "cuber.stderr"
    let result ← Process.runFiles {
      cmd := (tools.directory / "march_cu").toString
      args := #[input.toString, "-d", toString depth, "-o", output.toString]
      cwd := some directory } (request.seconds * 1000) stdout stderr tools.limits.logBytes
        #[(output, 16 * 1024 * 1024)]
    let finished (answer : Answer) : IO Cubing := do
      let log ← Files.putJson store (Json.mkObj [
        ("stdout", toJson (← Files.upload store stdout tools.limits.logBytes)),
        ("stderr", toJson (← Files.upload store stderr tools.limits.logBytes)),
        ("exitCode", toJson result.exitCode.toNat), ("stopped", toJson result.stopped)])
      return .finished { cube := parent, answer, log }
    if result.stopped then return ← finished (.unknown "Cuber deadline or output limit reached")
    if result.exitCode == 10 then
      return ← finished (← saveModel store tools original stdout info parent directory)
    unless result.exitCode == 0 || result.exitCode == 20 do
      return ← finished (.error s!"Unexpected march exit {result.exitCode}")
    unless ← output.pathExists do return ← finished (.error "Cuber did not produce a cube file")
    let parsed := parseCubes info.variables (2 ^ depth) (← IO.FS.readFile output)
    let .ok children := parsed | return ← finished (.error "Cuber did not produce a complete valid cube cover")
    -- march may refute the parent or produce no further decisions. In both
    -- cases Kissat must provide a checked certificate for that exact parent.
    if children == #[[]] then return .leaf
    match validateSplit parent depth children with
    | .error reason => finished (.error reason)
    | .ok () => return .split children

/-- Validate collection/coverage independently of completion order. Repeated or
missing results cannot establish UNSAT. Cubes themselves identify the leaves. -/
def validateResults (plan : CubePlan) (results : Array CubeResult) : Except String Unit := do
  validateCubes plan.variables plan.cubes
  let leaves := Std.HashSet.ofArray plan.cubes
  let mut seen : Std.HashSet Cube := {}
  for result in results do
    unless !seen.contains result.cube && leaves.contains result.cube do
      throw "Duplicate or mismatched cube result"
    seen := seen.insert result.cube

def Tools.finish (tools : Tools) (store : ObjectStore) (request : Request)
    (results : Array CubeResult) : IO Report := withInput tools store request 1 fun _ info => do
  let plan : CubePlan := { input := request.cnf, variables := info.variables, cubes := results.map (·.cube) }
  unless plan.cubes.size ≤ request.maxCubes && plan.cubes.all (fun cube => cube.length ≤ request.depth) do
    throw (IO.userError "Final cube plan exceeds request limits")
  IO.ofExcept (validateResults plan results)
  let bundle : Bundle := { request, plan := ← Files.putJson store plan, results, tools := tools.identity }
  return {
    outcome := aggregate plan.cubes.size results
    bundle := ← Files.putJson store bundle
    totalCubes := plan.cubes.size
    solvedCubes := (results.filter (fun result => match result.answer with | .sat _ | .unsat .. => true | _ => false)).size }

/-- Recheck downloaded evidence from scratch, including exact cube-CNF binding.
This command does not trust the original worker or the report's status. -/
def Tools.verifyBundle (tools : Tools) (store : ObjectStore) (ref : FileRef) : IO Conclusion := do
  let bundle : Bundle ← Files.readJson store ref
  unless bundle.format == "cube-and-conquer/bundle/v2" do throw (IO.userError "Unknown bundle format")
  withInput tools store bundle.request 1 fun original info =>
  IO.FS.withTempDir fun directory => do
    let plan ← loadPlan store bundle.request bundle.plan
    unless plan.variables == info.variables do throw (IO.userError "Plan variables mismatch")
    IO.ofExcept (validateResults plan bundle.results)
    for result in bundle.results do
      match result.answer with
      | .sat ref =>
        let output := directory / "check-model.sat"
        Files.download store ref output tools.limits.logBytes
        let model ← Dimacs.model output info.variables
        discard <| Dimacs.scan original (some model)
        unless result.cube.all (literalHolds model) do throw (IO.userError "Model violates cube assumptions")
      | .unsat formula proof _ =>
        IO.FS.withTempDir fun task => do
          let expected := task / "expected.cnf"
          Dimacs.withCube original expected info result.cube
          unless formula.sha256 == (← Files.digest expected) do
            throw (IO.userError "Proof formula does not match the original CNF and cube")
          let actual := task / "cube.cnf"
          let certificate := task / "proof.drat"
          Files.download store formula actual (tools.limits.inputBytes + 1024 * 1024)
          Files.download store proof certificate tools.limits.proofBytes
          unless (← tools.verifyProof actual certificate bundle.request.verifySeconds task).1 do
            throw (IO.userError s!"Invalid proof for cube {result.cube}")
      | _ => pure ()
    return aggregate plan.cubes.size bundle.results

end CubeAndConquer
