import LeanCloudRuntime.Application
import LeanCloudRuntime.Programs
import LeanCloudTests.Support

namespace ApplicationTests
open Lean LeanCloud LeanCloudRuntime LeanCloudCli LeanCloudTests

private def program : CloudProgram (Array Nat) Nat := {
  name := "user-program", version := "v1"
  run := fun input => pure (input.foldl (· + ·) 0)
  sampleInput := some #[1, 2, 3] }

private structure World where
  input : String := "[1,2,3]"
  output : String := ""
  services : Array String := #[]

private def host : HostOp α → StateM World (Except String α)
  | .readFile path => pure (if path.toString == "config" then .ok (include_str "../deploy/config.json") else .error "Missing file")
  | .readLine => return .ok (← get).input
  | .write text _ => do modify fun w => { w with output := w.output ++ text }; return .ok ()
  | _ => pure (.error "Unexpected host request")

private def service : Application.Service α → StateM World (Except String α)
  | .submit _ _ entry _ => do modify (fun w => { w with services := w.services.push entry }); return .ok ()
  | .health _ | .serveScheduler _ | .serveWorker _ | .control _ _ _
  | .configure _ _ | .workerStopped _ _ _ => return .ok ()
  | .membership _ => return .ok {}
  | .scheduler _ _ => do modify (fun w => { w with services := w.services.push "scheduler" }); return .ok ()
  | .worker _ _ => do modify (fun w => { w with services := w.services.push "worker" }); return .ok ()
  | .definition _ _ => return .ok ⟨program.info.entry, Json.null, program.info.resultSchema⟩
  | .outcome _ _ => return .ok (some (.success (toJson (42 : Nat))))
  | .cancel _ _ => return .ok (.cancelled "Killed by user")
  | .status _ _ | .referenceStatus _ _ => return .ok {}
  | .readText _ _ => return .error "A Nat result must not be treated as a blob"

def run : IO Unit := do
  let registry : Registry := ⟨#[program.register]⟩
  -- Registration at a different module bundles both imported workflow files.
  let some registered := LeanCloudRuntime.programs.programs[0]? | throw (IO.userError "No registered programs")
  assertTrue (registered.info.sources.any (·.file.endsWith "Demo.lean")) "Imported demo source missing"
  assertTrue (registered.info.sources.any (·.file.endsWith "Squares.lean")) "Imported helper source missing"
  assertTrue (registered.info.sources.all fun file => !file.sites.isEmpty) "Empty source map"
  let _ ← unwrap LeanCloudRuntime.programs.validate

  let saved : LeanCloudRuntime.Pool.Saved ← unwrap (fromJson? (Json.mkObj [
    ("state", Json.mkObj [("runs", toJson (#[] : Array LeanCloud.Pool.Run)), ("cursor", toJson (0 : Nat))]),
    ("replies", toJson (#[] : Array (String × Except String Json)))]))
  assertTrue saved.routes.isNone "Legacy scheduler state fabricated routes"
  for (args, expected) in [(["programs"], 0), (["validate", "user-program/v1"], 0),
      (["serve-scheduler", "config"], 0), (["serve-worker", "config"], 0),
      (["pool-workers", "config"], 0), (["pool-stopped", "config", "worker1", "2"], 0),
      (["pause", "config", "one"], 0), (["resume", "config", "one"], 0),
      (["submit-entry", "config", "one", "user-program/v1", "-"], 0),
      (["worker", "config", "one"], 0), (["scheduler", "config", "one"], 0),
      (["result", "config", "one"], 0), (["cancel", "config", "one"], 0), (["submit", "config", "one"], 0),
      (["worker", "config", "../invalid"], 1), (["worker", "config", "one", "unexpected"], 1)] do
    let (actual, world) := (Application.runWith host service (Application.run registry args)).run {}
    assertEq (← unwrap actual) expected
    if args.head? == some "result" then assertEq world.output "42\n"
    if args.head? == some "cancel" then
      let outcome ← unwrap (Json.parse world.output >>= fromJson? (α := Exit))
      assertEq outcome (.cancelled "Killed by user")
    if expected == 1 then assertTrue world.services.isEmpty "Invalid command reached a runtime service"
  let (actual, world) := (Application.runWith host service (Application.run registry ["validate", "user-program/v1"])).run
    { input := "\"bad input\"" }
  assertEq (← unwrap actual) 1
  assertTrue world.services.isEmpty "Invalid input reached a runtime service"
  for input in ["[]", "[1]", "not JSON"] do
    let (actual, _) := (Application.runWith host service (Application.run registry ["pool-configure", "config"])).run { input }
    assertEq (← unwrap actual) (if input == "[]" then 0 else 1)

end ApplicationTests
