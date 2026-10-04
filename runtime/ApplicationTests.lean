import LeanCloudRuntime.Application
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
  | .scheduler _ _ => do modify (fun w => { w with services := w.services.push "scheduler" }); return .ok ()
  | .worker _ _ => do modify (fun w => { w with services := w.services.push "worker" }); return .ok ()
  | .definition _ _ => return .ok ⟨program.info.entry, Json.null, program.info.resultSchema⟩
  | .outcome _ _ => return .ok (some (.success (toJson (42 : Nat))))
  | .cancel _ _ => return .ok (.cancelled "Killed by user")
  | .status _ _ => return .ok {}
  | .readText _ _ => return .error "A Nat result must not be treated as a blob"

def run : IO Unit := do
  let registry : Registry := ⟨#[program.register]⟩
  for (args, expected) in [(["programs"], 0), (["validate", "user-program/v1"], 0),
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

end ApplicationTests
