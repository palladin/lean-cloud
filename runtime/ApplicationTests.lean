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
  | .remove _ _ | .purge _ _ => return .ok ()
  | .membership _ => return .ok {}
  | .runs _ _ _ => return .ok #[("one", .active)]
  | .mode _ _ => return .ok .active
  | .durableControl _ _ _ => return .ok (.ok ())
  | .nodes _ => return .ok #[]
  | .observations _ _ _ _ _ => return .ok { items := #[] }
  | .definition _ _ => return .ok { entry := program.info.entry, input := Json.null, resultSchema := program.info.resultSchema }
  | .outcome _ _ => return .ok (some (.success (toJson (42 : Nat))))
  | .cancel _ _ => return .ok (some (.cancelled "Killed by user"))
  | .status _ _ => return .ok {}
  | .readText _ _ => return .error "A Nat result must not be treated as a blob"

private def failedControl (uncertain : Bool) : Application.Service α → StateM World (Except String α)
  | .durableControl _ _ _ => return if uncertain then .error "Scheduler timeout" else .ok (.error "Rejected")
  | op => service op

def run : IO Unit := do
  let key := "runs/example/records/" ++ String.ofList (List.replicate 64 'a')
  let page (contents : String) := s!"<ListBucketResult><KeyCount>1</KeyCount><Contents><Key>{contents}</Key></Contents></ListBucketResult>"
  let keys xml := S3.listKeys xml >>= ObjectStore.runRecordKeys "example"
  assertEq (← unwrap (keys (page key))) #[key]
  assertEq (← unwrap (keys (page (key.replace "/" "%2F")))) #[key]
  for invalid in ["objects/" ++ String.ofList (List.replicate 64 'a'),
      key.replace "example" "other", key ++ "/../objects", "runs/example/records/short"] do
    assertTrue (keys (page invalid)).toOption.isNone "Unsafe cleanup listing accepted"
  assertTrue (keys "<ListBucketResult></ListBucketResult>").toOption.isNone
    "Malformed empty listing was accepted"
  let json ← unwrap (Json.parse (include_str "../deploy/config.json"))
  assertTrue (fromJson? (α := Config) (json.setObjVal! "formatVersion" (toJson (999 : Nat)))).toOption.isNone
    "Future runtime configuration was accepted"
  let legacy := Json.mkObj ((← unwrap json.getObj?).toList.filter (·.1 != "worker"))
  let old : Config ← unwrap (fromJson? legacy)
  assertEq old.worker ({} : ExecutionConfig) "Legacy config lost defaults"
  let some route := old.mailboxes.workers[0]? | throw (IO.userError "Missing fixture worker")
  assertEq route.cpus 1 "Legacy worker lost its conservative CPU budget"
  assertTrue route.memoryMiB.isNone "Legacy worker fabricated a memory budget"
  for invalid in [{ route with cpus := 0 }, { route with memoryMiB := some 0 }] do
    assertTrue ({ old.mailboxes with workers := #[invalid] }.validate).toOption.isNone
      "Invalid worker budget was accepted"
  for (field, value) in [("cpus", Json.null), ("cpus", toJson false),
      ("memoryMiB", toJson false), ("memoryMiB", toJson "8192")] do
    assertTrue (fromJson? (α := HttpMailbox.WorkerEndpoint)
      ((toJson route).setObjVal! field value)).toOption.isNone "Malformed worker budget used defaults"
  assertTrue (fromJson? (α := Config) (json.setObjVal! "worker" Json.null)).toOption.isNone
    "Invalid limits silently used defaults"
  let entry : CloudProgram Nat Nat := { name := "fuel", version := "v1", run := fun n => do
    let value ← Cloud.pure (fun _ => n + 1)
    Cloud.pure (fun _ => value + 1) }
  let registered := registerProgram entry #[]
  let journal ← IO.mkRef ([] : List (String × ReplayRecord))
  let store : ReplayStore IO := {
    read := fun key => return (← journal.get).lookup key
    create := fun key record => do
      match (← journal.get).lookup key with
      | some existing => return existing
      | none => journal.modify ((key, record) :: ·); return record }
  let blobs : ExecContext IO := {
    blobs := {
      putBlob := fun _ => throw ⟨.unsupported, "unexpected blob"⟩
      readBlob := fun _ => throw ⟨.unsupported, "unexpected blob"⟩
      resolveBlob := fun _ => throw ⟨.unsupported, "unexpected blob"⟩ } }
  let definition : RunDefinition := { entry := entry.info.entry, input := toJson (5 : Nat), resultSchema := entry.info.resultSchema }
  let historical : RunDefinition := { definition with image := some "sha256:old", program := some entry.info }
  let recovered : RunDefinition ← unwrap (fromJson? (toJson historical))
  assertEq recovered.image historical.image
  assertEq (recovered.program.map toJson) (historical.program.map toJson) "Saved source metadata changed"
  assertTrue (recovered.sameSubmission historical) "Identical submission rejected"
  assertTrue (!(recovered.sameSubmission { historical with image := some "sha256:new" })) "Run reused across releases"
  assertTrue (!(recovered.sameSubmission { historical with input := toJson (6 : Nat) })) "Run reused for different input"
  let legacyDefinition : RunDefinition ← unwrap (fromJson? (Json.mkObj [
    ("entry", toJson definition.entry), ("input", definition.input), ("resultSchema", toJson definition.resultSchema)]))
  assertTrue (legacyDefinition.image.isNone && legacyDefinition.program.isNone) "Legacy source/release invented"
  let trace ← Trace.create "config-test"
  let assignment : Assignment := ⟨0, Location.root⟩
  let limited ← registered.execute { interpreterFuel := 1 } definition "test" ⟨store, pure #[]⟩ trace assignment blobs
  assertError limited.progress .protocol
  assertTrue ((← journal.get).lookup (ReplayStore.returnKey Location.root)).isNone
    "Fuel exhaustion published completion"
  let completed ← registered.execute { interpreterFuel := 10 } definition "test" ⟨store, pure #[]⟩ trace assignment blobs
  assertOutcome completed.progress (.ok .done)
  let some root := (← journal.get).lookup (ReplayStore.returnKey Location.root)
    | throw (IO.userError "Configured worker did not finish")
  assertEq root.outcome (.success (toJson (7 : Nat)))
  -- The registered worker path includes tracing. A user IO exception completes
  -- the assignment with a durable failure; it does not escape or restart the node.
  journal.set []
  let calls ← IO.mkRef (0 : Nat)
  let throwing : CloudProgram Nat Nat := {
    name := "throws", version := "v1"
    run := fun n => Cloud.exec fun _ => do
      let previous ← calls.modifyGet fun count => (count, count + 1)
      if previous == 0 then throw (IO.userError "application exception")
      return n }
  let throwingDefinition : RunDefinition := {
    entry := throwing.info.entry, input := toJson (5 : Nat), resultSchema := throwing.info.resultSchema }
  for _ in [:2] do
    let done ← (registerProgram throwing #[]).execute {} throwingDefinition "test"
      ⟨store, pure #[]⟩ trace assignment blobs
    assertOutcome done.progress (.ok .done)
  assertEq (← calls.get) 1 "Registered worker retried user IO"
  assertOutcome (← store.outcome.run) (.ok (some (.failure ⟨.application, "application exception"⟩)))
  -- The same worker can execute another workflow after that failure.
  journal.set []
  let next ← registered.execute {} definition "test" ⟨store, pure #[]⟩ trace assignment blobs
  assertOutcome next.progress (.ok .done)
  assertOutcome (← store.outcome.run) (.ok (some (.success (toJson (7 : Nat)))))
  journal.set []
  let resources : CloudProgram Unit Nat := {
    name := "resources", version := "v1"
    run := fun _ => Cloud.exec fun env => pure env.currentWorker.cpus }
  let resourceDefinition : RunDefinition := {
    entry := resources.info.entry, input := toJson (), resultSchema := resources.info.resultSchema }
  let environment : ExecContext IO := { blobs with currentWorker := { id := "test", cpus := 6 } }
  let used ← (registerProgram resources #[]).execute {} resourceDefinition "test"
    ⟨store, pure #[]⟩ trace assignment environment
  assertOutcome used.progress (.ok .done)
  assertOutcome (← store.outcome.run) (.ok (some (.success (toJson (6 : Nat)))))
  let registry : Registry := ⟨#[program.register]⟩
  let config : Config ← unwrap (fromJson? json)
  let client : ClientConfig := ⟨"test", "sha256:app", "public-token"⟩
  let action := Application.deploymentRun registry config client (.control "request" "one" .pause)
  let (rejected, _) := (Application.runWith host (failedControl false) action).run {}
  let (uncertain, _) := (Application.runWith host (failedControl true) action).run {}
  assertEq (toJson rejected) (toJson (.ok (.error "Rejected") : Except String (Except String Unit)))
    "Recorded rejection lost its receipt boundary"
  assertEq (toJson uncertain) (toJson (.error "Scheduler timeout" : Except String (Except String Unit)))
    "Transport failure looked like a confirmed rejection"
  -- Registration at a different module bundles both imported workflow files.
  let some registered := LeanCloudRuntime.programs.programs[0]? | throw (IO.userError "No registered programs")
  assertTrue (registered.info.sources.any (·.file.endsWith "Demo.lean")) "Imported demo source missing"
  assertTrue (registered.info.sources.any (·.file.endsWith "Squares.lean")) "Imported helper source missing"
  assertTrue (registered.info.sources.all fun file => !file.sites.isEmpty) "Empty source map"
  let _ ← unwrap LeanCloudRuntime.programs.validate

  let saved : LeanCloudRuntime.Pool.Saved ← unwrap (fromJson? (Json.mkObj [
    ("state", Json.mkObj [("runs", toJson (#[] : Array LeanCloud.Pool.Run)), ("cursor", toJson (0 : Nat))]),
    ("replies", toJson (#[] : Array (String × Except String Json)))]))
  assertTrue (fromJson? (α := LeanCloudRuntime.Pool.Saved)
    ((toJson saved).setObjVal! "formatVersion" (toJson (999 : Nat)))).toOption.isNone "Future catalog was accepted"
  assertTrue saved.routes.isNone "Legacy scheduler state fabricated routes"
  assertTrue saved.timings.isEmpty "Legacy scheduler state fabricated timestamps"
  let timing : LeanCloud.Timing.Run := { span := some ⟨1000, some 3000⟩, observedMs := 3000 }
  let restored : LeanCloudRuntime.Pool.Saved ← unwrap (fromJson? (toJson { saved with timings := #[ ("one", timing) ] }))
  assertEq restored.timings #[("one", timing)] "Saved scheduler timing did not roundtrip"
  for (args, expected) in [(["programs"], 0), (["validate", "user-program/v1"], 0),
      (["serve-scheduler", "config"], 0), (["serve-worker", "config"], 0),
      (["pool-workers", "config"], 0), (["pool-stopped", "config", "worker1", "2"], 0),
      (["pause", "config", "one"], 0), (["resume", "config", "one"], 0),
      (["submit-entry", "config", "one", "user-program/v1", "-"], 0),
      (["worker", "config", "one"], 1), (["scheduler", "config", "one"], 1), (["reference-status", "config", "one"], 1),
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
