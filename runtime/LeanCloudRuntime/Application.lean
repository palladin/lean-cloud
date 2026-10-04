import LeanCloudRuntime.Program
import LeanCloudCli.IO
import LeanCloudCli.Model

namespace LeanCloudRuntime.Application
open Lean LeanCloud LeanEff LeanCloudCli

/-- Runtime services used by the application protocol. User code stays in the registry. -/
inductive Service : Type → Type where
  | submit (config : Config) (run entry : String) (input : Json) : Service Unit
  | scheduler (config : Config) (run : String) : Service Unit
  | worker (config : Config) (run : String) : Service Unit
  | definition (config : Config) (run : String) : Service RunDefinition
  | outcome (config : Config) (run : String) : Service (Option Exit)
  | cancel (config : Config) (run : String) : Service Exit
  | status (config : Config) (run : String) : Service Scheduler.State
  | readText (config : Config) (ref : BlobRef) : Service String

inductive Runtime : Effect where
  | request (service : Service α) : Runtime (Except String α)

abbrev App := ExceptT String (Eff [Host, Runtime])

private def host (op : HostOp α) : App α := ExceptT.mk (send (Host.request op))
private def service (op : Service α) : App α := ExceptT.mk (send (Runtime.request op))
private def say (text : String) : App Unit := host (.write (text ++ "\n"))

/-- One protocol for every compiled application, independent of the actual services. -/
def run (registry : Registry) (args : List String) : App UInt32 := do
  try
    liftExcept registry.validate
    match args with
    | ["programs"] =>
      say (toJson (registry.programs.map (·.info))).compress
      pure 0
    | ["validate", entry] =>
      let program ← liftExcept (registry.find entry)
      let input ← liftExcept (Json.parse (← host .readLine))
      liftExcept (program.validate input)
      pure 0
    | command :: path :: id :: rest =>
      unless LeanCloudCli.validId id do throw "Invalid run ID"
      let config : Config ← liftExcept (Json.parse (← host (.readFile path)) >>= fromJson?)
      liftExcept config.mailboxes.validate
      unless config.scheduler.assignmentMs > 0 do throw "Assignment timeout must be positive"
      match command, rest with
      | "submit-entry", [entry, file] =>
        let input ← liftExcept (Json.parse (← host (.readFile file)))
        let program ← liftExcept (registry.find entry)
        liftExcept (program.validate input)
        service (.submit config id entry input)
        say s!"submitted {id}"
        pure 0
      | "submit", files =>
        let some program := registry.programs[0]? | throw "Application has no programs"
        let input ← match files with
          | [] => match program.info.sampleInput with
            | some input => pure input
            | none => throw "This program needs an input file"
          | [file] => liftExcept (Json.parse (← host (.readFile file)))
          | _ => throw "Expected at most one input file"
        liftExcept (program.validate input)
        service (.submit config id program.info.entry input)
        say s!"submitted {id}"
        pure 0
      | "scheduler", [] => service (.scheduler config id); pure 0
      | "worker", [] =>
        service (.worker config id)
        say s!"completed {id}"
        pure 0
      | "status", [] => say (toJson (← service (.status config id))).compress; pure 0
      | "outcome", [] => say (toJson (← service (.outcome config id))).compress; pure 0
      | "cancel", [] => say (toJson (← service (.cancel config id))).compress; pure 0
      | "result", [] =>
        match ← service (.outcome config id) with
        | none => say "pending"; pure 2
        | some (.failure error) => throw error.message
        | some (.cancelled reason) => throw reason
        | some (.success value) =>
          let definition ← service (.definition config id)
          if definition.resultSchema == (inferInstance : Codec BlobRef).schema then
            let ref ← liftExcept (Codec.decode (α := BlobRef) value)
            host (.write (← service (.readText config ref)))
          else say value.pretty
          pure 0
      | _, _ => throw "Unknown application command or invalid arguments"
    | _ =>
      say "Usage: APP programs | validate ENTRY | (submit-entry|worker|scheduler|status|outcome|result|cancel) CONFIG RUN [ARGS]"
      pure 2
  catch error => host (.write (error ++ "\n") true); pure 1

partial def runWith [Monad m]
    (handleHost : {α : Type} → HostOp α → m (Except String α))
    (handleService : {α : Type} → Service α → m (Except String α))
    (program : App α) : m (Except String α) := do
  match program.run with
  | .pure value => pure value
  | .impure (.here (.request operation)) next =>
    let value ← handleHost operation
    runWith handleHost handleService (ExceptT.mk (ArrsF.apply next value))
  | .impure (.there (.here (.request operation))) next =>
    let value ← handleService operation
    runWith handleHost handleService (ExceptT.mk (ArrsF.apply next value))
  | .impure (.there (.there rest)) _ => nomatch rest

private def handle (registry : Registry) (prepare : Config → String → Json → IO Unit) : Service α → IO α
  | .submit config id entry input => do
    S3.initializeBucket config.blobs
    prepare config entry input
    registry.submit config id entry input
  | .scheduler config id => runScheduler config id
  | .worker config id => registry.runWorker config id
  | .definition config id => loadRun config id
  | .outcome config id => completed config id
  | .cancel config id => LeanCloudRuntime.cancel config id
  | .status config id => LeanCloudRuntime.status config id
  | .readText config ref => do
    let bytes ← match ← (S3.readBytes config.blobs ref).run with
      | .ok bytes => pure bytes
      | .error error => throw (IO.userError error.message)
    let some text := String.fromUTF8? bytes | throw (IO.userError "Result blob is not UTF-8 text")
    pure text

/-- Users only supply their registry and delegate their executable's entry point. -/
def main (registry : Registry) (args : List String)
    (prepare : Config → String → Json → IO Unit := fun _ _ _ => pure ()) : IO UInt32 :=
  withHostIO fun handleHost => do
    let result ← runWith handleHost (fun op => do
      try return .ok (← handle registry prepare op)
      catch error => return .error error.toString) (run registry args)
    return result.toOption.getD 1

end LeanCloudRuntime.Application
