import LeanCloudRuntime.HttpMailbox
import LeanCloudRuntime.LocalDb

/-! Temporary HTTP/SQLite inboxes for adapter tests. They are hosted by the test
process, so applications need no standalone-mailbox deployment mode. -/
namespace TestServices
open LeanCloudRuntime

/-- Component fixture for the single-run mailbox model. The deployed pool owns
its own catalog; this fixture gives the model the same persistence boundary. -/
def schedulerStore (conn : LeanLinq.Sqlite.Conn) (run : String) : IO (LeanCloud.SchedulerStore IO) := do
  let catalog ← LocalDb.loadValue (α := LeanCloud.Scheduler.Catalog) conn run {}
  let state ← IO.mkRef catalog.restore
  return { load := state.get, save := fun next => do
    LocalDb.saveValue conn run next.catalog
    state.set next }

private def withMailbox (body : HttpMailbox.Config → IO α) : IO α :=
    IO.FS.withTempFile fun _ path => do
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let handler : HttpMailbox.ServerHandler := ⟨← Inbox.create conn, "adapter-test", fun _ => pure Lean.Json.null⟩
    let server ← (HttpServer.start (.v4 ⟨.ofParts 127 0 0 1, 0⟩) handler).block
    try
      let some (.v4 address) := server.localAddr | throw (IO.userError "Missing test inbox address")
      body ⟨"127.0.0.1", address.port.toNat, "adapter-test"⟩
    finally server.shutdownAndWait.block
  finally conn.close

def withMailboxes (count : Nat) (body : Array HttpMailbox.Config → IO α) : IO α :=
  match count with
  | 0 => body #[]
  | count + 1 => withMailbox fun endpoint =>
      withMailboxes count fun rest => body (#[endpoint] ++ rest)

end TestServices
