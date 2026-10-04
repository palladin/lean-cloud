import Std.Http
import Std.Async.Signal

namespace LeanCloudRuntime.HttpServer
open Std Std.Http Std.Async

-- Poll the signal task itself. Std 4.34's Signal.Waiter.selector polls an outer
-- task that merely installs the waiter, which can spuriously report a signal.
private def signalSelector (signal : Signal.Waiter) : Selector Unit where
  tryFn := do
    let task ← signal.wait
    if ← IO.hasFinished task then
      discard task.block
      return some ()
    return none
  registerFn waiter := do
    let task ← signal.wait
    discard <| AsyncTask.mapIO (x := task) fun _ =>
      waiter.race (pure ()) (fun promise => promise.resolve (.ok ()))
  unregisterFn := pure ()

/-- PID 1 must explicitly accept termination signals. Stop the entire node;
committed inbox rows and coordination state recover on its next start. -/
def stopOnSignal (server : Server) : Async Unit := do
  let terminate ← Signal.Waiter.mk .sigterm false
  let interrupt ← Signal.Waiter.mk .sigint false
  background do
    try
      Selectable.one #[
        .case (signalSelector terminate) (fun _ => IO.Process.exit 143),
        .case (signalSelector interrupt) (fun _ => IO.Process.exit 130),
        .case server.context.doneSelector (fun _ => pure ())]
    finally
      terminate.stop
      interrupt.stop

/-- Use Std's HTTP connection implementation with an Async accept loop.
Lean 4.34's ContextAsync accept loop retains a task chain (upstream #14918).
The Async loop uses the standard library's trampolined iteration instead.
Connections have an absolute lifetime bound, including clients that send no bytes. -/
def start [Server.Handler σ] (address : Net.SocketAddress) (handler : σ) : Async Server := do
  let listener ← TCP.Socket.Server.mk
  listener.bind address
  listener.listen 256
  let config : Http.Config := { enableKeepAlive := false, maxConnections := 256 }
  let server ← Server.new config (some (← listener.getSockName))
  server.activeConnections.atomically (set 1)
  let finished : IO Unit := server.activeConnections.atomically do
    modify (· - 1)
    if (← get) == 0 then discard <| server.shutdownPromise.send ()
  background do
    try
      repeat
        let next ← Selectable.one #[
          .case listener.acceptSelector (fun client => pure (some client)),
          .case server.context.doneSelector (fun _ => pure none)]
        let some client := next | break
        if (← server.activeConnections.atomically get) > config.maxConnections then
          Transport.close client
          continue
        server.activeConnections.atomically (modify (· + 1))
        let context ← server.context.fork
        background do
          let timeout ← Selector.sleep 60000
          Selectable.one #[
            .case timeout (fun _ => context.cancel .shutdown),
            .case context.doneSelector (fun _ => pure ())]
        background do
          try ContextAsync.runIn context (Server.serveConnection client handler config)
          catch error => Server.Handler.onFailure handler error
          finally
            context.cancel .shutdown
            finished
    finally
      server.context.cancel .shutdown
      finished
  return server

end LeanCloudRuntime.HttpServer
