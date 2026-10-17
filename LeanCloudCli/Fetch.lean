import LeanCloudCli.Effects

namespace LeanCloudCli.Fetch
open LeanEff

private partial def wait (id : HttpId) (tick : σ → Cli (Option σ))
    (state : σ) : Cli (Option (Except String String × σ)) := do
  if let some result ← request (.httpPoll id) then return some (result, state)
  let some state ← tick state | return none
  wait id tick state

private def perform (tick : σ → Cli (Option σ)) (state : σ) :
    HostOp α → Cli (Option (Except String α × σ))
  | .httpPost url token body => do
    match ← observing (request (.httpStart url token body)) with
    | .error error => return some (.error error, state)
    | .ok id => try wait id tick state finally request (.httpCancel id)
  | operation => do return some (← observing (request operation), state)

/-- Interpret a read-only refresh while servicing the terminal between HTTP
polls. Both refresh and keyboard logic remain Eff programs. Returning `none`
from `tick` abandons the refresh and cancels its outstanding request. -/
partial def run (program : Cli α) (tick : σ → Cli (Option σ))
    (state : σ) : Cli (Option (α × σ)) := do
  match program.run with
  | EffF.pure _ result => return some (← liftExcept result, state)
  | EffF.impure _ (.here (.request operation)) next =>
    let some (result, state) ← perform tick state operation | return none
    run (ExceptT.mk (ArrsF.apply next result)) tick state
  | EffF.impure _ (.there rest) _ => nomatch rest

end LeanCloudCli.Fetch
