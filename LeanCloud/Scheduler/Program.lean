import LeanCloud.Coordination
import LeanEff.Core

namespace LeanCloud.Scheduler
open LeanEff

/-- Volatile handles correlate replies with dispatched branches. -/
abbrev Ticket := Nat

inductive Scheduling : Effect where
  | spawn (branchStart : Location) : Scheduling Ticket
  | await (ticket : Ticket) : Scheduling (Except CloudError Progress)

abbrev Program := ExceptT CloudError (EffF Scheduling Empty)

/-- The recursive coordinator, independent of inboxes, IO, and storage.
Spawn the entire batch, await its replies in assignment order, finish each
fork's children, then resume that parent. Only workers access replay records. -/
partial def run (branches : List Location) : Program Unit := do
  let tickets ← branches.mapM fun branch => liftM (EffF.send (μ := Empty) (Scheduling.spawn branch))
  let reports ← tickets.mapM fun ticket => liftM (EffF.send (μ := Empty) (Scheduling.await ticket))
  for (branch, report) in branches.zip reports do
    match ← liftExcept report with
    | .done => pure ()
    | .fork location count =>
        run ((List.range count).map location.child)
        run [branch]

/-- The inbox loop keeps only the current request and its in-memory callback.
The closed request family lets this adapter live in ordinary runtime state. -/
inductive Waiting where
  | done (result : Except CloudError Unit)
  | spawn (branch : Location) (next : Ticket → Waiting)
  | await (ticket : Ticket) (next : Except CloudError Progress → Waiting)
  deriving Nonempty

partial def suspend (program : EffF Scheduling Empty (Except CloudError Unit)) : Waiting :=
  match program with
  | .pure _ result => .done result
  | .impure _ (.spawn branch) next => .spawn branch (fun ticket => suspend (next.apply ticket))
  | .impure _ (.await ticket) next => .await ticket (fun reply => suspend (next.apply reply))

end LeanCloud.Scheduler
