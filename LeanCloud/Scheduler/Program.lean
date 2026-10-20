import LeanCloud.Coordination
import LeanEff.Core

namespace LeanCloud.Scheduler
open LeanEff

/-- Dispatch every branch and start its callback as soon as its reply arrives.
The effect completes once all callbacks, including their nested work, finish. -/
inductive Scheduling : Effect where
  | forEach (branches : Array Location)
      (body : Location → Progress → EffF Scheduling Empty Unit) : Scheduling Unit

abbrev Program := EffF Scheduling Empty

/-- Each callback progresses independently; the continuation after `forEach`
runs exactly once after the entire group completes. -/
def forEach (branches : Array Location) (body : Location → Progress → Program Unit) : Program Unit :=
  EffF.send (Scheduling.forEach branches body)

/-- The recursive coordinator, independent of inboxes, IO, and storage.
Each subtree advances on its own replies and resumes its parent after its
children finish. Only workers access replay records. -/
partial def run (branches : Array Location) : Program Unit :=
  forEach branches fun branch progress => do
    match progress with
    | .done => pure ()
    | .fork location count =>
        run ((Array.range count).map location.child)
        run #[branch]

/-- A scheduling request with separate branch and group continuations.
This closed request family lets the handler keep callbacks in runtime state. -/
inductive Waiting where
  | done
  | forEach (branches : Array Location) (body : Location → Progress → Waiting)
      (next : Unit → Waiting)
  deriving Inhabited

partial def suspend (program : Program Unit) : Waiting :=
  match program with
  | .pure _ () => .done
  | .impure _ (.forEach branches body) next =>
      .forEach branches (fun branch progress => suspend (body branch progress))
        (fun _ => suspend (next.apply ()))

end LeanCloud.Scheduler
