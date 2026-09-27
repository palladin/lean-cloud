import LeanCloud.Proofs.ReplayRoute

/-! Build replay routes as execution advances through effects and descends into
parallel branches. Routes depend on journal records, not external state. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

namespace ReplayRoute

variable {World : Type} {journal : Journal}
    {program remaining : Cloud (StateM World) Json} {current target : Location} {steps : Nat}

/-- Extend the active prefix while keeping every ancestor on the same branch. -/
theorem extend {next : Cloud (StateM World) Json} {nextLocation : Location}
    {extra : Nat}
    (route : ReplayRoute journal program current remaining target steps)
    (extension : ReplayPrefix journal remaining target next nextLocation extra) :
    ReplayRoute journal program current next nextLocation (steps + extra) := by
  induction route with
  | leaf nonempty segment => exact .leaf nonempty (segment.trans extension)
  | child nonempty segment recorded size enters selected _ ih =>
    have stillEnters := extension.keeps_ancestor enters
    have stillSelected := (extension.branch_at _ (Location.entersChild_size enters)).trans selected
    have extended := ReplayRoute.child nonempty segment recorded size stillEnters stillSelected (ih extension)
    simpa only [Nat.add_assoc] using extended

/-- Writing a previously empty frontier preserves its reconstruction route. -/
theorem record_frontier
    (route : ReplayRoute journal program current remaining target steps)
    (value : Json) (missing : journal target.key = none) :
    ReplayRoute (journal.write target.key value) program current remaining target steps := by
  have depth := route.depth_le
  have nonempty := route.nonempty
  exact route.preserve (journal.preservesCompleted_write_missing target.key value missing)
    (journal.write_preserves_shallower target target value (by omega) (by omega))

theorem advance_delay {continuation : ArrsF (Control (StateM World)) Unit Json}
    (route : ReplayRoute journal program current (.impure .delay continuation) target steps) :
    ReplayRoute journal program current (ArrsF.apply continuation ()) target (steps + 1) := by
  exact route.extend (.delay .here)

/-- Record a successful primitive result and extend its replay route. -/
theorem advance_sequential {α : Type} {codec : Codec α} {operation : Operation (StateM World) α}
    {continuation : ArrsF (Control (StateM World)) α Json}
    (route : ReplayRoute journal program current
      (.impure (.sequential codec operation) continuation) target steps)
    (law : CodecLaw codec) (value : α)
    (missing : journal target.key = none) :
    ReplayRoute
      (journal.write target.key (toJson (Result.completed (.success (codec.encode value)))))
      program current (ArrsF.apply continuation value) target.next (steps + 1) := by
  have preserved := route.record_frontier (toJson (Result.completed (.success (codec.encode value)))) missing
  apply preserved.extend
  exact .sequential law (journal.read_write _ _) .here

/-- A completed group supplies the recorded values to its continuation. -/
theorem advance_parallel {α : Type} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud (StateM World) α}
    {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    (route : ReplayRoute journal program current
      (.impure (.parallel codec count branches) continuation) target steps)
    (law : CodecLaw codec) (values : Array α)
    (recorded : journal target.key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
    ReplayRoute journal program current (ArrsF.apply continuation values)
      target.next (steps + 1) := by
  exact route.extend (.parallel law recorded .here)

/-- Select the original child program within its enclosing replay route. -/
theorem enter_child {α : Type} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud (StateM World) α}
    {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    (route : ReplayRoute journal program current
      (.impure (.parallel codec count branches) continuation) target steps)
    (children : Array (Option Exit)) (recorded : journal target.key = some (toJson (Result.suspended children)))
    (size : children.size = count) (index : Fin count) :
    ReplayRoute journal program current (codec.encode <$> branches index)
      (target.child index.val) (steps + 1) := by
  generalize endpointEq : (EffF.impure (Control.parallel codec count branches) continuation) = endpoint at route
  induction route with
  | leaf nonempty segment =>
    cases endpointEq
    simpa only [Nat.add_zero] using
      (ReplayRoute.child nonempty segment recorded size (Location.enters_child _ index.val)
        (by simp [Location.child])
        (.leaf (Location.child_nonempty _ index.val) .here))
  | child nonempty segment ancestorRecorded ancestorSize enters selected _ ih =>
    have descended := ih recorded endpointEq
    have selected' := (Location.child_branch _ _ index.val (Location.entersChild_size enters)).trans selected
    simpa only [Nat.add_assoc] using
      (ReplayRoute.child nonempty segment ancestorRecorded ancestorSize
        (Location.entersChild_child enters index.val) selected' descended)

end ReplayRoute
end LeanCloud.Proofs
