import LeanCloud.Proofs.SimulationBackendSafety
import LeanCloud.Proofs.RecordPreservation
import LeanCloud.Proofs.ReplayEvolution

/-! Semantic contracts for the actual simulated replay store. The expected
journal is a pure specification, never a prefilled runtime store. Replies retain
their meaning while other workers create compatible immutable records. -/

namespace LeanCloud.Proofs.ReplayContracts
open Lean LeanEff SimulationBackend ReplayModel SimulationLogic

/-- Replay storage and observation operations leave coordination to the actors.
This describes their actual mutations, rather than restricting Cloud syntax or
assuming that arbitrary user IO preserves scheduler state. -/
structure PreservesCoordination (before after : World) : Prop where
  scheduler : after.scheduler = before.scheduler
  network : after.network = before.network
  schedulerInbox : after.schedulerInbox = before.schedulerInbox
  workerInboxes : after.workerInboxes = before.workerInboxes

def rules (expected : Journal) : Rules World where
  invariant world := Extends world.records expected
  interference before after := Extends before.records after.records
  orphanInterference before after := Extends before.records after.records
  guarantee _ before after := Extends before.records after.records ∧ PreservesCoordination before after

/-- Keep any fact preserved by immutable record growth alongside a program's
own result. This uses the checked contracts of all its operations. -/
theorem preserving (expected : Journal) {program : SimM World α}
    {pre : World → Prop} {post : α → World → Prop}
    (valid : (rules expected).Program (fun _ => True) post program)
    (stable : (rules expected).Stable (rules expected).interference pre) :
    (rules expected).Program pre (fun value world => post value world ∧ pre world) program :=
  ((Rules.Program.frame (rules expected) program valid
    ⟨stable, stable, fun _ before after first last grows holds => stable before after first last grows.1 holds⟩).weaken
    (rules expected) (fun _ _ holds => ⟨trivial, holds⟩))

/-- A read of `some value` remains valid. A read of `none` says nothing about
later absence: another worker may create the key before this reply arrives. -/
def ReadReply (key : String) (result : Option ReplayRecord) (world : World) : Prop :=
  ∀ record, result = some record → world.records.lookup key = some record

def Created (key : String) (proposed accepted : ReplayRecord) (world : World) : Prop :=
  accepted = proposed ∧ world.records.lookup key = some proposed

theorem read_stable (expected : Journal) (key : String) (result : Option ReplayRecord) :
    (rules expected).Stable (rules expected).interference (ReadReply key result) := by
  intro before after _ _ grows holds record returned
  exact grows key record (holds record returned)

theorem created_stable (expected : Journal) (key : String) (proposed accepted : ReplayRecord) :
    (rules expected).Stable (rules expected).interference (Created key proposed accepted) := by
  intro before after _ _ grows holds
  exact ⟨holds.1, grows key proposed holds.2⟩

/-- Record-preserving bookkeeping may run between an operation and its caller
without invalidating the reply assertion. -/
theorem unchanged (expected : Journal) (remote : Bool) (label : String) (operation : World → α × World)
    {pre : World → Prop} (stable : (rules expected).Stable (rules expected).interference pre)
    (same : ∀ world, (operation world).2.records = world.records)
    (coordination : ∀ world, PreservesCoordination world (operation world).2) :
    (rules expected).Program pre (fun _ => pre) (EffF.send (.step remote label operation)) := by
  apply Rules.send
  refine ⟨stable, fun _ => stable, fun _ => stable, ?_⟩
  intro world invariant holds
  have remains : (rules expected).invariant (operation world).2 := by
    change Extends (operation world).2.records expected
    rw [same]
    exact invariant
  have grows : (rules expected).interference world (operation world).2 := by
    change Extends world.records (operation world).2.records
    rw [same]
    exact Extends.refl _
  exact ⟨remains, ⟨grows, coordination world⟩, stable _ _ invariant remains grows holds⟩

theorem read (expected : Journal) (key : String) :
    (rules expected).Program (fun _ => True) (ReadReply key) (records.read key) := by
  apply Rules.send
  refine ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial, read_stable expected key, ?_⟩
  intro world invariant _
  exact ⟨invariant, ⟨Extends.refl _, ⟨rfl, rfl, rfl, rfl⟩⟩, fun _ returned => returned⟩

/-- Read an established value while retaining the caller's stable facts about
other records. A join uses this to keep all its children available. -/
theorem read_preserving (expected : Journal) (key : String) (record : ReplayRecord)
    (pre : World → Prop) (stable : (rules expected).Stable (rules expected).interference pre)
    (present : ∀ world, (rules expected).invariant world → pre world → world.records.lookup key = some record) :
    (rules expected).Program pre (fun result world => result = some record ∧ pre world)
      (records.read key) := by
  apply Rules.send
  refine ⟨stable, fun _ => stable, ?_, ?_⟩
  · intro value before after first last grows holds
    exact ⟨holds.1, stable before after first last grows holds.2⟩
  · intro world invariant holds
    exact ⟨invariant, ⟨Extends.refl _, ⟨rfl, rfl, rfl, rfl⟩⟩, present world invariant holds,
      stable _ _ invariant invariant (Extends.refl _) holds⟩

/-- A previously established record cannot disappear between issuing a read,
committing it, and delivering the reply. -/
theorem read_known (expected : Journal) (key : String) (record : ReplayRecord) :
    (rules expected).Program (fun world => world.records.lookup key = some record)
      (fun result world => result = some record ∧ world.records.lookup key = some record)
      (records.read key) :=
  read_preserving expected key record _ (fun _ _ _ _ grows present => grows key record present)
    (fun _ _ present => present)

/-- Retain a committed record while a certified computation continues. Fork
paths use this fact to reconstruct earlier effects after later suspension. -/
theorem preserve_record (expected : Journal) (key : String) (record : ReplayRecord)
    {pre : World → Prop} {post : α → World → Prop} {program : SimM World α}
    (valid : (rules expected).Program pre post program) :
    (rules expected).Program (fun world => pre world ∧ world.records.lookup key = some record)
      (fun value world => post value world ∧ world.records.lookup key = some record) program :=
  valid.frame _ program ⟨(fun _ _ _ _ grows present => grows key record present),
    (fun _ _ _ _ grows present => grows key record present),
    (fun _ _ _ _ _ grows present => grows.1 key record present)⟩

/-- Correct proposals are accepted unchanged, even when a competing attempt
has already filled the key. The shared invariant establishes their agreement. -/
theorem create (expected : Journal) (key : String) (proposed : ReplayRecord)
    (known : expected.lookup key = some proposed) :
    (rules expected).Program (fun _ => True) (Created key proposed) (records.create key proposed) := by
  apply Rules.send
  refine ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial, created_stable expected key proposed, ?_⟩
  intro world invariant _
  have accepted := simulated_create_within world expected key proposed invariant known
  have coordination : PreservesCoordination world (SimulationBackend.create key proposed world).2 := by
    unfold SimulationBackend.create
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨accepted.2, ⟨simulated_create_extends world key proposed, coordination⟩, accepted.1, ?_⟩
  have visible := create_is_visible world key proposed
  change (SimulationBackend.create key proposed world).2.records.lookup key =
    some (SimulationBackend.create key proposed world).1 at visible
  simpa only [accepted.1] using! visible

/-- The worker's observation wrapper records only a hint. It retains the same
semantic read contract as the underlying global store. -/
theorem observed_read (expected : Journal) (worker : WorkerId) (key : String) :
    (rules expected).Program (fun _ => True) (ReadReply key) ((observed worker).records.read key) := by
  apply Rules.bind _ (read expected key)
  intro result
  split
  · apply Rules.bind _ (unchanged expected _ _ _ (read_stable expected key result) (fun _ => rfl)
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩))
    intro _
    exact fun _ _ holds => holds
  · exact fun _ _ holds => holds

theorem observed_read_preserving (expected : Journal) (worker : WorkerId) (key : String) (record : ReplayRecord)
    (pre : World → Prop) (stable : (rules expected).Stable (rules expected).interference pre)
    (present : ∀ world, (rules expected).invariant world → pre world → world.records.lookup key = some record) :
    (rules expected).Program pre (fun result world => result = some record ∧ pre world)
      ((observed worker).records.read key) := by
  apply Rules.bind _ (read_preserving expected key record pre stable present)
  intro result
  split
  · apply Rules.bind _ (unchanged expected _ _ _ (pre := fun world => result = some record ∧ pre world)
      (fun before after first last grows holds => ⟨holds.1, stable before after first last grows holds.2⟩)
      (fun _ => rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩))
    intro _
    exact fun _ _ holds => holds
  · exact fun _ _ holds => holds

theorem outcome_preserving (expected : Journal) (worker : WorkerId) (branch : Location) (outcome : Exit)
    (pre : World → Prop) (stable : (rules expected).Stable (rules expected).interference pre)
    (present : ∀ world, (rules expected).invariant world → pre world →
      world.records.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    (rules expected).Returns pre ((observed worker).records.outcome branch) (some outcome) := by
  apply Rules.except_bind (middle := fun value world => value = some ⟨ReplayStore.returnRequest, outcome⟩ ∧ pre world)
  · apply Rules.except_lift _ (observed_read_preserving expected worker _ _ pre stable present)
    exact fun _ _ _ holds => holds
  · intro value
    cases value with
    | none =>
      intro world invariant holds
      cases holds.1
    | some record =>
      dsimp only
      split
      · intro world invariant holds
        have same := Option.some.inj holds.1
        exact ⟨by rw [same], holds.2⟩
      · intro world invariant holds
        have same : record.request = ReplayStore.returnRequest := congrArg ReplayRecord.request (Option.some.inj holds.1)
        simp_all

/-- A branch-return probe may find nothing. If it finds a return, that value
agrees with the specification and remains durably present for the caller. -/
def OutcomeReply (branch : Location) (expected : Exit) : Option Exit → World → Prop
  | none, _ => True
  | some actual, world => actual = expected ∧
      world.records.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, expected⟩

theorem outcome (expected : Journal) (worker : WorkerId) (branch : Location) (value : Exit)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, value⟩) :
    (rules expected).Program (fun _ => True)
      (fun result world => match result with
        | .error _ => False
        | .ok reply => OutcomeReply branch value reply world)
      ((observed worker).records.outcome branch).run := by
  apply Rules.except_bind (middle := ReadReply (ReplayStore.returnKey branch))
  · apply Rules.except_lift _ (observed_read expected worker _)
    exact fun _ _ _ holds => holds
  · intro reply
    cases reply with
    | none => exact fun _ _ _ => trivial
    | some record =>
      dsimp only
      split
      · intro world invariant holds
        have found := holds record rfl
        have same := Option.some.inj ((invariant _ _ found).symm.trans known)
        exact ⟨congrArg ReplayRecord.outcome same, found.trans (congrArg some same)⟩
      · intro world invariant holds
        have same := congrArg ReplayRecord.request (Option.some.inj ((invariant _ _ (holds record rfl)).symm.trans known))
        simp_all

theorem observed_create (expected : Journal) (worker : WorkerId) (key : String) (proposed : ReplayRecord)
    (known : expected.lookup key = some proposed) :
    (rules expected).Program (fun _ => True) (Created key proposed) ((observed worker).records.create key proposed) := by
  apply Rules.bind _ (create expected key proposed known)
  intro accepted
  apply Rules.bind _ (unchanged expected _ _ _ (created_stable expected key proposed accepted) (fun _ => rfl)
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩))
  intro _
  exact fun _ _ holds => holds

/-- Checking an existing record uses agreement with the pure specification.
The reply's presence assertion remains valid even after a delayed read. -/
theorem check_existing (expected : Journal) (key : String) (proposed actual : ReplayRecord)
    (known : expected.lookup key = some proposed) (pre : World → Prop)
    (present : ∀ world, (rules expected).invariant world → pre world → world.records.lookup key = some actual) :
    (rules expected).Program pre
      (fun result world => result = Except.ok proposed.outcome ∧ pre world ∧ world.records.lookup key = some proposed)
      (ReplayInterpreter.Internal.check proposed.request actual).run := by
  unfold ReplayInterpreter.Internal.check
  split
  · intro world invariant holds
    have found := present world invariant holds
    have same := Option.some.inj ((invariant _ _ found).symm.trans known)
    exact ⟨by rw [same], holds, found.trans (congrArg some same)⟩
  · intro world invariant holds
    have found := present world invariant holds
    have same := congrArg ReplayRecord.request (Option.some.inj ((invariant _ _ found).symm.trans known))
    simp_all

/-- Creating and checking a specified record establishes a durable result while
retaining the caller's stable facts. Retries return the same canonical value. -/
theorem create_checked (expected : Journal) (worker : WorkerId) (key : String) (proposed : ReplayRecord)
    (known : expected.lookup key = some proposed) (pre : World → Prop)
    (stable : (rules expected).Stable (rules expected).interference pre) :
    (rules expected).Program pre
      (fun result world => result = Except.ok proposed.outcome ∧ pre world ∧ world.records.lookup key = some proposed)
      ((do
        let accepted ← (observed worker).records.create key proposed
        ReplayInterpreter.Internal.check proposed.request accepted : ExceptT CloudError (SimM World) Exit).run) := by
  apply Rules.except_bind (middle := fun accepted world => Created key proposed accepted world ∧ pre world)
  · apply Rules.except_lift _ (preserving expected (observed_create expected worker key proposed known) stable)
    exact fun _ _ _ holds => holds
  · intro accepted
    unfold ReplayInterpreter.Internal.check
    split
    · intro world invariant holds
      exact ⟨by rw [holds.1.1], holds.2, holds.1.2⟩
    · intro world invariant holds
      have same := congrArg ReplayRecord.request holds.1.1
      simp_all

/-- The existing completion helper reports done only after its specified
return record is durable. Each intermediate reply may be delayed. -/
theorem finish (expected : Journal) (worker : WorkerId) (branch : Location) (outcome : Exit)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    (rules expected).Program (fun _ => True)
      (fun result world => result = Except.ok Progress.done ∧
        world.records.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩)
      (ReplayInterpreter.Internal.finish (observed worker).records branch outcome).run := by
  apply Rules.except_bind (middle := fun (_ : Unit) world =>
    world.records.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩)
  · apply Rules.except_bind (middle := Created (ReplayStore.returnKey branch) ⟨ReplayStore.returnRequest, outcome⟩)
    · apply Rules.except_lift _ (observed_create expected worker _ _ known)
      exact fun _ _ _ holds => holds
    · intro accepted
      split
      · intro world invariant holds
        exact holds.2
      · intro world invariant holds
        have same : accepted.request = ReplayStore.returnRequest := congrArg ReplayRecord.request holds.1
        simp_all
  · intro _
    exact fun _ _ present => ⟨rfl, present⟩

/-- Correct immutable record operations all obey the same interference law.
The simulator soundness theorem can therefore compose different workers. -/
def system (expected : Journal) (count : Nat) : SimulationSafety.System World count where
  invariant := (rules expected).invariant
  evolution := (rules expected).interference
  rely _ := (rules expected).interference
  guarantee _ := (rules expected).guarantee
  reflexive world := Extends.refl world.records
  transitive := fun {_ _ _} first second => first.trans second
  compatible _ _ _ _ _ _ grows := ⟨grows.1, fun _ _ => grows.1⟩

private theorem unchanged_world (expected : Journal)
    {post : Fin count → α → World → Prop} {state : Simulation.State World α count} {world : World}
    (valid : (system expected count).Valid post state)
    (postStable : ∀ actor value, (rules expected).Stable (rules expected).interference (post actor value))
    (same : world.records = state.world.records) :
    (system expected count).Valid post { state with world } ∧
      (system expected count).evolution state.world world := by
  have invariant : (system expected count).invariant world := by
    change Extends world.records expected
    rw [same]
    exact valid.invariant
  have grows : (system expected count).evolution state.world world := by
    change Extends state.world.records world.records
    rw [same]
    exact Extends.refl _
  exact ⟨valid.advance _ postStable invariant grows (fun _ => grows), grows⟩

/-- The backend's broker disconnect hook preserves semantic assertions as well
as immutable records. The underlying event is the actual Simulation.step. -/
theorem step_preserves (expected : Journal) (start : Simulation.Start World α count)
    (post : Fin count → α → World → Prop)
    (postStable : ∀ actor value, (rules expected).Stable (rules expected).interference (post actor value))
    (starts : ∀ actor generation, (rules expected).Program (fun _ => True) (post actor) (start actor generation))
    (state after : Simulation.State World α count) (event : Simulation.Event count)
    (valid : (system expected count).Valid post state)
    (executed : SimulationBackend.step start event state = .ok after) :
    (system expected count).Valid post after :=
  ((system expected count).backend_step_preserves start post postStable starts
    (fun _ _ _ safe => unchanged_world expected safe postStable (ReplayEvolution.disconnect _ _ _))
    state after event valid executed).1

/-- Stable reply assertions follow every actual actor/network interleaving.
Atomic and startup contracts remain the obligations to discharge for each actor;
correctness of a trace is obtained here, not assumed as a premise. -/
theorem trace_preserves (expected : Journal) (start : Simulation.Start World α count)
    (post : Fin count → α → World → Prop)
    (postStable : ∀ actor value, (rules expected).Stable (rules expected).interference (post actor value))
    (starts : ∀ actor generation, (rules expected).Program (fun _ => True) (post actor) (start actor generation))
    {allowed : Simulation.Event count → Prop} {before after : Simulation.State World α count}
    (valid : (system expected count).Valid post before)
    (history : SchedulerOwnership.Trace start allowed before after) :
    (system expected count).Valid post after :=
  ((system expected count).backend_trace_preserves start post postStable starts
    (fun _ _ _ safe => unchanged_world expected safe postStable (ReplayEvolution.disconnect _ _ _))
    (fun _ event safe => unchanged_world expected safe postStable (ReplayEvolution.network event _)) valid history).1

end LeanCloud.Proofs.ReplayContracts
