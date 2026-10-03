import LeanCloud.Proofs.ExecutionContracts
import LeanCloud.Proofs.Resumption

/-! Contracts for reconstructing a nested assignment through the actual replay
interpreter. The recorded prefix survives interleaving, delayed replies, and
orphan writes. Its continuation retains the same semantic execution contract. -/

namespace LeanCloud.Proofs.ResumptionContracts
open Lean LeanEff SimulationBackend ReplayModel ReplayInterpreter SimulationLogic Reconstruction

private theorem read_then (expected : Journal) (worker : WorkerId) (key : String) (record : ReplayRecord)
    (pre : World → Prop) (stable : (ReplayContracts.rules expected).Stable
      (ReplayContracts.rules expected).interference pre)
    (present : ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      world.records.lookup key = some record)
    (next : Option ReplayRecord → ExceptT CloudError (SimM World) α)
    (post : Except CloudError α → World → Prop)
    (continued : (ReplayContracts.rules expected).Program pre post (next (some record)).run) :
    (ReplayContracts.rules expected).Program pre post
      ((do let found ← (observed worker).records.read key; next found : ExceptT CloudError (SimM World) α).run) := by
  apply Rules.except_bind (middle := fun found world => found = some record ∧ pre world)
  · apply Rules.except_lift _ (ReplayContracts.observed_read_preserving expected worker key record pre stable present)
    exact fun _ _ _ holds => holds
  · intro found
    apply Rules.Program.assuming
    intro same
    subst found
    exact continued

/-- Following a recorded prefix reaches the supplied typed continuation, unless
the budget runs out first. All prefix reads retain the caller's stable facts;
unrelated records may be created before a read's continuation resumes. -/
theorem replay (expected journal : Journal) (worker : WorkerId) (assignment : Assignment)
    {α β : Type} {encode : α → Json} {program : Cloud (SimM World) α}
    {current steps} {remainingEncode : β → Json} {remaining : Cloud (SimM World) β}
    (witness : Prefix journal assignment.location encode program current steps remainingEncode remaining)
    (pre : World → Prop) (stable : (ReplayContracts.rules expected).Stable
      (ReplayContracts.rules expected).interference pre)
    (cached : ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      Extends journal world.records)
    (post : Except CloudError Progress → World → Prop)
    (fuel : Nat)
    (exhausted : fuel < steps → ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      post (.error ⟨.protocol, "Interpreter fuel exhausted"⟩) world)
    (continued : ∀ remainingFuel, steps + remainingFuel = fuel → (ReplayContracts.rules expected).Program pre post
      (walk (observed worker).records blobs assignment remainingFuel remainingEncode remaining assignment.location true).run) :
    (ReplayContracts.rules expected).Program pre post
      (walk (observed worker).records blobs assignment fuel encode program current).run := by
  induction witness generalizing fuel with
  | here encode program =>
    rw [walk_at_assignment]
    exact continued fuel (Nat.zero_add fuel)
  | delay next before rest ih =>
    cases fuel with
    | zero => exact exhausted (Nat.zero_lt_succ _)
    | succ fuel =>
      simpa only [walk, Bool.false_or, beq_eq_false_iff_ne.mpr before] using ih fuel (fun smaller => exhausted (by omega)) (fun remainingFuel same => continued remainingFuel (by omega))
  | sequential codec operation next record wire value before present checked success decoded rest ih =>
    cases fuel with
    | zero => exact exhausted (Nat.zero_lt_succ _)
    | succ fuel =>
      simp only [walk, Bool.false_or, beq_eq_false_iff_ne.mpr before]
      apply read_then expected worker _ record pre stable (fun world invariant holds => cached world invariant holds _ _ present)
      simp only [Internal.check, checked, ite_true, success]
      apply Rules.except_bind_value _ _ _ value (ExecutionContracts.decode expected pre codec wire value decoded)
      exact ih fuel (fun smaller => exhausted (by omega)) (fun remainingFuel same => continued remainingFuel (by omega))
  | joined codec count branches next record wire values before skip present checked success decoded size rest ih =>
    cases fuel with
    | zero => exact exhausted (Nat.zero_lt_succ _)
    | succ fuel =>
      simp only [walk, Bool.false_or, beq_eq_false_iff_ne.mpr before, Bool.not_false, Bool.true_and, skip, Bool.false_eq_true, ite_false]
      apply read_then expected worker _ record pre stable (fun world invariant holds => cached world invariant holds _ _ present)
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ite_false,
        Internal.check, checked, ite_true, success]
      apply Rules.except_bind_value _ _ _ values
      · unfold Internal.decodeGroup
        apply Rules.returns_bind (value := values)
        · exact ExecutionContracts.decode expected pre _ wire values decoded
        · simp only [size, beq_self_eq_true]
          exact Rules.returns_pure _ pre values
      · exact ih fuel (fun smaller => exhausted (by omega)) (fun remainingFuel same => continued remainingFuel (by omega))
  | child codec count branches next index before enters selected rest ih =>
    cases fuel with
    | zero => exact exhausted (Nat.zero_lt_succ _)
    | succ fuel =>
      simp only [walk, Bool.false_or, beq_eq_false_iff_ne.mpr before, Bool.not_false, Bool.true_and, enters, ite_true,
        selected, index.isLt, dite_true]
      exact ih fuel (fun smaller => exhausted (by omega)) (fun remainingFuel same => continued remainingFuel (by omega))

/-- Compose a certified active continuation with its actual recorded prefix.
The budget is the prefix length plus the supplied continuation bound. -/
theorem at_prefix [codec : Codec α] (expected journal : Journal) (worker : WorkerId)
    (assignment : Assignment) (program : ι → Cloud (SimM World) α) (input : ι)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud (SimM World) β} {steps}
    (expectedReturn : Exit)
    (returned : expected.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, expectedReturn⟩)
    (witness : Prefix journal assignment.location codec.encode (program input)
      Location.root steps remainingEncode remaining)
    (bound : Nat)
    (active : ∀ fuel, (ReplayContracts.rules expected).Program (ExecutionContracts.Ready expected assignment)
      (fun result world => ExecutionContracts.Result expected assignment.branch expectedReturn remainingEncode remaining assignment.location result world ∧
        ExecutionContracts.FuelBound fuel bound result ∧ ExecutionContracts.ForksAfter assignment assignment.location result)
      (walk (observed worker).records blobs assignment fuel remainingEncode remaining assignment.location true).run) :
    ∀ fuel, (ReplayContracts.rules expected).Program
        (fun world => Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world)
        (fun result world => ExecutionContracts.Result expected assignment.branch expectedReturn codec.encode (program input) Location.root result world ∧
          ExecutionContracts.FuelBound fuel (steps + bound) result ∧
          ExecutionContracts.ForksAfter assignment assignment.location result)
        (step (observed worker).records blobs fuel program input assignment).run := by
  have path : Resumable journal codec.encode (program input) Location.root assignment.location :=
    ⟨β, remainingEncode, remaining, steps, witness⟩
  let pre := fun world : World => Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world
  have stable : (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference pre :=
    fun before after first last grows holds =>
      ⟨holds.1.trans grows, ExecutionContracts.ready_stable expected assignment before after first last grows holds.2⟩
  intro fuel
  apply ExecutionContracts.entry expected worker fuel program input assignment _ returned path.valid_root pre stable _
    (fun _ _ _ present => ⟨⟨present, by intro location count impossible; cases impossible⟩, Or.inl rfl,
      by intro location count impossible; cases impossible⟩)
  apply replay expected journal worker assignment witness pre stable (fun _ _ holds => holds.1) _ fuel
  · exact fun short _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (by omega),
      by intro location count impossible; cases impossible⟩
  · intro remainingFuel accounted
    have frame : (ReplayContracts.rules expected).Frame (fun world => Extends journal world.records) :=
      ⟨(fun _ _ _ _ grows recorded => recorded.trans grows),
        (fun _ _ _ _ grows recorded => recorded.trans grows),
        (fun _ _ _ _ _ grows recorded => recorded.trans grows.1)⟩
    apply Rules.Program.weaken
    · apply Rules.Program.weaken_post _ _ ((active remainingFuel).frame _ _ frame)
      intro result world invariant holds
      exact ⟨⟨holds.1.1.1, fun location count forked =>
        (holds.1.1.2 location count forked).prepend (witness.extend holds.2) (by decide)⟩,
        by simpa only [accounted] using holds.1.2.1.add_prefix steps, holds.1.2.2⟩
    · exact fun _ _ holds => ⟨holds.2, holds.1⟩

/-- A nested assignment retains the meaning of the original source program.
The recorded path determines its continuation, encoder, and branch result; no
separate meaning for that continuation is assumed. Its sufficient fuel includes
both reconstruction and the active continuation. -/
theorem assigned [codec : Codec α] (expected journal : Journal) (worker : WorkerId)
    (assignment : Assignment) (program : ι → Cloud (SimM World) α) (input : ι)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud (SimM World) β} {steps outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (consistent : Extends journal expected)
    (branch : assignment.branch = Location.branchStart assignment.location)
    (witness : Prefix journal assignment.location codec.encode (program input)
      Location.root steps remainingEncode remaining) :
    ∃ expectedReturn,
      expected.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, expectedReturn⟩ ∧
      ∃ bound, ∀ fuel, (ReplayContracts.rules expected).Program
        (fun world => Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world)
        (fun result world => ExecutionContracts.Result expected assignment.branch expectedReturn codec.encode (program input) Location.root result world ∧
          ExecutionContracts.FuelBound fuel bound result ∧ ExecutionContracts.ForksAfter assignment assignment.location result)
        (step (observed worker).records blobs fuel program input assignment).run := by
  obtain ⟨result, resumed, returned⟩ := meaning.resume (by simpa using known) witness consistent
  rw [← branch] at returned
  obtain ⟨bound, active⟩ := ExecutionContracts.active_bounded expected resumed
    (Nat.lt_of_lt_of_le (by decide) (witness.follows (by decide)).depth)
  exact ⟨_, returned, steps + bound, at_prefix expected journal worker assignment program input _ returned witness bound
    (active worker assignment remainingEncode branch returned)⟩

/-- One budget works for this location across all workers, attempts, join modes,
and compatible snapshots. The complete specification chooses a typed path once;
`Prefix.in_snapshot` transfers that exact path to each worker's available cache. -/
theorem location_fuel [codec : Codec α] (expected : Journal) (target : Location)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (available : Resumable expected codec.encode (program input) Location.root target) :
    ∃ bound, ∀ worker assignment,
      assignment.location = target → assignment.branch = Location.branchStart target →
      ∀ journal, Extends journal expected → Resumable journal codec.encode (program input) Location.root target →
      ∀ fuel, bound ≤ fuel → (ReplayContracts.rules expected).Program
        (fun world => Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world)
        (fun result _ => result.isOk = true)
        (step (observed worker).records blobs fuel program input assignment).run := by
  obtain ⟨β, remainingEncode, remaining, steps, witness⟩ := available
  obtain ⟨result, resumed, returned⟩ := meaning.resume (by simpa using known) witness (Extends.refl _)
  obtain ⟨bound, active⟩ := ExecutionContracts.active_bounded expected resumed
    (Nat.lt_of_lt_of_le (by decide) (witness.follows (by decide)).depth)
  refine ⟨steps + bound, ?_⟩
  intro worker assignment same branch journal consistent available fuel enough
  subst target
  have path := witness.in_snapshot consistent available
  rw [← branch] at returned
  have valid := at_prefix expected journal worker assignment program input _ returned path bound
    (active worker assignment remainingEncode branch returned) fuel
  exact valid.weaken_post _ _ (fun _ _ _ holds => holds.2.1.isOk enough)

end LeanCloud.Proofs.ResumptionContracts
