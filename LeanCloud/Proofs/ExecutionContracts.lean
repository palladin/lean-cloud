import LeanCloud.Proofs.ParallelContracts
import LeanCloud.Proofs.Suspension

/-! Semantic contracts for the active portion of the existing replay walk.
The invariant is agreement with a pure specification, while actual storage may
initially be missing any record the current assignment is allowed to create. -/

namespace LeanCloud.Proofs.ExecutionContracts
open Lean LeanEff SimulationBackend ReplayModel ReplayInterpreter SimulationLogic

variable {info : Option SourceSiteId}

def Ready (expected : Journal) (assignment : Assignment) (world : World) : Prop :=
  assignment.joining = true → Recording.JoinReady expected world.records assignment.location

theorem ready_stable (expected : Journal) (assignment : Assignment) :
    (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference (Ready expected assignment) :=
  fun _ _ _ _ grows ready joining => (ready joining).extend grows

/-- Workflow failures are stored branch outcomes. An interpreter error in the
supported pure fragment can only be exhaustion of its execution budget. -/
def Outcome (expected : Journal) (branch : Location) (outcome : Exit) : Except CloudError Progress → World → Prop
  | .error error, _ => error = ⟨.protocol, "Interpreter fuel exhausted"⟩
  | .ok .done, world => world.records.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩
  | .ok (.fork location count), _ => branch = Location.branchStart location ∧ Specification.Group expected location count

theorem outcome_stable (expected : Journal) (branch : Location) (outcome : Exit) (result : Except CloudError Progress) :
    (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference (Outcome expected branch outcome result) := by
  intro before after _ _ grows holds
  cases result with
  | error _ => exact holds
  | ok progress =>
    cases progress with
    | done => exact grows _ _ holds
    | fork _ _ => exact holds

/-- A segment's result includes the paths needed to schedule its next fork.
The paths describe the original typed program and durable records, not values
or continuations added to the report sent over the mailbox. -/
def Result (expected : Journal) (branch : Location) (outcome : Exit)
    (encode : α → Json) (program : Cloud (SimM World) α) (current : Location)
    (result : Except CloudError Progress) (world : World) : Prop :=
  Outcome expected branch outcome result world ∧
    ∀ location count, result = .ok (.fork location count) →
      Suspension.Paths world.records encode program current location count

/-- A failed interpreter step used less fuel than the sufficient bound.
Together with `Result`, this excludes every interpreter error above the bound. -/
def FuelBound (fuel bound : Nat) (result : Except CloudError Progress) : Prop :=
  result.isOk = true ∨ fuel < bound

/-- A segment never moves backwards. An authorized join cannot suspend again
at the fork it was sent to join, even if another worker writes its result while
the segment is running. This is progress of locations, not delivery fairness. -/
def ForksAfter (assignment : Assignment) (current : Location)
    (result : Except CloudError Progress) : Prop :=
  ∀ location count, result = .ok (.fork location count) →
    Routing.Follows current location ∧ (assignment.joining = true → location ≠ assignment.location)

theorem ForksAfter.next {assignment current result}
    (later : ForksAfter assignment current.next result) (nonempty : 0 < current.size) :
    ForksAfter assignment current result := by
  intro location count forked
  obtain ⟨follows, different⟩ := later location count forked
  exact ⟨(Routing.next_follows current nonempty).trans follows, different⟩

theorem FuelBound.succ {fuel bound result} (valid : FuelBound fuel bound result) :
    FuelBound (fuel + 1) (bound + 1) result :=
  valid.elim Or.inl (fun smaller => Or.inr (Nat.succ_lt_succ smaller))

theorem FuelBound.add_prefix {fuel bound result} (valid : FuelBound fuel bound result) (steps : Nat) :
    FuelBound (steps + fuel) (steps + bound) result :=
  valid.elim Or.inl (fun smaller => Or.inr (Nat.add_lt_add_left smaller steps))

theorem FuelBound.isOk {fuel bound result} (valid : FuelBound fuel bound result) (enough : bound ≤ fuel) :
    result.isOk = true := valid.resolve_right (Nat.not_lt_of_ge enough)

theorem result_stable (expected : Journal) (branch : Location) (outcome : Exit)
    (encode : α → Json) (program : Cloud (SimM World) α) (current : Location) (result : Except CloudError Progress) :
    (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference
      (Result expected branch outcome encode program current result) :=
  fun before after first last grows holds =>
    ⟨outcome_stable expected branch outcome result before after first last grows holds.1,
      fun location count forked => (holds.2 location count forked).extend grows⟩

private theorem Result.lift {expected branch outcome current source result world}
    {encode : α → Json} {program : Cloud (SimM World) α}
    {sourceEncode : β → Json} {sourceProgram : Cloud (SimM World) β}
    (valid : Result expected branch outcome encode program current result world)
    (lift : ∀ target, Reconstruction.Resumable world.records encode program current target →
      Reconstruction.Resumable world.records sourceEncode sourceProgram source target) :
    Result expected branch outcome sourceEncode sourceProgram source result world :=
  ⟨valid.1, fun location count forked => (valid.2 location count forked).lift lift⟩

theorem decode (expected : Journal) (pre : World → Prop) (codec : Codec α) (wire : Json) (value : α)
    (decoded : codec.decode wire = .ok value) :
    (ReplayContracts.rules expected).Returns pre (Internal.decode codec wire) value := by
  unfold Internal.decode
  rw [decoded]
  exact Rules.returns_pure _ pre value

theorem decode_group (expected : Journal) (pre : World → Prop) (codec : Codec α) (count : Nat) (values : Array α)
    (roundtrip : Pure.RoundTrips codec) (size : values.size = count) :
    (ReplayContracts.rules expected).Returns pre
      (Internal.decodeGroup codec count (.arr (values.map codec.encode))) values := by
  apply Rules.returns_bind (value := values)
  · exact decode expected pre (@instCodecArray _ codec) _ values (roundtrip.array codec values)
  · simp only [size, beq_self_eq_true]
    exact Rules.returns_pure _ pre values

private theorem checked_then (expected : Journal) (request : Request) (outcome : Exit) (actual : ReplayRecord)
    (next : Exit → ExceptT CloudError (SimM World) α) (pre : World → Prop) (post : Except CloudError α → World → Prop)
    (continued : (ReplayContracts.rules expected).Program pre post (next outcome).run) :
    (ReplayContracts.rules expected).Program (fun world => actual = ⟨request, outcome⟩ ∧ pre world) post
      ((do let value ← Internal.check request actual; next value).run) := by
  apply Rules.Program.assuming
  intro same
  subst actual
  simpa only [Internal.check, beq_self_eq_true, ite_true] using! continued

/-- The command case records its pure result before continuing.
The continuation receives both the value and its durable presence assertion. -/
theorem exec_then (expected : Journal) (worker : WorkerId) (current : Location)
    (codec : Codec α) (label : String) (body : Unit → α) (pre : World → Prop)
    (stable : (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference pre)
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → SimM World α)),
        .success (codec.encode (body ()))⟩)
    (next : Exit → ExceptT CloudError (SimM World) β) (post : Except CloudError β → World → Prop)
    (continued : (ReplayContracts.rules expected).Program
      (fun world => pre world ∧ world.records.lookup (ReplayStore.valueKey current) =
        some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → SimM World α)),
          .success (codec.encode (body ()))⟩)
      post (next (.success (codec.encode (body ())))).run) :
    let operation : Operation (SimM World) α := .exec label (fun _ => pure (body ()))
    let request := Internal.request codec operation
    (ReplayContracts.rules expected).Program pre post
      ((do
        let outcome ← match ← (observed worker).records.read (ReplayStore.valueKey current) with
          | some record => Internal.check request record
          | none => do
            let outcome ← try
              pure (.success (codec.encode (← blobs.execute operation)))
            catch error => pure (.failure error)
            let accepted ← (observed worker).records.create (ReplayStore.valueKey current) ⟨request, outcome⟩
            Internal.check request accepted
        next outcome : ExceptT CloudError (SimM World) β).run) := by
  dsimp only
  apply Rules.except_bind (middle := fun record world => ReplayContracts.ReadReply (ReplayStore.valueKey current) record world ∧ pre world)
  · apply Rules.except_lift _ (ReplayContracts.preserving expected
      (ReplayContracts.observed_read expected worker (ReplayStore.valueKey current)) stable)
    exact fun _ _ _ holds => holds
  · intro record
    cases record with
    | some record =>
      apply Rules.Program.weaken _ (checked_then expected _ _ record _ _ _ continued)
      intro world invariant holds
      have found := holds.1 record rfl
      have same := Option.some.inj ((invariant _ _ found).symm.trans known)
      exact ⟨same, holds.2, found.trans (congrArg some same)⟩
    | none =>
      change (ReplayContracts.rules expected).Program _ post ((do
        let accepted ← (observed worker).records.create (ReplayStore.valueKey current)
          ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → SimM World α)),
            .success (codec.encode (body ()))⟩
        let value ← Internal.check
          (Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → SimM World α))) accepted
        next value : ExceptT CloudError (SimM World) β).run)
      apply Rules.except_bind (middle := fun accepted world =>
        ReplayContracts.Created (ReplayStore.valueKey current)
          ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → SimM World α)),
            .success (codec.encode (body ()))⟩ accepted world ∧ pre world)
      · apply Rules.Program.weaken
        · apply Rules.except_lift _ (ReplayContracts.preserving expected
            (ReplayContracts.observed_create expected worker _ _ known) stable)
          exact fun _ _ _ holds => holds
        · exact fun _ _ holds => holds.2
      · intro accepted
        apply Rules.Program.weaken _ (checked_then expected _ _ accepted _ _ _ continued)
        exact fun _ _ holds => ⟨holds.1.1, holds.2, holds.1.2⟩

private theorem finish (expected : Journal) (worker : WorkerId) (branch : Location) (outcome : Exit)
    (encode : α → Json) (program : Cloud (SimM World) α) (current : Location)
    (pre : World → Prop) (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩)
    {fuel bound : Nat} :
    (ReplayContracts.rules expected).Program pre
      (fun result world => Result expected branch outcome encode program current result world ∧ FuelBound fuel bound result ∧
        ForksAfter assignment current result)
      (Internal.finish (observed worker).records branch outcome).run := by
  apply Rules.Program.weaken
  · apply Rules.Program.weaken_post _ _ (ReplayContracts.finish expected worker branch outcome known)
    intro result world invariant holds
    rw [holds.1]
    exact ⟨⟨holds.2, by intro location count impossible; cases impossible⟩, Or.inl rfl,
      by intro location count impossible; cases impossible⟩
  · exact fun _ _ _ => trivial

/-- The actual parallel case either suspends at this fork or obtains its
specified group result before invoking the supplied continuation contract. -/
private theorem parallel (expected : Journal) (worker : WorkerId) (assignment : Assignment)
    (fuel : Nat) (encode : β → Json) (current : Location) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud (SimM World) α) (next : ArrsF (Control (SimM World)) SourceSiteId (Array α) β)
    (joined : Exit) (post : Except CloudError Progress → World → Prop)
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, joined⟩)
    (group : Specification.Group expected current count)
    (forked : (current != assignment.location || !assignment.joining) = true →
      ∀ world, (ReplayContracts.rules expected).invariant world → Ready expected assignment world →
      post (.ok (.fork current count)) world)
    (continued : (ReplayContracts.rules expected).Program
      (fun world => Ready expected assignment world ∧ world.records.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, joined⟩) post
      ((match (generalizing := false) joined with
        | .success wire => do
          let values ← Internal.decodeGroup codec count wire
          walk (observed worker).records blobs assignment fuel encode (next.apply values) current.next true
        | outcome => Internal.finish (observed worker).records assignment.branch outcome :
          ExceptT CloudError (SimM World) Progress).run)) :
    (ReplayContracts.rules expected).Program (Ready expected assignment) post
      (walk (observed worker).records blobs assignment (fuel + 1) encode
        (.impure info (.parallel codec count branches) next) current true).run := by
  simp only [walk, Bool.true_or, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
  apply Rules.except_bind (middle := fun record world =>
    ReplayContracts.ReadReply (ReplayStore.valueKey current) record world ∧ Ready expected assignment world)
  · apply Rules.except_lift _ (ReplayContracts.preserving expected
      (ReplayContracts.observed_read expected worker _) (ready_stable expected assignment))
    exact fun _ _ _ holds => holds
  · intro record
    cases record with
    | some record =>
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ite_false]
      apply Rules.Program.weaken _ (checked_then expected _ joined record _ _ _ continued)
      intro world invariant holds
      have found := holds.1 record rfl
      have same := Option.some.inj ((invariant _ _ found).symm.trans known)
      exact ⟨same, holds.2, found.trans (congrArg some same)⟩
    | none =>
      simp only [Option.isNone_none, Bool.true_and]
      split
      · rename_i canFork
        exact fun world invariant holds => forked canFork world invariant holds.2
      · rename_i authorized
        have same : current = assignment.location := by simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr authorized)).1
        have joining : assignment.joining = true := by simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr authorized)).2
        obtain ⟨children, returned, collected⟩ :=
          Recording.JoinReady.of_specification group codec.schema count joined known
        have joinedResult := (ParallelContracts.join_ready expected worker current codec.schema count joined children known returned collected).weaken
          (ReplayContracts.rules expected)
          (pre := fun world => ReplayContracts.ReadReply (ReplayStore.valueKey current) none world ∧ Ready expected assignment world)
          (fun _ _ holds => by simpa [same] using holds.2 joining)
        apply Rules.except_bind_known _ _ _ joined joinedResult
        apply Rules.except_bind (middle := fun accepted world =>
          ReplayContracts.Created (ReplayStore.valueKey current)
            ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, joined⟩ accepted world ∧
              Recording.JoinReady expected world.records current)
        · apply Rules.except_lift _ (ReplayContracts.preserving expected
            (ReplayContracts.observed_create expected worker _ _ known)
            (fun _ _ _ _ grows ready => ready.extend grows))
          exact fun _ _ _ holds => holds
        · intro accepted
          apply Rules.Program.weaken _ (checked_then expected _ joined accepted _ _ _ continued)
          exact fun _ _ holds => ⟨holds.1.1, (fun _ => by simpa [same] using holds.2), holds.1.2⟩

/-- Every pure active segment has a sufficient fuel bound, independently of
which correct records other workers create while it runs. Its result preserves
the semantic and reconstruction certificates; sufficient fuel excludes errors.
The bound is derived from the source, not from an assumed completed execution. -/
theorem active_bounded (expected : Journal)
    {current : Location} {program : Cloud (SimM World) α} {outcome}
    (meaning : Specification.Complete expected current program outcome)
    (nonempty : 0 < current.size) :
    ∃ bound, ∀ (worker : WorkerId) (assignment : Assignment) (encode : α → Json),
      assignment.branch = Location.branchStart current →
      expected.lookup (ReplayStore.returnKey assignment.branch) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩ →
      ∀ fuel, (ReplayContracts.rules expected).Program (Ready expected assignment)
      (fun result world => Result expected assignment.branch (Parallel.recorded encode outcome) encode program current result world ∧
        FuelBound fuel bound result ∧ ForksAfter assignment current result)
      (walk (observed worker).records blobs assignment fuel encode program current true).run := by
  induction meaning with
  | pure value =>
    refine ⟨1, fun worker assignment encode branch known fuel => ?_⟩
    cases fuel with
    | zero => exact fun _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (by decide),
        by intro location count impossible; cases impossible⟩
    | succ fuel =>
      simpa only [walk, Bool.true_or, ite_true, Parallel.recorded] using!
        finish expected worker assignment.branch (.success (encode value)) encode _ _ (Ready expected assignment) known
  | fail error next =>
    refine ⟨1, fun worker assignment encode branch known fuel => ?_⟩
    cases fuel with
    | zero => exact fun _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (by decide),
        by intro location count impossible; cases impossible⟩
    | succ fuel =>
      simpa only [walk, Bool.true_or, ite_true, Parallel.recorded] using!
        finish expected worker assignment.branch (.failure error) encode _ _ (Ready expected assignment) known
  | delay next rest ih =>
    obtain ⟨bound, continued⟩ := ih nonempty
    refine ⟨bound + 1, fun worker assignment encode branch known fuel => ?_⟩
    cases fuel with
    | zero => exact fun _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (Nat.zero_lt_succ _),
        by intro location count impossible; cases impossible⟩
    | succ fuel =>
      simp only [walk, Bool.true_or]
      apply Rules.Program.weaken_post _ _ (continued worker assignment encode branch known fuel)
      exact fun _ _ _ holds => ⟨holds.1.lift (fun _ path => path.delay next), holds.2.1.succ, holds.2.2⟩
  | exec codec label body next roundtrip present rest ih =>
    obtain ⟨bound, continued⟩ := ih (by simpa [LeanCloud.Location.next] using nonempty)
    refine ⟨bound + 1, fun worker assignment encode branch known fuel => ?_⟩
    cases fuel with
    | zero => exact fun _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (Nat.zero_lt_succ _),
        by intro location count impossible; cases impossible⟩
    | succ fuel =>
      simp only [walk, Bool.true_or, ite_true]
      apply exec_then expected worker _ codec label body (Ready expected assignment)
        (ready_stable expected assignment) present
      apply Rules.except_bind_value _ _ _ (body ()) (decode expected _ codec _ _ roundtrip)
      apply Rules.Program.weaken_post _ _ (ReplayContracts.preserve_record expected _ _
        (continued worker assignment encode (by simpa using branch) known fuel))
      intro result world invariant holds
      exact ⟨holds.1.1.lift (fun _ path => path.command codec (.exec label (fun _ => pure (body ()))) next _ _ _
        nonempty holds.2 (by simp) rfl roundtrip), holds.1.2.1.succ, holds.1.2.2.next nonempty⟩
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    obtain ⟨bound, continued⟩ := ih (by simpa [LeanCloud.Location.next] using nonempty)
    refine ⟨bound + 1, fun worker assignment encode branch known fuel => ?_⟩
    cases fuel with
    | zero => exact fun _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (Nat.zero_lt_succ _),
        by intro location count impossible; cases impossible⟩
    | succ fuel =>
      apply parallel expected worker assignment fuel encode _ codec count branches next _ _ present
        ⟨_, codec, outcomes, by simpa [collected, Parallel.recorded] using present, returned⟩
        (fun canFork world _ _ => ⟨⟨⟨branch, ⟨_, codec, outcomes, by simpa [collected, Parallel.recorded] using present, returned⟩⟩,
          by intro location size same; cases same; exact Suspension.immediate world.records encode _ codec count branches next⟩, Or.inl rfl,
          by
            intro location size same
            cases same
            exact ⟨Routing.Follows.refl _ nonempty, fun joining => by simpa [joining] using canFork⟩⟩)
      apply Rules.except_bind_value _ _ _ _ (decode_group expected _ codec count _ roundtrip
        (by simpa using Parallel.sequence_size _ _ collected))
      apply Rules.Program.weaken_post _ _ (ReplayContracts.preserve_record expected _ _
        (continued worker assignment encode (by simpa using branch) known fuel))
      intro result world invariant holds
      exact ⟨holds.1.1.lift (fun _ path => path.joined codec count branches next _ _ _ nonempty holds.2 (by simp) rfl
        (roundtrip.array codec _) (by simpa using Parallel.sequence_size _ _ collected)), holds.1.2.1.succ,
        holds.1.2.2.next nonempty⟩
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    refine ⟨1, fun worker assignment encode branch known fuel => ?_⟩
    cases fuel with
    | zero => exact fun _ _ _ => ⟨⟨rfl, by intro location count impossible; cases impossible⟩, Or.inr (by decide),
        by intro location count impossible; cases impossible⟩
    | succ fuel =>
      apply parallel expected worker assignment fuel encode _ codec count branches next _ _ present
        ⟨_, codec, outcomes, by simpa [collected, Parallel.recorded] using present, returned⟩
        (fun canFork world _ _ => ⟨⟨⟨branch, ⟨_, codec, outcomes, by simpa [collected, Parallel.recorded] using present, returned⟩⟩,
          by intro location size same; cases same; exact Suspension.immediate world.records encode _ codec count branches next⟩, Or.inl rfl,
          by
            intro location size same
            cases same
            exact ⟨Routing.Follows.refl _ nonempty, fun joining => by simpa [joining] using canFork⟩⟩)
      exact finish expected worker assignment.branch _ encode _ _ _ known

/-- The entry point either reuses the specified durable return or invokes the
certified replay walk. The return probe preserves the walk's precondition. -/
theorem entry [codec : Codec α] (expected : Journal) (worker : WorkerId) (fuel : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (assignment : Assignment) (outcome : Exit)
    (known : expected.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, outcome⟩)
    (valid : (!assignment.location.isEmpty && assignment.location[0]!.1 == 0) = true)
    (pre : World → Prop) (stable : (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference pre)
    (post : Except CloudError Progress → World → Prop)
    (completed : ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      world.records.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, outcome⟩ →
      post (.ok .done) world)
    (traversal : (ReplayContracts.rules expected).Program pre post
      (walk (observed worker).records blobs assignment fuel codec.encode (program input) Location.root).run) :
    (ReplayContracts.rules expected).Program pre post
      (step (observed worker).records blobs fuel program input assignment).run := by
  unfold ReplayInterpreter.step
  simp only [valid, ite_true]
  apply Rules.except_bind (middle := fun reply world => ReplayContracts.OutcomeReply assignment.branch outcome reply world ∧ pre world)
  · apply Rules.Program.weaken_post _ _ (ReplayContracts.preserving expected
      (ReplayContracts.outcome expected worker assignment.branch outcome known) stable)
    intro result world invariant holds
    cases result with
    | error _ => exact holds.1.elim
    | ok _ => exact holds
  · intro reply
    cases reply with
    | some value => exact fun world invariant holds => completed world invariant holds.2 holds.1.2
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      exact traversal.weaken _ (fun _ _ holds => holds.2)

end LeanCloud.Proofs.ExecutionContracts
