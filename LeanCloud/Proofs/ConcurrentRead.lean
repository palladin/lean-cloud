import LeanCloud.Proofs.ConcurrentJournal

/-! Reads of an immutable journal under concurrent publication. A read assembles
separately observed slots; it need not describe a single instantaneous snapshot.
Present values persist, and records present before the read cannot be missed. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean LeanEff Simulation SimulationBackend JournalAdapter JournalDb

/-- The expected physical records have the types required by the adapter.
This states format validity, not agreement between a cached result and its children. -/
structure Readable (expected : Journal) (key : String) : Prop where
  result : ∀ value, expected (resultKey key) = some value →
    ∃ outcome : Exit, value = toJson outcome
  fork : ∀ value, expected (forkKey key) = some value →
    ∃ count : Nat, value = toJson count
  child : ∀ index value, expected (childKey key index) = some value →
    ∃ outcome : Exit, value = toJson outcome

/-- Absence can be stale. A value observed present must still be present later. -/
def Slot (key : String) (before after : Durable) (index : Nat) : Option Exit → Prop
  | none => view before (childKey key index) = none
  | some outcome => view after (childKey key index) = some (toJson outcome)

/-- The observations in their original child-index order. -/
inductive Slots (key : String) (before after : Durable) : List Nat → List (Option Exit) → Prop where
  | nil : Slots key before after [] []
  | cons {index slot indices slots} (head : Slot key before after index slot)
      (tail : Slots key before after indices slots) : Slots key before after (index :: indices) (slot :: slots)

/-- A returned view is bounded by the journal before the read and after it.
The fork case deliberately permits different observation times for its slots. -/
inductive Observation (key : String) (before after : Durable) : Option Json → Prop where
  | missing (result : view before (resultKey key) = none)
      (fork : view before (forkKey key) = none) : Observation key before after none
  | cached (outcome : Exit) (stored : view after (resultKey key) = some (toJson outcome)) :
      Observation key before after (some (toJson (Result.completed outcome)))
  | fork (children : Array (Option Exit))
      (uncached : view before (resultKey key) = none)
      (descriptor : view after (forkKey key) = some (toJson children.size))
      (slots : Slots key before after (List.range children.size) children.toList) :
      Observation key before after (some (toJson (Result.settle children)))

private theorem absent_before {before after : Durable} (growth : Grows before after)
    {key : String} (absent : view after key = none) : view before key = none := by
  cases stored : view before key with
  | none => rfl
  | some value => have := growth key value stored; simp [absent] at this

private theorem Slots.length {key before after indices slots}
    (observed : Slots key before after indices slots) : indices.length = slots.length := by
  induction observed with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem Slots.later {key : String} {before current after : Durable}
    {indices : List Nat} {slots : List (Option Exit)}
    (observed : Slots key before current indices slots)
    (growth : Grows current after) : Slots key before after indices slots := by
  induction observed with
  | nil => exact .nil
  | @cons index slot indices slots head tail ih =>
    apply Slots.cons ?_ ih
    cases slot with
    | none => exact head
    | some outcome => exact growth _ _ head

/-- The adapter's loop body, retaining the actual error and early-return paths. -/
private abbrev getChild (key : String) (index : Nat)
    (acc : Option (Option Json) × Array (Option Exit)) :
    StateT Unit M (ForInStep (Option (Option Json) × Array (Option Exit))) := do
  match ← rawDb.get (childKey key index) with
  | none => return .yield (none, acc.2.push none)
  | some value =>
    match fromJson? (α := Exit) value with
    | .ok outcome => return .yield (none, acc.2.push (some outcome))
    | .error error => return .done (some (some (Json.str s!"Invalid child result: {error}")), acc.2)

private theorem apply_one (next : α → SimM δ β) : ArrsF.apply (.one next) = next := by
  funext value
  simp [ArrsF.apply, ArrsF.viewL]

private theorem getChildren_safe (expected : Journal) (key : String) (format : Readable expected key)
    (before : Durable) (indices : List Nat) (acc : Array (Option Exit))
    (next : (Option (Option Json) × Array (Option Exit)) → StateT Unit M α)
    (post : (α × Unit) → Durable → Prop) (state : Durable)
    (valid : Valid expected state) (prior : Grows before state)
    (resume : ∀ current, Valid expected current → Grows state current →
      ∀ slots, Slots key before current indices slots →
      Safe (Valid expected) Grows post
        (.ofProgram ((next (none, acc ++ slots.toArray)).run ())) current) :
    Safe (Valid expected) Grows post
      (.ofProgram ((forIn indices (none, acc) (getChild key) >>= next).run ())) state := by
  induction indices generalizing state acc with
  | nil =>
    simp only [List.forIn_nil, StateT.run, StateT.bind, StateT.pure, bind, pure, EffF.bind]
    simpa only [List.toArray, Array.append_empty, StateT.run] using
      resume state valid (.refl _) [] .nil
  | cons index rest ih =>
    have remaining (slot : Option Exit) (current : Durable) (kept : Valid expected current)
        (growth : Grows state current) (seen : Slot key before current index slot) :
        Safe (Valid expected) Grows post
          (.ofProgram ((forIn rest (none, acc.push slot) (getChild key) >>= next).run ())) current := by
      apply ih (acc.push slot) current kept (prior.trans growth)
      intro final finalValid later slots observed
      have head : Slot key before final index slot := by
        cases slot with
        | none => exact seen
        | some outcome => exact later _ _ seen
      have safe := resume final finalValid (growth.trans later) (slot :: slots) (.cons head observed)
      simpa [Array.push_eq_append, Array.append_assoc, -Array.append_singleton] using safe
    rw [List.forIn_cons]
    simp only [getChild, rawDb, StateT.run, StateT.bind, SimM.atomic, EffF.send,
      EffF.bind, bind, pure, Simulation.Worker.ofProgram]
    apply read_safe
    intro observed current observedValid currentValid growth later
    dsimp [view]
    cases stored : observed.records.lookup (childKey key index) with
    | none =>
      simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
        StateT.pure, pure]
      exact remaining none current currentValid (growth.trans later)
        (absent_before (prior.trans growth) stored)
    | some value =>
      obtain ⟨outcome, encoded⟩ := format.child index value (observedValid _ _ stored)
      subst value
      simp only [exit_roundtrip, apply_one, ArrsF.apply, ArrsF.viewL,
        ArrsF.viewLAppend, EffF.bind, StateT.pure, pure]
      exact remaining (some outcome) current currentValid (growth.trans later)
        (later _ _ stored)

/-- The actual reader is safe under arbitrary compatible journal extensions
between every commit and reply. The lower bound may precede a restarted attempt. -/
theorem get_safe (expected : Journal) (key : String) (format : Readable expected key)
    (before state : Durable) (prior : Grows before state) :
    Safe (Valid expected) Grows (fun returned final => Observation key before final returned.1)
      (.ofProgram ((JournalDb.get rawDb key).run ())) state := by
  let post := fun returned : Option Json × Unit => fun final => Observation key before final returned.1
  let next : (Option (Option Json) × Array (Option Exit)) → StateT Unit M (Option Json) := fun result =>
    Break.runK result.1 (fun _ => pure (some (toJson (Result.settle result.2)))) pure
  have remaining (count : Nat) (current : Durable) (kept : Valid expected current)
      (growth : Grows before current) (uncached : view before (resultKey key) = none)
      (descriptor : view current (forkKey key) = some (toJson count)) :
      Safe (Valid expected) Grows post
        (.ofProgram ((forIn (List.range count) (none, #[]) (getChild key) >>= next).run ())) current := by
    apply getChildren_safe expected key format before _ #[] next post current kept growth
    intro delivered deliveredValid later slots observed
    have size : slots.length = count := by simpa using observed.length.symm
    apply Safe.finished
    intro final _ extended
    simp only [post, Array.empty_append]
    apply Observation.fork slots.toArray uncached
    · simpa [size] using extended _ _ (later _ _ descriptor)
    · simpa [size] using observed.later extended
  unfold JournalDb.get
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [rawDb, StateT.run, StateT.bind, SimM.atomic,
    EffF.send, EffF.bind, bind, pure, Simulation.Worker.ofProgram]
  apply read_safe
  intro cachedAt current cachedValid currentValid growth later
  dsimp [view]
  cases cached : cachedAt.records.lookup (resultKey key) with
  | some value =>
    obtain ⟨outcome, encoded⟩ := format.result value (cachedValid _ _ cached)
    subst value
    simp only [exit_roundtrip, apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend,
      EffF.bind, StateT.pure, pure, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final _ extended
    exact .cached outcome (extended _ _ (later _ _ cached))
  | none =>
    have uncached := absent_before (prior.trans growth) cached
    simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend,
      EffF.bind, Simulation.Worker.ofProgram]
    apply read_safe
    intro forkAt delivered forkValid deliveredValid forkGrowth forkLater
    dsimp [view]
    cases descriptor : forkAt.records.lookup (forkKey key) with
    | none =>
      simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend,
        EffF.bind, StateT.pure, pure, Simulation.Worker.ofProgram]
      apply Safe.finished
      intro final _ _
      exact .missing uncached (absent_before (((prior.trans growth).trans later).trans forkGrowth) descriptor)
    | some value =>
      obtain ⟨count, encoded⟩ := format.fork value (forkValid _ _ descriptor)
      subst value
      simp only [show fromJson? (toJson count) = Except.ok count from rfl,
        apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend,
        EffF.bind]
      exact remaining count delivered deliveredValid
        ((((prior.trans growth).trans later).trans forkGrowth).trans forkLater)
        uncached (forkLater _ _ descriptor)

/-- Lift the read contract to the actual simulator, including reader crashes
and restarts. Other workers may run arbitrary programs whose boundary-safety
proofs preserve the expected journal and previously stored values. Their result
values are irrelevant to this reader's contract. -/
theorem get_concurrent (expected : Journal) (key : String) (format : Readable expected key)
    (reader : Fin count) (start : Fin count → M (Option Json × Unit))
    (readerAction : start reader = (JournalDb.get rawDb key).run ())
    (background : ∀ worker, worker ≠ reader → ∀ state, Valid expected state →
      Safe (Valid expected) Grows (fun _ _ => True) (.ofProgram (start worker)) state)
    (initial : Durable) (bounded : Valid expected initial)
    (events : List (Event count)) (final : Simulation.State Durable (Option Json × Unit) count)
    (executed : Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    Grows initial final.durable ∧ Valid expected final.durable ∧
      ∀ returned, (final.workers reader).outcome? = some returned →
        Observation key initial final.durable returned.1 := by
  let invariant := fun state => Valid expected state ∧ Grows initial state
  let post := fun worker (returned : Option Json × Unit) final =>
    if worker = reader then Observation key initial final returned.1 else True
  have preserved before after (kept : invariant before) (valid : Valid expected after)
      (growth : Grows before after) : invariant after := ⟨valid, kept.2.trans growth⟩
  have fresh worker state (kept : invariant state) :
      Safe invariant Grows (post worker) (.ofProgram (start worker)) state := by
    by_cases same : worker = reader
    · subst worker
      simp only [post, ↓reduceIte, readerAction]
      exact (get_safe expected key format initial state kept.2).strengthen invariant
        (fun _ h => h.1) preserved
    · simp only [post, same, ↓reduceIte]
      exact (background worker same state kept.1).strengthen invariant (fun _ h => h.1) preserved
  have clock elapsed state (kept : invariant state) :
      invariant (advance elapsed state) ∧ Grows state (advance elapsed state) := ⟨kept, .refl _⟩
  have safe : AllSafe invariant Grows post (Simulation.State.initial initial start) :=
    ⟨⟨bounded, .refl _⟩, fun worker => fresh worker initial ⟨bounded, .refl _⟩⟩
  obtain ⟨growth, kept, workers⟩ := Simulation.run_safe (valid := invariant) (grows := Grows)
    Grows.refl (fun first second => first.trans second)
    start advance post fresh clock events safe executed
  refine ⟨growth, kept.1, fun returned finished => ?_⟩
  simpa only [post, ↓reduceIte] using
    (workers reader).returned Grows.refl kept finished

end LeanCloud.Proofs.ConcurrentJournal
