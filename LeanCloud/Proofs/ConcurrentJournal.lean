import LeanCloud.Proofs.SimulationSafety
import LeanCloud.Proofs.JournalRecovery
import LeanCloud.SimulationBackend

/-! Concurrent calls to the actual journal publisher. A fixed expected journal
expresses same-key agreement. Safety holds for arbitrary finite legal schedules,
including partial publication, delayed responses, crashes, and restarts. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean LeanEff Simulation SimulationBackend JournalAdapter

def view (state : Durable) : Journal := fun key => state.records.lookup key

/-- Compatible writes accumulate at the front of the ideal database log.
The suffix relation preserves the order of intermediate observations. -/
def Grows (before after : Durable) : Prop :=
  Extends (view before) (view after) ∧ before.records <:+ after.records

instance {before after : Durable} : CoeFun (Grows before after)
    (fun _ => ∀ key value, view before key = some value → view after key = some value) where
  coe growth := growth.1

theorem Grows.refl (state : Durable) : Grows state state := ⟨.refl _, List.suffix_rfl⟩

theorem Grows.trans {first middle last : Durable}
    (a : Grows first middle) (b : Grows middle last) : Grows first last :=
  ⟨a.1.trans b.1, a.2.trans b.2⟩

def Valid (expected : Journal) (state : Durable) : Prop := Extends (view state) expected

private def store (key : String) (value : Json) (state : Durable) : Durable :=
  { state with records := (key, value) :: state.records }

private theorem view_store (key : String) (value : Json) (state : Durable) :
    view (store key value state) = (view state).write key value := by
  funext other
  by_cases same : other = key
  · subst other
    simp [view, store, Journal.write]
  · simp [view, store, Journal.write, same, List.lookup_cons, beq_eq_false_iff_ne.mpr same]

private theorem store_safe {expected : Journal} {key : String} {value : Json}
    (intended : expected key = some value) (state : Durable) (valid : Valid expected state) :
    Valid expected (store key value state) ∧ Grows state (store key value state) := by
  obtain ⟨growth, bounded⟩ := extends_write valid intended
  refine ⟨?_, ?_, List.suffix_cons _ _⟩
  · simpa only [Valid, view_store] using bounded
  · simpa only [view_store] using growth

def Published (key : String) (value : Json) (returned : Bool × Unit) (state : Durable) : Prop :=
  returned = (true, ()) ∧ view state key = some value

/-- Even an old `none` response can safely lead to a write: the intervening
state need only agree with the expected journal, not still have an absent key. -/
theorem putSame_safe (expected : Journal) (key : String) (value : Json)
    (intended : expected key = some value) (reflexive : (value == value) = true)
    (state : Durable) :
    Safe (Valid expected) Grows (Published key value)
      (.ofProgram ((JournalDb.putSame rawDb key value).run ())) state := by
  dsimp [JournalDb.putSame, rawDb, StateT.run, StateT.bind, StateT.pure,
    SimM.atomic, EffF.send, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨valid, .refl _⟩
  · intro observed valid growth
    apply Safe.responding
    intro current currentValid later
    dsimp [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind]
    cases stored : observed.records.lookup key with
    | none =>
      simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
        bind, pure, Simulation.Worker.ofProgram]
      apply Safe.waiting
      · intro committed committedValid _
        exact store_safe intended committed committedValid
      · intro committed committedValid _
        apply Safe.responding
        intro delivered deliveredValid extended
        simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
          Simulation.Worker.ofProgram]
        apply Safe.finished
        intro final finalValid last
        refine ⟨rfl, ?_⟩
        apply last key value
        apply extended key value
        simp [view]
    | some old =>
      have same : old = value := Option.some.inj ((valid key old stored).symm.trans intended)
      subst old
      simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
        bind, pure, StateT.pure, Simulation.Worker.ofProgram, reflexive]
      apply Safe.finished
      intro final finalValid last
      exact ⟨rfl, last key value (later key value stored)⟩

private theorem calls_safe (expected : Journal) (start : Fin count → M α)
    (post : Fin count → α → Durable → Prop)
    (fresh : ∀ worker state, Valid expected state →
      Safe (Valid expected) Grows (post worker) (.ofProgram (start worker)) state)
    (initial : Durable) (bounded : Valid expected initial)
    (events : List (Event count)) (final : Simulation.State Durable α count)
    (executed : Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    Grows initial final.durable ∧ Valid expected final.durable ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned →
        post worker returned final.durable := by
  have clock elapsed state (valid : Valid expected state) :
      Valid expected (advance elapsed state) ∧ Grows state (advance elapsed state) :=
    ⟨valid, .refl _⟩
  have safe : AllSafe (Valid expected) Grows post (Simulation.State.initial initial start) :=
    ⟨bounded, fun worker => fresh worker initial bounded⟩
  obtain ⟨growth, valid, workers⟩ := Simulation.run_safe (valid := Valid expected) (grows := Grows)
    Grows.refl
    (fun first second => first.trans second) start advance post fresh clock events safe executed
  refine ⟨growth, valid, fun worker returned recorded => ?_⟩
  exact (workers worker).returned Grows.refl valid recorded

/-- Any number of agreeing writers, under any finite legal schedule. Records
can only accumulate, and every returned call succeeds with its value present.
Workers may still be paused or crashed; this theorem makes no liveness claim.
Agreement with `expected` is a hypothesis, not yet derived from Cloud semantics. -/
theorem putSame_concurrent (expected : Journal)
    (keys : Fin count → String) (values : Fin count → Json)
    (agrees : ∀ worker, expected (keys worker) = some (values worker))
    (reflexive : ∀ worker, (values worker == values worker) = true)
    (initial : Durable) (bounded : Valid expected initial)
    (events : List (Event count)) (final : Simulation.State Durable (Bool × Unit) count)
    (executed :
      let start := fun worker => (JournalDb.putSame rawDb (keys worker) (values worker)).run ()
      Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    Grows initial final.durable ∧ Valid expected final.durable ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned →
        Published (keys worker) (values worker) returned final.durable := by
  apply calls_safe expected _ _ ?_ initial bounded events final executed
  intro worker state _
  exact putSame_safe expected (keys worker) (values worker) (agrees worker) (reflexive worker) state

private theorem apply_one (next : α → SimM δ β) : ArrsF.apply (.one next) = next := by
  funext value
  simp [ArrsF.apply, ArrsF.viewL]

/-- A read may be delivered after other workers have extended the journal. -/
theorem read_safe (expected : Journal) (key : String)
    (next : ArrsF (Atomic Durable) (Option Json) α) (post : α → Durable → Prop)
    (state : Durable)
    (resume : ∀ observed current, Valid expected observed → Valid expected current →
      Grows state observed → Grows observed current →
      Safe (Valid expected) Grows post
        (.ofProgram (ArrsF.apply next (view observed key))) current) :
    Safe (Valid expected) Grows post
      (.waiting (fun state => (state.records.lookup key, state)) next) state := by
  apply Safe.waiting
  · intro current valid _
    exact ⟨valid, .refl _⟩
  · intro observed valid growth
    exact .responding fun current kept later => resume observed current valid kept growth later

private theorem write_safe (expected : Journal) (key : String) (value : Json)
    (intended : expected key = some value)
    (next : ArrsF (Atomic Durable) Bool α) (post : α → Durable → Prop) (state : Durable)
    (resume : ∀ current, Valid expected current → Grows state current →
      view current key = some value →
      Safe (Valid expected) Grows post (.ofProgram (ArrsF.apply next true)) current) :
    Safe (Valid expected) Grows post
      (.waiting (fun state => (true, store key value state)) next) state := by
  apply Safe.waiting
  · intro current valid _
    exact store_safe intended current valid
  · intro committed valid growth
    apply Safe.responding
    intro delivered kept later
    have stored := (store_safe intended committed valid).2
    apply resume delivered kept (growth.trans (stored.trans later))
    apply later key value
    simp [view, store]

/-- The existing loop body, named only to keep its safety proof readable. -/
private abbrev putChild (key : String) (children : Array (Option Exit))
    (index : Nat) (_ : Option Bool × Unit) : StateT Unit M (ForInStep (Option Bool × Unit)) := do
  match children[index]! with
  | some outcome =>
    if ← JournalDb.putSame rawDb (JournalDb.childKey key index) (toJson outcome) then
      return .yield (none, ())
    else return .done (some false, ())
  | _ => return .yield (none, ())

private theorem putChildren_safe (expected : Journal) (key : String)
    (children : Array (Option Exit)) (indices : List Nat)
    (agrees : Agrees (indices.filterMap (childRecord key children)) expected)
    (next : (Option Bool × Unit) → StateT Unit M α) (post : (α × Unit) → Durable → Prop)
    (state : Durable) (valid : Valid expected state)
    (resume : ∀ current, Valid expected current → Grows state current →
      JournalAdapter.Published (indices.filterMap (childRecord key children)) (view current) →
      Safe (Valid expected) Grows post (.ofProgram ((next (none, ())).run ())) current) :
    Safe (Valid expected) Grows post
      (.ofProgram ((forIn indices (none, ()) (putChild key children) >>= next).run ())) state := by
  induction indices generalizing state with
  | nil =>
    simp only [List.forIn_nil, StateT.run, StateT.bind, StateT.pure, bind, pure, EffF.bind]
    exact resume state valid (.refl _) (by simp [JournalAdapter.Published])
  | cons index rest ih =>
    rw [List.forIn_cons]
    cases slot : children[index]! with
    | none =>
      simp only [putChild, slot, StateT.run, StateT.bind, StateT.pure, bind, pure, EffF.bind]
      apply ih
      · simpa [childRecord, slot] using agrees
      · exact valid
      · intro current valid growth published
        apply resume current valid growth
        simpa [childRecord, slot] using published
    | some outcome =>
      have head := agrees (JournalDb.childKey key index, toJson outcome)
        (by simp [childRecord, slot])
      have tail : Agrees (rest.filterMap (childRecord key children)) expected := by
        intro entry member
        exact agrees entry (by simp [childRecord, slot, member])
      have remaining (current : Durable) (kept : Valid expected current)
          (growth : Grows state current)
          (stored : view current (JournalDb.childKey key index) = some (toJson outcome)) :
          Safe (Valid expected) Grows post
            (.ofProgram ((forIn rest (none, ()) (putChild key children) >>= next).run ())) current := by
        apply ih tail current kept
        intro final finalValid later published
        apply resume final finalValid (growth.trans later)
        intro entry member
        simp only [List.filterMap_cons, childRecord, slot, Option.map_some,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact later _ _ stored
        · exact published _ member
      simp only [putChild, slot, JournalDb.putSame, rawDb, StateT.run, StateT.bind,
        SimM.atomic, EffF.send, EffF.bind, bind, pure, Simulation.Worker.ofProgram]
      apply read_safe
      intro observed current observedValid currentValid growth later
      dsimp [view]
      cases stored : observed.records.lookup (JournalDb.childKey key index) with
      | none =>
        simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
          Simulation.Worker.ofProgram]
        apply write_safe expected _ _ head.1
        intro delivered deliveredValid extended written
        simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
          pure, StateT.pure, ↓reduceIte, Simulation.Worker.ofProgram]
        exact remaining delivered deliveredValid ((growth.trans later).trans extended) written
      | some old =>
        have same : old = toJson outcome :=
          Option.some.inj ((observedValid _ _ stored).symm.trans head.1)
        subst old
        simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
          pure, StateT.pure, head.2, ↓reduceIte]
        exact remaining current currentValid (growth.trans later) (later _ _ stored)

/-- Success means that every physical record prescribed by this logical result
is present. Other workers may have published additional records. -/
def Publication (key : String) (result : Result) (returned : Bool × Unit)
    (state : Durable) : Prop :=
  returned = (true, ()) ∧ JournalAdapter.Published (records key result) (view state)

/-- Safety of the actual adapter, with each read and write still a separate
suspension point. The whole publication is not assumed atomic. -/
theorem put_safe (expected : Journal) (key : String) (result : Result)
    (agrees : Agrees (records key result) expected)
    (state : Durable) :
    Safe (Valid expected) Grows (Publication key result)
      (.ofProgram ((JournalDb.put rawDb key (toJson result)).run ())) state := by
  unfold JournalDb.put
  rw [result_roundtrip]
  cases result with
  | completed outcome =>
    obtain ⟨intended, reflexive⟩ := agrees (JournalDb.resultKey key, toJson outcome) (by simp [records])
    have same : Publication key (.completed outcome) = Published (JournalDb.resultKey key) (toJson outcome) := by
      funext returned current
      simp [Publication, JournalAdapter.Published, records, Published]
    rw [same]
    simpa only [StateT.run, StateT.bind, StateT.pure, bind, pure, EffF.bind] using
      putSame_safe expected _ _ intended reflexive state
  | suspended children =>
    have head := agrees (JournalDb.forkKey key, toJson children.size) (by simp [records])
    have tail : Agrees ((List.range children.size).filterMap (childRecord key children)) expected :=
      fun entry member => agrees entry (by simp [records, member])
    -- The continuation generated by the adapter's early-return loop.
    let next : (Option Bool × Unit) → StateT Unit M Bool := fun result =>
      Break.runK result.1 (fun _ => pure true) pure
    have remaining (current : Durable) (kept : Valid expected current)
        (stored : view current (JournalDb.forkKey key) = some (toJson children.size)) :
        Safe (Valid expected) Grows (Publication key (.suspended children))
          (.ofProgram ((forIn (List.range children.size) (none, ()) (putChild key children) >>= next).run ())) current := by
      apply putChildren_safe expected key children _ tail next _ current kept
      intro delivered deliveredValid growth published
      apply Safe.finished
      intro final _ later
      refine ⟨rfl, ?_⟩
      intro entry member
      simp only [records, List.mem_cons] at member
      rcases member with rfl | member
      · exact later _ _ (growth _ _ stored)
      · exact later _ _ (published _ member)
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    simp only [JournalDb.putSame, rawDb, StateT.run, StateT.bind, StateT.pure,
      SimM.atomic, EffF.send, EffF.bind, bind, pure, Simulation.Worker.ofProgram]
    apply read_safe
    intro observed current observedValid currentValid growth later
    dsimp [view]
    cases stored : observed.records.lookup (JournalDb.forkKey key) with
    | none =>
      simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
      apply write_safe expected _ _ head.1
      intro delivered deliveredValid extended written
      simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, ↓reduceIte]
      exact remaining delivered deliveredValid written
    | some old =>
      have same : old = toJson children.size :=
        Option.some.inj ((observedValid _ _ stored).symm.trans head.1)
      subst old
      simp only [apply_one, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
        StateT.pure, pure, head.2, ↓reduceIte]
      exact remaining current currentValid (later _ _ stored)

/-- Arbitrarily many compatible full or partial publications can interleave,
crash, and restart. Every prefix retains the original records; each returned
call succeeds and has all its own records present in the final shared journal.
This is safety, not a claim that the schedule eventually finishes each call. -/
theorem put_concurrent (expected : Journal)
    (keys : Fin count → String) (results : Fin count → Result)
    (agrees : ∀ worker, Agrees (records (keys worker) (results worker)) expected)
    (initial : Durable) (bounded : Valid expected initial)
    (events : List (Event count)) (final : Simulation.State Durable (Bool × Unit) count)
    (executed :
      let start := fun worker => (JournalDb.put rawDb (keys worker) (toJson (results worker))).run ()
      Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    Grows initial final.durable ∧ Valid expected final.durable ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned →
        Publication (keys worker) (results worker) returned final.durable := by
  apply calls_safe expected _ _ ?_ initial bounded events final executed
  intro worker state _
  exact put_safe expected (keys worker) (results worker) (agrees worker) state

end LeanCloud.Proofs.ConcurrentJournal
