import LeanCloud.Proofs.SimulationLiveness

/-! Proof-only history for the existing simulator. Every atomic operation and
clock update retains its preceding durable state. Program results, worker
continuations, legal events, crashes, and restart behavior are unchanged. -/

namespace LeanCloud.Simulation.History
open LeanEff

structure Store (δ : Type) where
  current : δ
  past : List δ := []

def Store.states (store : Store δ) : List δ := store.current :: store.past

/-- Newest state first. Remembering a publication survives its later removal
from the queue; it makes no claim that the message is still retained. -/
def Seen (predicate : δ → Prop) (store : Store δ) : Prop :=
  ∃ state ∈ store.states, predicate state

def Grows (before after : Store δ) : Prop := before.states <:+ after.states

theorem Grows.refl (state : Store δ) : Grows state state := ⟨[], rfl⟩

theorem Grows.trans {before middle after : Store δ}
    (first : Grows before middle) (last : Grows middle after) : Grows before after :=
  List.IsSuffix.trans first last

theorem Seen.now {predicate : δ → Prop} {store : Store δ} (present : predicate store.current) :
    Seen predicate store := ⟨store.current, List.mem_cons_self, present⟩

theorem Seen.grow {predicate : δ → Prop} {before after : Store δ}
    (seen : Seen predicate before) (growth : Grows before after) : Seen predicate after := by
  obtain ⟨state, member, present⟩ := seen
  exact ⟨state, growth.subset member, present⟩

/-- A remembered state is the current state of an actual history prefix. -/
theorem Seen.earlier {predicate : δ → Prop} {store : Store δ} (seen : Seen predicate store) :
    ∃ earlier, Grows earlier store ∧ predicate earlier.current := by
  obtain ⟨state, member, present⟩ := seen
  obtain ⟨newer, past, same⟩ := List.mem_iff_append.mp member
  exact ⟨⟨state, past⟩, ⟨newer, same.symm⟩, present⟩

/-- A durable transition occurred after this history offset. Both adjacent
states are retained, so later consumption cannot erase publication evidence. -/
def Occurred (since : Nat) (relation : δ → δ → Prop) (store : Store δ) : Prop :=
  ∃ before after past, since ≤ past.length ∧ relation before after ∧
    after :: before :: past <:+ store.states

theorem Grows.length {before after : Store δ} (growth : Grows before after) :
    before.past.length ≤ after.past.length := by
  have bound := List.IsSuffix.length_le growth
  simpa only [Store.states, List.length_cons, Nat.add_le_add_iff_right] using bound

/-- Two prefixes of one history are ordered by their offsets. -/
theorem Grows.between {before middle after : Store δ}
    (first : Grows before after) (second : Grows middle after)
    (ordered : before.past.length ≤ middle.past.length) : Grows before middle :=
  List.suffix_of_suffix_length_le first second (by simpa only [Store.states, List.length_cons] using Nat.add_le_add_right ordered 1)

theorem Occurred.grow {since : Nat} {relation : δ → δ → Prop} {before after : Store δ}
    (occurred : Occurred since relation before) (growth : Grows before after) : Occurred since relation after := by
  obtain ⟨first, last, past, bound, related, recorded⟩ := occurred
  exact ⟨first, last, past, bound, related, recorded.trans growth⟩

def operation (action : δ → α × δ) (store : Store δ) : α × Store δ :=
  let (value, current) := action store.current
  (value, ⟨current, store.states⟩)

def advance (clock : Nat → δ → δ) (elapsed : Nat) (store : Store δ) : Store δ :=
  ⟨clock elapsed store.current, store.states⟩

theorem operation_grows (action : δ → α × δ) (store : Store δ) :
    Grows store (operation action store).2 := ⟨[(action store.current).2], rfl⟩

theorem operation_occurred (action : δ → α × δ) (store : Store δ) (since : Nat)
    (bound : since ≤ store.past.length) (relation : δ → δ → Prop)
    (related : relation store.current (action store.current).2) :
    Occurred since relation (operation action store).2 :=
  ⟨store.current, (action store.current).2, store.past, bound, related, List.suffix_rfl⟩

theorem advance_grows (clock : Nat → δ → δ) (elapsed : Nat) (store : Store δ) :
    Grows store (advance clock elapsed store) := ⟨[clock elapsed store.current], rfl⟩

/-- Every earlier durable snapshot precedes every later snapshot according to
the original backend's interference relation. This lets later proofs use
journal growth between the checkpoints retained in response certificates. -/
def Ordered (rel : δ → δ → Prop) (store : Store δ) : Prop :=
  store.states.Pairwise (fun later earlier => rel earlier later)

theorem Ordered.initial (rel : δ → δ → Prop) (state : δ) : Ordered rel ⟨state, []⟩ :=
  .cons (by simp) .nil

theorem Ordered.earlier {rel : δ → δ → Prop} {before after : Store δ}
    (ordered : Ordered rel after) (growth : Grows before after) : Ordered rel before :=
  List.Pairwise.sublist growth.sublist ordered

theorem Ordered.growth {rel : δ → δ → Prop} {before after : Store δ}
    (ordered : Ordered rel after) (refl : ∀ state, rel state state) (growth : Grows before after) :
    rel before.current after.current := by
  obtain ⟨newer, same⟩ := growth
  cases newer with
  | nil =>
    have equal : before.current = after.current := Option.some.inj (congrArg List.head? same)
    rw [equal]
    exact refl _
  | cons current rest =>
    have tail : rest ++ before.states = after.past := congrArg List.tail same
    apply (List.pairwise_cons.mp ordered).1
    rw [← tail]
    simp [Store.states]

theorem Ordered.append {rel : δ → δ → Prop} {before : Store δ} {next : δ}
    (ordered : Ordered rel before) (refl : ∀ state, rel state state)
    (trans : ∀ {a b c}, rel a b → rel b c → rel a c) (growth : rel before.current next) :
    Ordered rel ⟨next, before.states⟩ := by
  apply List.pairwise_cons.mpr
  refine ⟨?_, ordered⟩
  intro state member
  have earlier : rel state before.current := by
    rcases List.mem_cons.mp member with rfl | member
    · exact refl _
    · exact (List.pairwise_cons.mp ordered).1 state member
  exact trans earlier growth

mutual
  /-- Add history to backend requests without changing the Cloud program or
  combining any primitive boundaries. This map is used only in proofs. -/
  def program (source : SimM δ α) : SimM (Store δ) α :=
    match source with
    | .pure value => .pure value
    | .impure (.step action) next => .impure (.step (operation action)) (continuation next)
  def continuation (next : ArrsF (Atomic δ) α β) : ArrsF (Atomic (Store δ)) α β :=
    match next with
    | .one next => .one (fun value => program (next value))
    | .append first rest => .append (continuation first) (continuation rest)
end

theorem program_bind (source : SimM δ α) (next : α → SimM δ β) :
    program (source >>= next) = program source >>= fun value => program (next value) := by
  cases source with
  | pure value => rfl
  | impure request rest => cases request; rfl

private def view (next : ArrsF.ViewL (Atomic δ) α β) : ArrsF.ViewL (Atomic (Store δ)) α β :=
  match next with
  | .one next => .one (fun value => program (next value))
  | .cons next rest => .cons (fun value => program (next value)) (continuation rest)

private theorem view_append (first : ArrsF (Atomic δ) α β) (rest : ArrsF (Atomic δ) β γ) :
    ArrsF.viewLAppend (continuation first) (continuation rest) = view (ArrsF.viewLAppend first rest) := by
  cases first with
  | one next => rfl
  | append left right => exact view_append left (.append right rest)
termination_by sizeOf first

private theorem view_continuation (next : ArrsF (Atomic δ) α β) :
    ArrsF.viewL (continuation next) = view (ArrsF.viewL next) := by
  cases next with
  | one next => rfl
  | append first rest => exact view_append first rest

theorem continuation_apply (next : ArrsF (Atomic δ) α β) (value : α) :
    ArrsF.apply (continuation next) value = program (ArrsF.apply next value) := by
  rw [ArrsF.apply, view_continuation, ArrsF.apply]
  cases seen : ArrsF.viewL next with
  | one first => rfl
  | cons first rest =>
    change (program (first value) >>= ArrsF.apply (continuation rest)) = program (first value >>= ArrsF.apply rest)
    rw [program_bind]
    congr 1
    funext value
    exact continuation_apply rest value
termination_by sizeOf next
decreasing_by simpa [seen] using ArrsF.viewL_rest_lt next

def worker : Worker δ α → Worker (Store δ) α
  | .waiting action next => .waiting (operation action) (continuation next)
  | .responding value next => .responding value (continuation next)
  | .stopped => .stopped
  | .finished value => .finished value

theorem worker_program (source : SimM δ α) : worker (.ofProgram source) = .ofProgram (program source) := by
  cases source with
  | pure value => rfl
  | impure request next => cases request; rfl

@[simp] theorem worker_phase (source : Worker δ α) : (worker source).phase = source.phase := by
  cases source <;> rfl

@[simp] theorem worker_outcome (source : Worker δ α) : (worker source).outcome? = source.outcome? := by
  cases source <;> rfl

def state (past : List δ) (source : State δ α count) : State (Store δ) α count :=
  ⟨⟨source.durable, past⟩, fun index => worker (source.workers index)⟩

theorem state_setWorker (past : List δ) (source : State δ α count)
    (index : Fin count) (next : Worker δ α) :
    state past (source.setWorker index next) = (state past source).setWorker index (worker next) := by
  apply (State.mk.injEq ..).mpr
  refine ⟨rfl, ?_⟩
  funext other
  by_cases same : other = index <;> simp [state, State.setWorker, same]

/-- Only commits and explicit clock updates add an observation. Losing a
reply, crashing, and restarting leave the durable history untouched. -/
def pastAfter (event : Event count) (source : State δ α count) (past : List δ) : List δ :=
  match event with
  | .commit _ | .advanceTime _ => source.durable :: past
  | _ => past

/-- One original event and one recorded event have the same result or error.
In particular recording neither enables invalid schedules nor hides failures. -/
theorem step_correspondence (start : Fin count → SimM δ α) (clock : Nat → δ → δ)
    (event : Event count) (source : State δ α count) (past : List δ) :
    Simulation.step (fun index => program (start index)) (advance clock) event (state past source) =
      (Simulation.step start clock event source).map (state (pastAfter event source past)) := by
  cases event with
  | commit index =>
    cases seen : source.workers index <;>
      simp only [Simulation.step, state, seen, worker, operation, Store.states, pastAfter, Except.map]
    case waiting action next =>
      congr 1
      apply (State.mk.injEq ..).mpr
      refine ⟨rfl, ?_⟩
      funext other
      by_cases same : other = index <;> simp [State.setWorker, same]
  | resume index =>
    cases seen : source.workers index <;>
      simp only [Simulation.step, state, seen, worker, pastAfter, Except.map]
    case responding value next =>
      rw [continuation_apply, ← worker_program]
      exact congrArg Except.ok (state_setWorker past source index (.ofProgram (ArrsF.apply next value))).symm
  | crash index =>
    cases seen : source.workers index <;>
      simp only [Simulation.step, state, seen, worker, pastAfter, Except.map]
    all_goals exact congrArg Except.ok (state_setWorker past source index .stopped).symm
  | restart index =>
    cases seen : source.workers index <;>
      simp only [Simulation.step, state, seen, worker, pastAfter, Except.map]
    case stopped =>
      rw [← worker_program]
      exact congrArg Except.ok (state_setWorker past source index (.ofProgram (start index))).symm
  | advanceTime elapsed => rfl

/-- Every finite original schedule lifts, with exactly the same worker
outcomes. No termination, queue fairness, or successful output is assumed. -/
theorem run_correspondence (start : Fin count → SimM δ α) (clock : Nat → δ → δ)
    (events : List (Event count)) (source final : State δ α count) (past : List δ)
    (executed : Simulation.run start clock events source = .ok final) :
    ∃ history, Simulation.run (fun index => program (start index)) (advance clock) events (state past source) =
      .ok (state history final) ∧ history.length ≤ past.length + events.length := by
  induction events generalizing source past with
  | nil => cases executed; exact ⟨past, rfl, Nat.le_refl _⟩
  | cons event events ih =>
    change (Simulation.step start clock event source >>= fun middle => Simulation.run start clock events middle) = _ at executed
    cases first : Simulation.step start clock event source with
    | error error => simp [first, bind, Except.bind] at executed
    | ok middle =>
      obtain ⟨history, tail, bound⟩ := ih middle (pastAfter event source past) (by simpa [first, bind, Except.bind] using executed)
      refine ⟨history, ?_, ?_⟩
      · change (Simulation.step _ _ event _ >>= fun middle => Simulation.run _ _ events middle) = _
        rw [step_correspondence, first]
        exact tail
      · cases event <;> simp only [pastAfter, List.length_cons] at bound ⊢ <;> omega

/-- Original safety contracts lift unchanged, with append-only history added
to the permitted interference relation. The recorded state is proof data. -/
theorem record_safe {valid : δ → Prop} {grows : δ → δ → Prop} {post : α → δ → Prop}
    {source : Worker δ α} {initial : δ} (safe : Safe valid grows post source initial)
    (refl : ∀ state, grows state state) (trans : ∀ {a b c}, grows a b → grows b c → grows a c) (past : List δ) :
    Safe (fun store : Store δ => valid store.current ∧ Ordered grows store)
      (fun before after : Store δ => grows before.current after.current ∧ Grows before after)
      (fun value store => post value store.current) (worker source) ⟨initial, past⟩ := by
  induction safe generalizing past with
  | waiting commit next ih =>
    apply Safe.waiting
    · intro current valid growth
      have checked := commit current.current valid.1 growth.1
      exact ⟨⟨checked.1, valid.2.append refl trans checked.2⟩, checked.2, operation_grows _ _⟩
    · intro current valid growth
      exact ih current.current valid.1 growth.1 current.states
  | responding next ih =>
    apply Safe.responding
    intro current valid growth
    rw [continuation_apply, ← worker_program]
    exact ih current.current valid.1 growth.1 current.past
  | finished done => exact .finished fun current valid growth => done current.current valid.1 growth.1
  | stopped => exact .stopped

private def tracePast {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) : Nat → List δ
  | 0 => []
  | n + 1 => pastAfter (source.events n) (source.states n) (tracePast source n)

/-- Lift any original infinite legal execution. The event sequence is identical
and the projection at every index is the original durable state and workers. -/
def trace {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) :
    Simulation.Trace (fun index => program (start index)) (advance clock) where
  states n := state (tracePast source n) (source.states n)
  events := source.events
  execution n := by
    rw [step_correspondence, source.execution]
    rfl

theorem trace_current {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (n : Nat) :
    ((trace source).states n).durable.current = (source.states n).durable := rfl

private theorem Store.same_states {first second : Store δ} (same : first.states = second.states) : first = second := by
  cases first
  cases second
  simpa only [Store.states, List.cons.injEq, Store.mk.injEq] using same

private theorem trace_update {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (n : Nat) :
    ((trace source).states (n + 1)).durable = ((trace source).states n).durable ∨
    ((trace source).states (n + 1)).durable.past = ((trace source).states n).durable.states := by
  have executed := source.execution n
  cases event : source.events n with
  | commit index | advanceTime elapsed =>
    right
    simp only [trace, state, tracePast, event, pastAfter, Store.states]
  | resume index | crash index | restart index =>
    left
    cases seen : (source.states n).workers index <;>
      simp only [Simulation.step, event, seen] at executed
    all_goals try { cases executed }
    all_goals
      have durable := congrArg State.durable (Except.ok.inj executed)
      simp only [trace, state, tracePast, event, pastAfter]
      exact congrArg (fun current => Store.mk current (tracePast source n)) durable.symm

/-- A physical history starts empty and adds at most the preceding snapshot
at each event. Unchanged events include reply delivery and loop repetition. -/
structure Timeline (logs : Nat → Store δ) : Prop where
  initial : (logs 0).past = []
  update : ∀ n, logs (n + 1) = logs n ∨ (logs (n + 1)).past = (logs n).states

theorem Timeline.grows {logs : Nat → Store δ} (timeline : Timeline logs) (before after : Nat) (later : before ≤ after) :
    Grows (logs before) (logs after) := by
  induction after with
  | zero =>
    have zero : before = 0 := by omega
    subst before
    exact .refl _
  | succ after ih =>
    by_cases equal : before = after + 1
    · subst before; exact .refl _
    apply (ih (by omega)).trans
    rcases timeline.update after with unchanged | appended
    · rw [unchanged]; exact .refl _
    · exact ⟨[(logs (after + 1)).current], by simp only [List.singleton_append, Store.states, appended]⟩

/-- Every checkpoint retained by the proof history was the state at a real
event boundary. It is not merely an abstract snapshot satisfying an invariant. -/
theorem Timeline.checkpoint {logs : Nat → Store δ} (timeline : Timeline logs) (n : Nat) (checkpoint : Store δ)
    (recorded : Grows checkpoint (logs n)) :
    ∃ atTime, atTime ≤ n ∧ (logs atTime) = checkpoint := by
  induction n with
  | zero =>
    have bound := recorded.length
    have empty : checkpoint.past = [] := by simpa only [timeline.initial, List.length_nil, Nat.le_zero, List.length_eq_zero_iff] using bound
    have same := List.IsSuffix.eq_of_length recorded (by simp [Store.states, empty, timeline.initial])
    exact ⟨0, Nat.le_refl _, (Store.same_states same).symm⟩
  | succ n ih =>
    rcases timeline.update n with unchanged | appended
    · rw [unchanged] at recorded
      obtain ⟨atTime, earlier, same⟩ := ih recorded
      exact ⟨atTime, Nat.le_succ_of_le earlier, same⟩
    · change checkpoint.states <:+ _ :: _ at recorded
      rw [appended, List.suffix_cons_iff] at recorded
      rcases recorded with same | earlier
      · exact ⟨n + 1, Nat.le_refl _, (Store.same_states (by simpa only [Store.states, appended] using same)).symm⟩
      · obtain ⟨atTime, before, same⟩ := ih earlier
        exact ⟨atTime, Nat.le_succ_of_le before, same⟩

/-- A checkpoint with a strictly newer history offset occurred after the
specified event boundary, including when pure resume events repeat a snapshot. -/
theorem Timeline.checkpoint_after {logs : Nat → Store δ} (timeline : Timeline logs) (n : Nat) (checkpoint : Store δ)
    (recorded : Grows checkpoint (logs n)) (cut : Nat)
    (newer : (logs cut).past.length < checkpoint.past.length) :
    ∃ atTime, cut < atTime ∧ atTime ≤ n ∧ (logs atTime) = checkpoint := by
  obtain ⟨atTime, earlier, same⟩ := timeline.checkpoint n checkpoint recorded
  refine ⟨atTime, ?_, earlier, same⟩
  apply Nat.lt_of_not_ge
  intro before
  have bound := (timeline.grows atTime cut before).length
  rw [same] at bound
  omega

theorem Timeline.seen {logs : Nat → Store δ} (timeline : Timeline logs) (n : Nat) {predicate : δ → Prop}
    (seen : Seen predicate (logs n)) : ∃ atTime, atTime ≤ n ∧ predicate (logs atTime).current := by
  obtain ⟨checkpoint, recorded, present⟩ := seen.earlier
  obtain ⟨atTime, earlier, same⟩ := timeline.checkpoint n checkpoint recorded
  exact ⟨atTime, earlier, by rwa [same]⟩

theorem trace_timeline {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) : Timeline (fun n => ((trace source).states n).durable) :=
  ⟨rfl, trace_update source⟩

theorem trace_grows {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (before after : Nat) (later : before ≤ after) :
    Grows ((trace source).states before).durable ((trace source).states after).durable :=
  (trace_timeline source).grows before after later

/-- Every checkpoint retained by the proof history was the state at a real
event boundary. It is not merely an abstract snapshot satisfying an invariant. -/
theorem trace_checkpoint {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (n : Nat) (checkpoint : Store δ)
    (recorded : Grows checkpoint ((trace source).states n).durable) :
    ∃ atTime, atTime ≤ n ∧ ((trace source).states atTime).durable = checkpoint :=
  (trace_timeline source).checkpoint n checkpoint recorded

/-- A checkpoint with a strictly newer history offset occurred after the
specified event boundary, including when pure resume events repeat a snapshot. -/
theorem trace_checkpoint_after {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (n : Nat) (checkpoint : Store δ)
    (recorded : Grows checkpoint ((trace source).states n).durable) (cut : Nat)
    (newer : ((trace source).states cut).durable.past.length < checkpoint.past.length) :
    ∃ atTime, cut < atTime ∧ atTime ≤ n ∧ ((trace source).states atTime).durable = checkpoint :=
  (trace_timeline source).checkpoint_after n checkpoint recorded cut newer

/-- Historical evidence of a queue receipt or retained message can be located
in the original execution, even if later acknowledgements removed it. -/
theorem trace_seen {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (n : Nat) {predicate : δ → Prop}
    (seen : Seen predicate ((trace source).states n).durable) :
    ∃ atTime, atTime ≤ n ∧ predicate (source.states atTime).durable :=
  (trace_timeline source).seen n seen

theorem trace_outcome {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (n : Nat) (index : Fin count) :
    (((trace source).states n).workers index).outcome? = ((source.states n).workers index).outcome? :=
  worker_outcome _

theorem trace_fair {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (fair : source.WeaklyFair) : (trace source).WeaklyFair := by
  constructor
  · intro index n enabled
    exact fair.commit index n (fun later after => by simpa only [trace, state, worker_phase] using enabled later after)
  · intro index n enabled
    exact fair.resume index n (fun later after => by simpa only [trace, state, worker_phase] using enabled later after)
  · intro index n enabled
    exact fair.restart index n (fun later after => by simpa only [trace, state, worker_phase] using enabled later after)

theorem trace_noCrashes {start : Fin count → SimM δ α} {clock : Nat → δ → δ}
    (source : Simulation.Trace start clock) (index : Fin count) (cut : Nat)
    (stopped : source.NoCrashesAfter index cut) : (trace source).NoCrashesAfter index cut := stopped

end LeanCloud.Simulation.History
