import LeanCloud.Proofs.SimulationComposition
import LeanCloud.Proofs.SimulationHistory
import LeanCloud.Proofs.LeaseQueue
import LeanCloud.SimulationBackend
import Init.Data.Array.Monadic

/-! Publication before acknowledgement with dynamic consumers. The proof keeps
historical enqueue/write transitions, so a successor need not remain queued.
Every removal has a publication certificate, even if its acknowledgement reply
is lost. Permission to retire the selected command is a separate worker fact. -/

namespace LeanCloud.Proofs.ConcurrentHandoff
open Lean LeanEff Simulation SimulationBackend LeaseQueueModel

abbrev Log := History.Store Durable

def enqueued (location : Location) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.enqueue location state.transport).2 }

def acknowledged (receipt : Receipt) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.acknowledge receipt state.transport).2 }

def completed (outcome : Exit) (state : Durable) : Durable :=
  { state with completed := some outcome }

/-- Every emitted successor was enqueued since the call's starting offset, or
the final result was written. Later consumption does not erase this evidence. -/
def Published (since : Nat) (response : StepResult) (log : Log) : Prop :=
  match response with
  | .runnable locations => ∀ location ∈ locations,
      History.Occurred since (fun before after => after = enqueued location before) log
  | .done outcome => History.Occurred since (fun before after => after = completed outcome before) log

theorem Published.grow {since response before after}
    (published : Published since response before) (growth : History.Grows before after) :
    Published since response after := by
  cases response with
  | runnable locations => exact fun location member => (published location member).grow growth
  | done outcome => exact History.Occurred.grow published growth

/-- The worker supplies the semantic reason for replacing a delivered item.
The transport proof derives prior publication; it does not assume it here. -/
abbrev Permission := Nat → Receipt → StepResult → Log → Prop

def Removal (permit : Permission) (before after : Durable) (past : List Durable) : Prop :=
  ∀ slot message, before.transport.messages[slot]? = some (some message) →
    after.transport.messages[slot]? = some none →
    ∃ since receipt response, receipt.message = slot ∧ after = acknowledged receipt before ∧
      permit since receipt response ⟨before, past⟩ ∧ Published since response ⟨before, past⟩

/-- Certificates cover all durable removals, including those whose replies
have not arrived. The history may contain arbitrary interleaved consumers. -/
def Certified (permit : Permission) : List Durable → Prop
  | after :: before :: past => LeaseQueue.Lineage before.transport after.transport ∧
      Removal permit before after past ∧ Certified permit (before :: past)
  | _ => True

def Valid (permit : Permission) (log : Log) : Prop := Certified permit log.states

theorem Valid.initial (permit : Permission) (state : Durable) : Valid permit ⟨state, []⟩ := trivial

/-- A primitive that cannot create an acknowledgement tombstone. Journal
operations, completion reads, and dequeue satisfy this independently of values. -/
def NoRemoval (action : Durable → α × Durable) : Prop :=
  ∀ (state : Durable) (slot : Nat) (message : Message Location), state.transport.messages[slot]? = some (some message) →
    (action state).2.transport.messages[slot]? ≠ some none

theorem NoRemoval.preserves {action : Durable → α × Durable} (framed : NoRemoval action)
    (lineage : ∀ state, LeaseQueue.Lineage state.transport (action state).2.transport)
    (permit : Permission) (initial : Log) (valid : Valid permit initial) :
    Valid permit (History.operation action initial).2 :=
  ⟨lineage initial.current,
    fun slot message stored removed => False.elim (framed initial.current slot message stored removed), valid⟩

private theorem poll_noRemoval (duration : Nat) : NoRemoval (fun state : Durable =>
    ((LeaseQueueModel.dequeue duration state.transport).1,
      { state with transport := (LeaseQueueModel.dequeue duration state.transport).2 })) := by
  intro state slot message stored
  change (LeaseQueueModel.dequeue duration state.transport).2.messages[slot]? ≠ some none
  unfold LeaseQueueModel.dequeue
  split
  · simp [stored]
  · rename_i selected found
    split
    · rename_i old occupied
      by_cases same : selected = slot
      · subst slot
        have inside := (Array.getElem?_eq_some_iff.mp occupied).choose
        simp [inside]
      · simp [same, stored]
    · simp [stored]

/-- The receipt and payload matched a real retained message at the dequeue
commit. Its lease may be stale by the time this evidence is used. -/
def Received (location : Location) (receipt : Receipt) (log : Log) : Prop :=
  History.Seen (fun state => ∃ message,
    LeaseQueueModel.current receipt state.transport = some message ∧ message.value = location) log

def Polled (returned : Work × SimulationBackend.Worker) (log : Log) : Prop :=
  match returned.1 with
  | .item location => ∃ receipt, returned.2.delivery = some (location, receipt) ∧ Received location receipt log
  | _ => True

theorem Polled.grow {returned before after} (polled : Polled returned before) (growth : History.Grows before after) :
    Polled returned after := by
  rcases returned with ⟨work, worker⟩
  cases work with
  | completed _ | idle => trivial
  | item location =>
    obtain ⟨receipt, held, received⟩ := polled
    exact ⟨receipt, held, received.grow growth⟩

/-- Polling never removes a message, and its returned receipt has a historical
payload witness. A delayed response does not assert that the lease is current. -/
theorem next_safe (permit : Permission) (duration : Nat) (worker : SimulationBackend.Worker) (initial : Log) :
    Safe (Valid permit) History.Grows Polled
      (.ofProgram (History.program ((queue duration).next.run worker))) initial := by
  dsimp [queue, LeanCloud.LeaseQueue.toWorkQueue, LeanCloud.LeaseQueue.liftBackend,
    readCompleted, transport, StateT.run, StateT.bind, StateT.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, SimM.atomic, EffF.send, bind, pure,
    EffF.bind, History.program, History.continuation, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current kept growth
    exact ⟨⟨.refl _, fun slot message stored removed => by simp [History.operation, stored] at removed, kept⟩,
      History.operation_grows _ _⟩
  · intro observed kept growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, History.operation]
    cases completed : observed.current.completed with
    | some outcome =>
      exact .finished fun _ _ _ => trivial
    | none =>
      apply Safe.waiting
      · intro current valid growth
        exact ⟨(poll_noRemoval duration).preserves (fun state => .dequeue state.transport duration)
          permit current valid, History.operation_grows _ _⟩
      · intro polled valid growth
        apply Safe.responding
        intro received receivedValid extended
        simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
          History.program, History.continuation, History.operation]
        cases selected : (LeaseQueueModel.dequeue duration polled.current.transport).1 with
        | none =>
          simp only [Option.map_none, pure, StateT.pure, ArrsF.apply, ArrsF.viewL,
            History.program, Simulation.Worker.ofProgram]
          exact .finished fun _ _ _ => trivial
        | some delivery =>
          simp only [Option.map_some, pure, bind, StateT.bind, StateT.pure, StateT.modifyGet,
            EffF.bind, ArrsF.apply, ArrsF.viewL, History.program, Simulation.Worker.ofProgram]
          apply Safe.finished
          intro final finalValid last
          refine ⟨delivery.receipt, rfl, ?_⟩
          apply History.Seen.grow (growth := extended.trans last)
          apply History.Seen.now
          obtain ⟨message, held, value, _⟩ := LeaseQueue.dequeue_retains
            (show LeaseQueueModel.dequeue duration polled.current.transport =
              (some delivery, (LeaseQueueModel.dequeue duration polled.current.transport).2) from
              Prod.ext selected rfl)
          exact ⟨message, held, value⟩

/-- Even an idle poll commits a read. Extra interference can increase this
count further, but a loop iteration cannot consume fuel without a boundary. -/
theorem next_advances (permit : Permission) (duration : Nat) (worker : SimulationBackend.Worker) (initial : Log) :
    Safe (Valid permit) History.Grows
      (fun returned final => Polled returned final ∧ initial.past.length < final.past.length)
      (.ofProgram (History.program ((queue duration).next.run worker))) initial := by
  apply Safe.after_commit (next_safe permit duration worker initial) History.Grows.refl (fun a b => a.trans b)
  · intro current kept growth
    change initial.past.length < current.past.length + 1
    have prior := growth.length
    omega
  · intro before after progress growth
    exact Nat.lt_of_lt_of_le progress growth.length

private theorem removal_enqueue (permit : Permission) (location : Location) (state : Durable) (past : List Durable) :
    Removal permit state (enqueued location state) past := by
  intro slot message stored removed
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  have same : (enqueued location state).transport.messages[slot]? = some (some message) := by
    simpa [enqueued, LeaseQueueModel.enqueue, Array.getElem?_push, inside, Nat.ne_of_lt inside] using stored
  simp [same] at removed

private theorem removal_done (permit : Permission) (outcome : Exit) (state : Durable) (past : List Durable) :
    Removal permit state (completed outcome state) past := by
  intro slot message stored removed
  change state.transport.messages[slot]? = some none at removed
  simp [stored] at removed

private theorem removal_ack {permit : Permission} {since receipt response state past}
    (permitted : permit since receipt response ⟨state, past⟩)
    (published : Published since response ⟨state, past⟩) :
    Removal permit state (acknowledged receipt state) past := by
  intro slot message stored removed
  by_cases same : receipt.message = slot
  · exact ⟨since, receipt, response, same, rfl, permitted, published⟩
  · change (LeaseQueueModel.acknowledge receipt state.transport).2.messages[slot]? = some none at removed
    rw [LeaseQueue.acknowledge_preserves_other receipt state.transport slot same, stored] at removed
    cases removed

private theorem atomic_safe (permit : Permission) (action : Durable → α × Durable)
    (worker : SimulationBackend.Worker) (initial : Log) (post : α → Log → Prop)
    (stable : ∀ value before after, History.Grows before after → post value before → post value after)
    (commit : ∀ current, Valid permit current → History.Grows initial current →
      Valid permit (History.operation action current).2 ∧
        post (action current.current).1 (History.operation action current).2) :
    Safe (Valid permit) History.Grows
      (fun returned final => returned.2 = worker ∧ post returned.1 final)
      (.ofProgram (History.program ((LeanCloud.LeaseQueue.liftBackend (fun handle : Unit => do
        let value ← SimM.atomic action
        pure (value, handle))).run worker))) initial := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, StateT.run, SimM.atomic, EffF.send, bind, pure,
    EffF.bind, History.program, History.continuation, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨(commit current valid growth).1, History.operation_grows _ _⟩
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind,
      Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    exact ⟨by cases worker with | mk backend delivery => cases backend; rfl,
      stable _ _ _ (later.trans last) (commit committed valid growth).2⟩

private theorem state_bind {permit : Permission}
    {action : StateT SimulationBackend.Worker M α} {next : α → StateT SimulationBackend.Worker M β}
    {first : (α × SimulationBackend.Worker) → Log → Prop}
    {post : (β × SimulationBackend.Worker) → Log → Prop} {worker : SimulationBackend.Worker} {initial : Log}
    (safe : Safe (Valid permit) History.Grows first (.ofProgram (History.program (action.run worker))) initial)
    (valid : Valid permit initial)
    (resume : ∀ returned current, Valid permit current → History.Grows initial current → first returned current →
      Safe (Valid permit) History.Grows post
        (.ofProgram (History.program ((next returned.1).run returned.2))) current) :
    Safe (Valid permit) History.Grows post (.ofProgram (History.program ((action >>= next).run worker))) initial := by
  change Safe _ _ _ (.ofProgram (History.program (action.run worker >>= fun pair => (next pair.1).run pair.2))) initial
  rw [History.program_bind]
  apply Safe.bind History.Grows.refl (fun a b => a.trans b)
    (safe.remember (fun a b => a.trans b) initial (.refl _)) valid
  intro returned current kept h
  exact resume returned current kept h.1 h.2

private theorem enqueue_safe (permit : Permission) (duration since : Nat) (location : Location)
    (worker : SimulationBackend.Worker) (initial : Log) (bound : since ≤ initial.past.length) :
    Safe (Valid permit) History.Grows
      (fun returned final => returned = ((), worker) ∧ Published since (.runnable #[location]) final)
      (.ofProgram (History.program ((LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)).run worker))) initial := by
  have safe := atomic_safe permit (fun state => ((), enqueued location state)) worker initial
    (fun _ final => Published since (.runnable #[location]) final)
    (fun _ _ _ growth published => published.grow growth) (by
      intro current valid growth
      refine ⟨⟨.enqueue _ _, removal_enqueue permit location current.current current.past, valid⟩, ?_⟩
      intro item member
      have same : item = location := by simpa using member
      subst item
      exact History.operation_occurred _ current since (Nat.le_trans bound growth.length) _ rfl)
  apply safe.weaken
  intro returned final valid h
  rcases returned with ⟨value, handle⟩
  cases value
  exact ⟨by simp only [Prod.mk.injEq, true_and]; exact h.1, h.2⟩

private theorem done_safe (permit : Permission) (since : Nat) (outcome : Exit)
    (worker : SimulationBackend.Worker) (initial : Log) (bound : since ≤ initial.past.length) :
    Safe (Valid permit) History.Grows
      (fun returned final => returned = ((), worker) ∧ Published since (.done outcome) final)
      (.ofProgram (History.program ((LeanCloud.LeaseQueue.liftBackend (writeCompleted outcome)).run worker))) initial := by
  have safe := atomic_safe permit (fun state => ((), completed outcome state)) worker initial
    (fun _ final => Published since (.done outcome) final)
    (fun _ _ _ growth published => published.grow growth) (by
      intro current valid growth
      exact ⟨⟨.refl _, removal_done permit outcome current.current current.past, valid⟩,
        History.operation_occurred _ current since (Nat.le_trans bound growth.length) _ rfl⟩)
  apply safe.weaken
  intro returned final valid h
  rcases returned with ⟨value, handle⟩
  cases value
  exact ⟨by simp only [Prod.mk.injEq, true_and]; exact h.1, h.2⟩

private theorem ack_safe {permit : Permission}
    (stable : ∀ since receipt response before after, History.Grows before after →
      permit since receipt response before → permit since receipt response after)
    (duration since : Nat) (receipt : Receipt) (response : StepResult)
    (worker : SimulationBackend.Worker) (initial : Log)
    (permitted : permit since receipt response initial) (published : Published since response initial) :
    Safe (Valid permit) History.Grows
      (fun returned final => returned.2 = worker ∧ Published since response final)
      (.ofProgram (History.program ((LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge receipt)).run worker))) initial := by
  apply atomic_safe permit (fun state =>
    ((LeaseQueueModel.acknowledge receipt state.transport).1, acknowledged receipt state)) worker initial
    (fun _ final => Published since response final) (fun _ _ _ growth published => published.grow growth)
  intro current valid growth
  exact ⟨⟨.acknowledge _ _, removal_ack (stable _ _ _ _ _ growth permitted) (published.grow growth), valid⟩,
    published.grow (growth.trans (History.operation_grows _ _))⟩

private abbrev enqueueBody (duration : Nat) (location : Location) (_ : PUnit.{1}) :
    StateT SimulationBackend.Worker M (ForInStep PUnit.{1}) := do
  LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)
  pure (.yield PUnit.unit)

private theorem enqueue_list_safe (permit : Permission) (duration since : Nat) (locations : List Location)
    (worker : SimulationBackend.Worker) (initial : Log) (valid : Valid permit initial)
    (bound : since ≤ initial.past.length) :
    Safe (Valid permit) History.Grows
      (fun returned final => returned = (PUnit.unit, worker) ∧ Published since (.runnable locations.toArray) final)
      (.ofProgram (History.program ((forIn locations PUnit.unit (enqueueBody duration)).run worker))) initial := by
  induction locations generalizing worker initial with
  | nil => exact .finished fun _ _ _ => ⟨rfl, by simp [Published]⟩
  | cons location rest ih =>
    rw [List.forIn_cons]
    have first : Safe (Valid permit) History.Grows
        (fun returned final => returned = (.yield PUnit.unit, worker) ∧ Published since (.runnable #[location]) final)
        (.ofProgram (History.program ((enqueueBody duration location PUnit.unit).run worker))) initial := by
      unfold enqueueBody
      apply state_bind (enqueue_safe permit duration since location worker initial bound) valid
      intro returned current kept growth h
      obtain ⟨rfl, published⟩ := h
      exact .finished fun final _ later => ⟨rfl, published.grow later⟩
    apply state_bind first valid
    intro returned current kept growth h
    obtain ⟨rfl, head⟩ := h
    apply Safe.weaken ((ih worker current kept (Nat.le_trans bound growth.length)).remember
      (fun a b => a.trans b) current (.refl _))
    intro returned final finalValid h
    obtain ⟨later, rfl, tail⟩ := h
    refine ⟨rfl, ?_⟩
    intro item member
    have alternatives : item = location ∨ item ∈ rest := by simpa using member
    rcases alternatives with rfl | member
    · exact (head.grow later) item (by simp)
    · exact tail item (by simpa using member)

/-- The actual completion adapter certifies every removal at its commit,
before its reply is delivered. All successors (or the final outcome) have been
published since this invocation began. They may already have been consumed;
overlapping attempts need not agree on their response arrays. -/
theorem complete_safe {permit : Permission}
    (stable : ∀ since receipt response before after, History.Grows before after →
      permit since receipt response before → permit since receipt response after)
    (duration : Nat) (location : Location) (receipt : Receipt) (response : StepResult)
    (initial : Log) (valid : Valid permit initial)
    (permitted : permit initial.past.length receipt response initial) :
    Safe (Valid permit) History.Grows
      (fun returned final => returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
        Published initial.past.length response final)
      (.ofProgram (History.program (((queue duration).complete location response).run
        ⟨(), some (location, receipt)⟩))) initial := by
  let worker : SimulationBackend.Worker := ⟨(), some (location, receipt)⟩
  have acknowledge (current : Log) (kept : Valid permit current) (growth : History.Grows initial current)
      (published : Published initial.past.length response current) :
      Safe (Valid permit) History.Grows
        (fun returned final => returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
          Published initial.past.length response final)
        (.ofProgram (History.program ((do
          let _ ← LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge receipt)
          modify fun worker : SimulationBackend.Worker => { worker with delivery := none }).run worker))) current := by
    apply state_bind (ack_safe stable duration initial.past.length receipt response worker current
      (stable _ _ _ _ _ growth permitted) published) kept
    intro returned delivered deliveredValid later h
    obtain ⟨same, published⟩ := h
    rcases returned with ⟨accepted, handle⟩
    dsimp only at same
    subst handle
    exact .finished fun _ _ last => ⟨rfl, published.grow last⟩
  dsimp [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run, StateT.bind, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, bind, pure, EffF.bind]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change Safe _ _ _ (.ofProgram (History.program ((do
    match response with
    | .runnable locations => for next in locations do
        LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue next)
    | .done result => LeanCloud.LeaseQueue.liftBackend (writeCompleted result)
    let _ ← LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge receipt)
    modify fun worker : SimulationBackend.Worker => { worker with delivery := none }).run worker))) initial
  cases response with
  | done outcome =>
    apply state_bind (done_safe permit initial.past.length outcome worker initial (Nat.le_refl _)) valid
    intro returned current kept growth h
    obtain ⟨rfl, published⟩ := h
    exact acknowledge current kept growth published
  | runnable locations =>
    dsimp only
    rw [← Array.forIn_toList]
    apply state_bind (enqueue_list_safe permit duration initial.past.length locations.toList worker initial valid (Nat.le_refl _)) valid
    intro returned current kept growth h
    obtain ⟨rfl, published⟩ := h
    exact acknowledge current kept growth (by simpa only [Array.toArray_toList] using published)

private theorem Certified.suffix {permit : Permission} (newer older : List Durable) :
    Certified permit (newer ++ older) → Certified permit older := by
  induction newer with
  | nil => exact id
  | cons head rest ih =>
    intro certified
    apply ih
    cases seen : rest ++ older with
    | nil => trivial
    | cons next remaining =>
      simp only [List.cons_append, seen, Certified] at certified
      exact certified.2.2

theorem Valid.earlier {permit : Permission} {before after : Log}
    (valid : Valid permit after) (growth : History.Grows before after) : Valid permit before := by
  obtain ⟨newer, same⟩ := growth
  exact Certified.suffix newer before.states (by rw [same]; exact valid)

/-- Extract a removal's certificate from any historical transition, including
an acknowledgement committed just before a crash. -/
theorem Valid.removal {permit : Permission} {log : Log} (valid : Valid permit log)
    {before after : Durable} {past : List Durable}
    (recorded : after :: before :: past <:+ log.states) : Removal permit before after past :=
  (valid.earlier (before := ⟨after, before :: past⟩) recorded).2.1

/-- Every historical interval preserves slot identity, even across immediate
consumption and redelivery by other workers. -/
theorem Valid.lineage {permit : Permission} {before after : Log}
    (valid : Valid permit after) (growth : History.Grows before after) :
    LeaseQueue.Lineage before.current.transport after.current.transport := by
  obtain ⟨newer, same⟩ := growth
  have chain (newer : List Durable) (current : Durable)
      (certified : Certified permit (newer ++ before.states))
      (head : (newer ++ before.states).head? = some current) :
      LeaseQueue.Lineage before.current.transport current.transport := by
    induction newer generalizing current with
    | nil => cases head; exact .refl _
    | cons latest rest ih =>
      cases head
      cases rest with
      | nil => exact certified.1
      | cons intermediate rest => exact (ih intermediate certified.2.2 rfl).trans certified.1
  exact chain newer after.current (by rw [same]; exact valid) (by rw [same]; rfl)

/-- A stale receipt still identifies its original payload. Acknowledgement
permission cannot be transferred to unrelated work that reused the slot. -/
theorem Received.payload {permit : Permission} {location receipt log message}
    (valid : Valid permit log) (received : Received location receipt log)
    (stored : log.current.transport.messages[receipt.message]? = some (some message)) : message.value = location := by
  obtain ⟨earlier, growth, delivered, held, value⟩ := History.Seen.earlier received
  have occupied := (LeaseQueue.current_iff.mp held).1
  have inside := (Array.getElem?_eq_some_iff.mp occupied).choose
  obtain ⟨previous, prior, same⟩ := (valid.lineage growth).retained receipt.message message inside stored
  rw [occupied] at prior
  cases prior
  exact same.symm.trans value

theorem Received.inside {permit : Permission} {location receipt log}
    (valid : Valid permit log) (received : Received location receipt log) :
    receipt.message < log.current.transport.messages.size := by
  obtain ⟨earlier, growth, message, held, _⟩ := History.Seen.earlier received
  have inside := (Array.getElem?_eq_some_iff.mp (LeaseQueue.current_iff.mp held).1).choose
  exact Nat.lt_of_lt_of_le inside (valid.lineage growth).size

/-- Each successor was appended after the response was computed. Its slot is
newer than every slot already allocated at that checkpoint, even if another
worker has since consumed it. -/
theorem Published.fresh {permit : Permission} {before after : Log} {locations : Array Location}
    (valid : Valid permit after) (growth : History.Grows before after)
    (published : Published before.past.length (.runnable locations) after)
    {location : Location} (member : location ∈ locations) :
    ∃ slot issued message, before.current.transport.messages.size ≤ slot ∧
      History.Grows before issued ∧ History.Grows issued after ∧
      issued.current.transport.messages[slot]? = some (some message) ∧ message.value = location ∧
      before.past.length < issued.past.length := by
  obtain ⟨previous, next, past, offset, enqueued, recorded⟩ := published location member
  have prior : History.Grows (⟨previous, past⟩ : Log) after :=
    List.IsSuffix.trans ⟨[next], rfl⟩ recorded
  have started := growth.between prior offset
  let issued : Log := ⟨next, previous :: past⟩
  have committed : History.Grows (⟨previous, past⟩ : Log) issued := ⟨[next], rfl⟩
  refine ⟨previous.transport.messages.size, issued, ⟨location, 0, previous.transport.now⟩,
    ((valid.earlier prior).lineage started).size, started.trans committed, recorded, ?_, rfl, ?_⟩
  · change next.transport.messages[previous.transport.messages.size]? = _
    rw [enqueued]
    simp [ConcurrentHandoff.enqueued, LeaseQueueModel.enqueue]
  · exact Nat.lt_succ_of_le offset

/-- A published slot either remains recoverable, including while leased, or
its history contains an actual acknowledgement transition. In the latter case
`Valid.removal` supplies the step/publication certificate for that transition. -/
theorem Valid.retained_or_removed {permit : Permission} {before after : Log}
    (valid : Valid permit after) (growth : History.Grows before after)
    {slot : Nat} {message : Message Location}
    (stored : before.current.transport.messages[slot]? = some (some message)) :
    (∃ current, after.current.transport.messages[slot]? = some (some current) ∧ current.value = message.value) ∨
      History.Occurred 0 (fun previous next =>
        (∃ current, previous.transport.messages[slot]? = some (some current) ∧ current.value = message.value) ∧
        next.transport.messages[slot]? = some none) after := by
  obtain ⟨newer, same⟩ := growth
  induction newer generalizing after with
  | nil =>
    have head := congrArg List.head? same
    have equal : before.current = after.current := Option.some.inj head
    exact .inl ⟨message, by rw [← equal]; exact stored, rfl⟩
  | cons latest rest ih =>
    cases after with
    | mk current past =>
      change latest :: (rest ++ before.states) = current :: past at same
      cases same
      cases middle : rest ++ before.states with
      | nil =>
        have length := congrArg List.length middle
        simp [History.Store.states] at length
      | cons previous past =>
        rw [middle] at valid
        have prior := ih (after := ⟨previous, past⟩) valid.2.2 middle
        rcases prior with ⟨retained, held, value⟩ | removed
        · rcases valid.1.live_or_removed held with ⟨present, held, same⟩ | removed
          · exact .inl ⟨present, held, same.trans value⟩
          · exact .inr ⟨previous, latest, past, Nat.zero_le _, ⟨⟨retained, held, value⟩, removed⟩, List.suffix_rfl⟩
        · exact .inr (removed.grow ⟨[latest], rfl⟩)

end LeanCloud.Proofs.ConcurrentHandoff
