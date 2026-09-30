import LeanCloud.Proofs.ConcurrentJoin
import LeanCloud.Proofs.SimulationComposition

/-! Safety of the complete child-publication path, composing the actual
interpreter's reads and writes under compatible concurrent journal extensions. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean LeanEff Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery
open ReplayInterpreter.Internal

private abbrev Action (α : Type) := ExceptT CloudError (StateT Unit M) α
private abbrev workerDb := JournalDb.ofDb rawDb

/-- Successful execution of a worker action, with its durable postcondition. -/
def Checked (expected : Journal) (action : Action α) (post : α → Durable → Prop)
    (state : Durable) : Prop :=
  Safe (Valid expected) Grows
    (fun returned final => ∃ value, returned = (.ok value, ()) ∧ post value final)
    (.ofProgram (action.run ())) state

theorem checked_pure {expected : Journal} (value : α) (post : α → Durable → Prop)
    (state : Durable) (done : ∀ final, Valid expected final → Grows state final → post value final) :
    Checked expected (pure value) post state :=
  .finished fun final kept growth => ⟨value, rfl, done final kept growth⟩

theorem checked_bind {expected : Journal} {action : Action α} {next : α → Action β}
    {first : α → Durable → Prop} {post : β → Durable → Prop} {state : Durable}
    (safe : Checked expected action first state) (kept : Valid expected state)
    (resume : ∀ value current, Valid expected current → Grows state current → first value current →
      Checked expected (next value) post current) :
    Checked expected (action >>= next) post state := by
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    (safe.remember (fun a b => a.trans b) state (.refl _)) kept
  intro returned current valid h
  obtain ⟨growth, value, rfl, done⟩ := h
  exact resume value current valid growth done

theorem Checked.weaken {expected : Journal} {action : Action α}
    {first post : α → Durable → Prop} {state : Durable}
    (safe : Checked expected action first state)
    (implies : ∀ value final, first value final → post value final) :
    Checked expected action post state := by
  apply Safe.weaken safe
  intro returned final valid h
  obtain ⟨value, rfl, done⟩ := h
  exact ⟨value, rfl, implies value final done⟩

/-- Cache/child agreement is a property of the prescribed physical records.
It is not an assumption that a worker call succeeds. -/
def Coherent (expected : Journal) (key : String) : Prop :=
  ∀ slots outcome, JournalAdapter.Published (records key (.suspended slots)) expected →
    Result.settle slots = .completed outcome → expected (resultKey key) = some (toJson outcome)

private theorem slots_published {key : String} {before after : Durable}
    {slots : Array (Option Exit)}
    (descriptor : view after (forkKey key) = some (toJson slots.size))
    (seen : Slots key before after (List.range slots.size) slots.toList) :
    JournalAdapter.Published (records key (.suspended slots)) (view after) := by
  apply published_suspended key slots (view after) descriptor
  intro index inside outcome present
  have observed : Slot key before after index slots[index]! := by
    simpa [inside] using seen.at index (by simpa using inside)
  simpa [Slot, present] using observed

theorem completed_intended {expected : Journal} {state : Durable} {key : String} {outcome : Exit}
    (coherent : Coherent expected key) (kept : Valid expected state)
    (completed : CompletedAt (view state) key outcome) :
    expected (resultKey key) = some (toJson outcome) := by
  cases completed with
  | cached stored => exact kept _ _ stored
  | group slots fork filled settled =>
    apply coherent slots outcome ?_ settled
    apply published_suspended _ _ _ (kept _ _ fork)
    intro index inside value present
    obtain ⟨actual, same, stored⟩ := filled index inside
    rw [present] at same
    cases same
    exact kept _ _ stored

/-- The typed information an actual journal read can establish. -/
inductive ReadResult (key : String) (before after : Durable) : Option Result → Prop where
  | missing : view before (resultKey key) = none → view before (forkKey key) = none →
      ReadResult key before after none
  | completed (outcome : Exit) : CompletedAt (view after) key outcome →
      ReadResult key before after (some (.completed outcome))
  | suspended (slots : Array (Option Exit)) :
      JournalAdapter.Published (records key (.suspended slots)) (view after) →
      (∀ outcome, ¬ CompletedAt (view before) key outcome) →
      Result.settle slots = .suspended slots →
      ReadResult key before after (some (.suspended slots))

private theorem observation_result {expected : Journal} {key : String} {before after : Durable}
    (coherent : Coherent expected key) (lower : Valid expected before) (upper : Valid expected after)
    {answer : Option Json} (seen : Observation key before after answer) :
    ∃ result, answer = result.map toJson ∧ ReadResult key before after result := by
  have notCompleted (slots : Array (Option Exit))
      (encoded : answer = some (toJson (Result.suspended slots))) :
      ∀ outcome, ¬ CompletedAt (view before) key outcome := by
    intro outcome ready
    have same := seen.completed ready lower upper (completed_intended coherent lower ready)
    rw [encoded] at same
    have impossible := toJson_injective result_roundtrip (Option.some.inj same)
    cases impossible
  cases seen with
  | missing result fork => exact ⟨none, rfl, .missing result fork⟩
  | cached outcome stored => exact ⟨some (.completed outcome), rfl, .completed outcome (.cached stored)⟩
  | fork slots uncached descriptor observed =>
    have published := slots_published descriptor observed
    cases settled : Result.settle slots with
    | completed outcome =>
      exact ⟨some (.completed outcome), rfl, .completed outcome
        (Publication.completed ⟨rfl, published⟩ settled)⟩
    | suspended remaining =>
      have same := Result.settle_suspended settled
      subst remaining
      exact ⟨some (.suspended slots), rfl, .suspended slots published (notCompleted slots (by rw [settled])) settled⟩

private theorem lift_checked {expected : Journal} {action : StateT Unit M α}
    {post : α → Durable → Prop} {state : Durable}
    (safe : Safe (Valid expected) Grows (fun returned final => post returned.1 final)
      (.ofProgram (action.run ())) state) (kept : Valid expected state)
    (stable : ∀ value before after, Grows before after → post value before → post value after) :
    Checked expected (monadLift action) post state := by
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    (safe.remember (fun a b => a.trans b) state (.refl _)) kept
  intro returned current valid h
  rcases returned with ⟨value, ⟨⟩⟩
  exact .finished fun final finalValid later => ⟨value, rfl, stable value current final later h.2⟩

theorem load_checked (expected : Journal) (location : Location)
    (format : Readable expected location.key) (coherent : Coherent expected location.key)
    (state : Durable) (kept : Valid expected state) :
    Checked expected (load workerDb location) (fun result final => ReadResult location.key state final result) state := by
  have lifted := lift_checked (post := fun answer final => Observation location.key state final answer)
    (get_safe expected location.key format state state (.refl _)) kept (by
      intro value before after growth observed
      cases observed with
      | missing result fork => exact .missing result fork
      | cached outcome stored => exact .cached outcome (growth _ _ stored)
      | fork children uncached descriptor slots =>
        exact .fork children uncached (growth _ _ descriptor) (slots.later growth))
  unfold load
  apply checked_bind lifted kept
  intro answer current valid growth observation
  obtain ⟨result, rfl, seen⟩ := observation_result coherent kept valid observation
  cases result with
  | none =>
    apply checked_pure
    intro final finalValid later
    cases seen with
    | missing absent fork => exact .missing absent fork
  | some result =>
    simp only [Option.map_some, result_roundtrip]
    apply checked_pure
    intro final finalValid later
    cases seen with
    | completed outcome completed => exact .completed outcome (completed.grow later.1)
    | suspended slots published incomplete settled =>
      exact .suspended slots (fun entry member => later _ _ (published entry member)) incomplete settled

theorem save_checked (expected : Journal) (location : Location) (result : Result)
    (agrees : Agrees (records location.key result) expected)
    (state : Durable) (kept : Valid expected state) :
    Checked expected (save workerDb location result)
      (fun _ final => JournalAdapter.Published (records location.key result) (view final)) state := by
  have published := (put_safe expected location.key result agrees state).weaken
    (fun returned current => returned.1 = true ∧
      JournalAdapter.Published (records location.key result) (view current)) (by
      intro returned current valid h
      exact ⟨congrArg Prod.fst h.1, h.2⟩)
  have lifted := lift_checked (post := fun accepted current => accepted = true ∧
    JournalAdapter.Published (records location.key result) (view current)) published kept (by
    intro value before after growth h
    exact ⟨h.1, fun entry member => growth _ _ (h.2 entry member)⟩)
  unfold save
  apply checked_bind lifted kept
  intro accepted current valid growth h
  obtain ⟨rfl, published⟩ := h
  simp only [↓reduceIte]
  apply checked_pure
  intro final finalValid later
  exact fun entry member => later _ _ (published entry member)

/-- A wakeup has durable evidence. An empty response has a published child slot
and a reread that started while the group was still incomplete. -/
inductive Notification (parent : Location) (index : Nat) (outcome : Exit)
    (before after : Durable) : StepResult → Prop where
  | wake (result : Exit) (completed : CompletedAt (view after) parent.key result) :
      Notification parent index outcome before after (.runnable #[parent])
  | waiting (checked : Durable) (started : Grows before checked) (finished : Grows checked after)
      (child : view checked (childKey parent.key index) = some (toJson outcome))
      (incomplete : ∀ result, ¬ CompletedAt (view checked) parent.key result) :
      Notification parent index outcome before after (.runnable #[])

theorem Notification.grow {parent index outcome before after response}
    (notified : Notification parent index outcome before after response)
    {initial final : Durable} (earlier : Grows initial before) (later : Grows after final) :
    Notification parent index outcome initial final response := by
  cases notified with
  | wake result completed => exact .wake result (completed.grow later.1)
  | waiting checked started finished child incomplete =>
    exact .waiting checked (earlier.trans started) (finished.trans later) child incomplete

private theorem reread_checked (expected : Journal) (parent : Location) (index : Nat) (outcome : Exit)
    (format : Readable expected parent.key) (coherent : Coherent expected parent.key)
    (state : Durable) (kept : Valid expected state) (count : Nat)
    (fork : view state (forkKey parent.key) = some (toJson count))
    (child : view state (childKey parent.key index) = some (toJson outcome)) :
    Checked expected (do
      let some latest ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
      return joinResponse parent latest)
      (fun response final => Notification parent index outcome state final response) state := by
  apply checked_bind (load_checked expected parent format coherent state kept) kept
  intro result current valid growth seen
  cases seen with
  | missing absent noFork => simp [fork] at noFork
  | completed result completed =>
    apply checked_pure
    intro final finalValid later
    exact .wake result (completed.grow later.1)
  | suspended slots published incomplete settled =>
    apply checked_pure
    intro final finalValid later
    exact .waiting state (.refl _) (growth.trans later) child incomplete

private theorem update_slots {expected : Journal} {parent : Location} {index : Nat} {outcome : Exit}
    {slots : Array (Option Exit)} (inside : index < slots.size)
    (prescribed : expected (childKey parent.key index) = some (toJson outcome))
    (published : JournalAdapter.Published (records parent.key (.suspended slots)) expected)
    (sameExit : (outcome == outcome) = true) :
    Result.recordChild (.suspended slots) index outcome = .ok (Result.settle (slots.set! index (some outcome))) ∧
    JournalAdapter.Published (records parent.key (.suspended (slots.set! index (some outcome)))) expected := by
  obtain ⟨fork, children⟩ := published_fork published
  constructor
  · cases slot : slots[index]! with
    | none => exact Result.recordChild_missing slots index outcome inside slot
    | some actual =>
      have same : actual = outcome := toJson_injective exit_roundtrip
        (Option.some.inj ((children index inside actual slot).symm.trans prescribed))
      subst actual
      have unchanged : slots.set! index (some outcome) = slots := by
        have stored : slots[index] = some outcome := by simpa only [getElem!_pos slots index inside] using slot
        simp [Array.set!, Array.setIfInBounds_def, inside, ← stored]
      rw [unchanged]
      exact Result.recordChild_existing slots index outcome inside slot sameExit
  · apply published_suspended
    · simpa using fork
    · intro i bound value slot
      have inSlots : i < slots.size := by simpa using bound
      by_cases same : i = index
      · subst i
        rw [Array.getElem!_set!_self _ _ _ inside] at slot
        cases slot
        exact prescribed
      · have unchanged : (slots.set! index (some outcome))[i]! = slots[i]! := by
          simp [getElem!_pos, inSlots, Ne.symm same]
        exact children i inSlots value (unchanged.symm.trans slot)

private theorem notify_checked (expected : Journal) (parent : Location) (index : Nat) (outcome : Exit)
    (format : Readable expected parent.key) (coherent : Coherent expected parent.key)
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true)
    (prescribed : expected (childKey parent.key index) = some (toJson outcome))
    (count : Nat) (inside : index < count) (state : Durable) (kept : Valid expected state)
    (fork : view state (forkKey parent.key) = some (toJson count)) :
    Checked expected (do
      let some group ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
      match group with
      | .completed _ => return .runnable #[parent]
      | .suspended children =>
        let updated ← match Result.recordChild group index outcome with
          | .ok result => pure result
          | .error error => throw error
        save workerDb parent (.suspended (children.set! index (some outcome)))
        if let .completed _ := updated then save workerDb parent updated
        let some latest ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
        return joinResponse parent latest)
      (fun response final => Notification parent index outcome state final response) state := by
  apply checked_bind (load_checked expected parent format coherent state kept) kept
  intro result current valid growth observed
  cases observed with
  | missing absent noFork => simp [fork] at noFork
  | completed result completed =>
    apply checked_pure
    intro final finalValid later
    exact .wake result (completed.grow later.1)
  | suspended slots published incomplete settled =>
    have bounded : JournalAdapter.Published (records parent.key (.suspended slots)) expected :=
      fun entry member => valid _ _ (published entry member)
    have size : slots.size = count := toJson_injective (α := Nat) (fun _ => rfl)
      (Option.some.inj ((valid _ _ (published_fork published).1).symm.trans (kept _ _ fork)))
    have inSlots : index < slots.size := by omega
    obtain ⟨recorded, updated⟩ := update_slots inSlots prescribed bounded sameExit
    simp only [recorded]
    apply checked_bind (checked_pure _ (fun value _ => value = Result.settle (slots.set! index (some outcome))) current (fun _ _ _ => rfl)) valid
    intro selected selectedAt selectedValid selectedGrowth selectedValue
    subst selected
    apply checked_bind (save_checked expected parent _ (agrees_of_published updated comparable) selectedAt selectedValid) selectedValid
    intro ignored publishedAt publishedValid publishedGrowth durable
    have child := (published_fork durable).2 index (by simpa using inSlots) outcome
      (Array.getElem!_set!_self _ _ _ inSlots)
    have prior : Grows state publishedAt := (growth.trans selectedGrowth).trans publishedGrowth
    have reread (ready : Durable) (readyValid : Valid expected ready) (later : Grows publishedAt ready) :
        Checked expected (do
          let some latest ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
          return joinResponse parent latest)
          (fun response final => Notification parent index outcome state final response) ready := by
      exact (reread_checked expected parent index outcome format coherent ready readyValid count
        ((prior.trans later) _ _ fork) (later _ _ child)).weaken (fun _ _ notified => notified.grow (prior.trans later) (.refl _))
    cases settled : Result.settle (slots.set! index (some outcome)) with
    | suspended rest =>
      exact reread publishedAt publishedValid (.refl _)
    | completed result =>
      have cache : Agrees (records parent.key (.completed result)) expected := by
        apply agrees_of_published _ comparable
        intro entry member
        simp only [records, List.mem_singleton] at member
        subst entry
        exact coherent _ _ updated settled
      apply checked_bind (save_checked expected parent (.completed result) cache publishedAt publishedValid) publishedValid
      intro ignored ready readyValid later _
      exact reread ready readyValid later

/-- Preconditions for notifying a parent: its descriptor is durable, the child
is in range, and its prescribed outcome agrees with the shared journal. -/
def ParentReady (expected : Journal) (parent : Location) (index : Nat) (outcome : Exit)
    (state : Durable) : Prop :=
  ∃ count, index < count ∧ view state (forkKey parent.key) = some (toJson count) ∧
    expected (childKey parent.key index) = some (toJson outcome) ∧
    Readable expected parent.key ∧ Coherent expected parent.key

/-- Completion preserves its own outcome and justifies the returned work. -/
def Finished (current : Location) (outcome : Exit) (before : Durable)
    (response : StepResult) (after : Durable) : Prop :=
  CompletedAt (view after) current.key outcome ∧
    match current.parent? with
    | none => response = .done outcome
    | some (parent, index) => Notification parent index outcome before after response

/-- The actual full `finish` action: no atomicity is assumed across its calls.
Every successful return has durable evidence and the correct notification.
The `Safe` contract also covers every interrupted prefix of this action. -/
theorem finish_checked (expected : Journal) (current : Location) (outcome : Exit)
    (format : Readable expected current.key) (coherent : Coherent expected current.key)
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true)
    (intended : expected (resultKey current.key) = some (toJson outcome))
    (before state : Durable) (kept : Valid expected state) (prior : Grows before state)
    (source : CompletionSource (view before) expected current.key outcome)
    (parents : ∀ parent index, current.parent? = some (parent, index) →
      ParentReady expected parent index outcome before) :
    Checked expected (finish workerDb current outcome) (Finished current outcome before) state := by
  have resume (recordedAt : Durable) (valid : Valid expected recordedAt) (growth : Grows state recordedAt)
      (completed : CompletedAt (view recordedAt) current.key outcome) :
      Checked expected (match current.parent? with
        | none => pure (.done outcome)
        | some (parent, index) => do
          let some group ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
          match group with
          | .completed _ => return .runnable #[parent]
          | .suspended children =>
            let updated ← match Result.recordChild group index outcome with
              | .ok result => pure result
              | .error error => throw error
            save workerDb parent (.suspended (children.set! index (some outcome)))
            if let .completed _ := updated then save workerDb parent updated
            let some latest ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
            return joinResponse parent latest)
        (Finished current outcome before) recordedAt := by
    cases linked : current.parent? with
    | none =>
      apply checked_pure
      intro final finalValid later
      exact ⟨completed.grow later.1, by simp [linked]⟩
    | some pair =>
      obtain ⟨parent, index⟩ := pair
      obtain ⟨count, inside, fork, prescribed, parentFormat, parentCoherent⟩ := parents parent index linked
      have notified := notify_checked expected parent index outcome parentFormat parentCoherent comparable sameExit
        prescribed count inside recordedAt valid ((prior.trans growth) _ _ fork)
      -- Retain completion while the notification reads and publishes more records.
      apply Safe.weaken (notified.remember (fun a b => a.trans b) recordedAt (.refl _))
      intro returned final finalValid h
      obtain ⟨later, response, rfl, notification⟩ := h
      exact ⟨response, rfl, completed.grow later.1, by
        simpa only [linked] using notification.grow (prior.trans growth) (.refl _)⟩
  unfold finish
  apply checked_bind (load_checked expected current format coherent state kept) kept
  intro record observed valid growth seen
  cases seen with
  | missing absent fork =>
    have agrees : Agrees (records current.key (.completed outcome)) expected := by
      apply agrees_of_published _ comparable
      intro entry member
      simp only [records, List.mem_singleton] at member
      subst entry
      exact intended
    apply checked_bind (save_checked expected current (.completed outcome) agrees observed valid) valid
    intro ignored saved savedValid later published
    apply resume saved savedValid (growth.trans later)
    apply CompletedAt.cached
    exact published (resultKey current.key, toJson outcome) (by simp [records])
  | completed actual completed =>
    have same : actual = outcome := toJson_injective exit_roundtrip
      (Option.some.inj ((completed_intended coherent valid completed).symm.trans intended))
    subst actual
    simp only [bne, sameExit, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact resume observed valid growth completed
  | suspended slots published incomplete settled =>
    cases source with
    | terminal absent =>
      have fork := valid _ _ (published_fork published).1
      simp [absent] at fork
    | completed recorded => exact False.elim (incomplete outcome (recorded.grow prior.1))

/-- A group already completed before an attempt cannot receive an empty
notification from that attempt, even when it is paused between operations. -/
theorem Notification.completed_before {parent index outcome before after response result}
    (notified : Notification parent index outcome before after response)
    (completed : CompletedAt (view before) parent.key result) :
    response = .runnable #[parent] := by
  cases notified with
  | wake result completed => rfl
  | waiting checked started finished child incomplete =>
    exact False.elim (incomplete result (completed.grow started.1))

/-- Any finite legal schedule of actual `finish` calls, including independent
crashes and fresh retries. Every prefix preserves records; each returned call
succeeds and satisfies `Finished`. Paused or stopped calls need not have returned. -/
theorem finish_concurrent (expected : Journal)
    (locations : Fin count → Location) (outcomes : Fin count → Exit)
    (format : ∀ worker, Readable expected (locations worker).key)
    (coherent : ∀ worker, Coherent expected (locations worker).key)
    (comparable : Comparable expected)
    (sameExit : ∀ worker, (outcomes worker == outcomes worker) = true)
    (intended : ∀ worker, expected (resultKey (locations worker).key) = some (toJson (outcomes worker)))
    (initial : Durable) (bounded : Valid expected initial)
    (source : ∀ worker, CompletionSource (view initial) expected (locations worker).key (outcomes worker))
    (parents : ∀ worker parent index, (locations worker).parent? = some (parent, index) →
      ParentReady expected parent index (outcomes worker) initial)
    (events : List (Event count))
    (final : Simulation.State Durable (Except CloudError StepResult × Unit) count)
    (executed :
      let start := fun worker => (finish (JournalDb.ofDb rawDb) (locations worker) (outcomes worker)).run ()
      Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    Grows initial final.durable ∧ Valid expected final.durable ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned →
        ∃ response, returned = (.ok response, ()) ∧
          Finished (locations worker) (outcomes worker) initial response final.durable := by
  let start := fun worker => (finish workerDb (locations worker) (outcomes worker)).run ()
  let invariant := fun state => Valid expected state ∧ Grows initial state
  let post := fun worker (returned : Except CloudError StepResult × Unit) final =>
    ∃ response, returned = (.ok response, ()) ∧ Finished (locations worker) (outcomes worker) initial response final
  have preserved before after (kept : invariant before) (valid : Valid expected after)
      (growth : Grows before after) : invariant after := ⟨valid, kept.2.trans growth⟩
  have fresh worker state (kept : invariant state) :
      Safe invariant Grows (post worker) (.ofProgram (start worker)) state :=
    (finish_checked expected (locations worker) (outcomes worker) (format worker) (coherent worker)
      comparable (sameExit worker) (intended worker) initial state kept.1 kept.2 (source worker)
      (parents worker)).strengthen invariant (fun _ h => h.1) preserved
  have clock elapsed state (kept : invariant state) :
      invariant (advance elapsed state) ∧ Grows state (advance elapsed state) := ⟨kept, .refl _⟩
  have safe : AllSafe invariant Grows post (Simulation.State.initial initial start) :=
    ⟨⟨bounded, .refl _⟩, fun worker => fresh worker initial ⟨bounded, .refl _⟩⟩
  obtain ⟨growth, kept, workers⟩ := Simulation.run_safe (valid := invariant) (grows := Grows)
    Grows.refl (fun first second => first.trans second)
    start advance post fresh clock events safe executed
  exact ⟨growth, kept.1, fun worker returned finished =>
    (workers worker).returned Grows.refl kept finished⟩

end LeanCloud.Proofs.ConcurrentJournal
