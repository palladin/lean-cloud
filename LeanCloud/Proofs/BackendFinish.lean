import LeanCloud.Proofs.BackendCompletion

/-! The actual child-completion and parent-notification actions under the
shared service contracts. Every read and write keeps its own commit boundary. -/

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- A wakeup has durable evidence. An empty response has a published child slot
and a reread that started while the group was still incomplete. -/
inductive Notification (parent : Location) (index : Nat) (outcome : Exit)
    (before after : Backend.State) : StepResult → Prop where
  | wake (result : Exit) (completed : CompletedAt (view after) parent.key result) :
      Notification parent index outcome before after (.runnable #[parent])
  | waiting (checked : Backend.State) (started : Grows before checked) (finished : Grows checked after)
      (child : view checked (childKey parent.key index) = some (toJson outcome))
      (incomplete : ∀ result, ¬ CompletedAt (view checked) parent.key result) :
      Notification parent index outcome before after (.runnable #[])

theorem Notification.grow {parent index outcome before after response}
    (notified : Notification parent index outcome before after response)
    {initial final : Backend.State} (earlier : Grows initial before) (later : Grows after final) :
    Notification parent index outcome initial final response := by
  cases notified with
  | wake result completed => exact .wake result (completed.grow later)
  | waiting checked started finished child incomplete =>
    exact .waiting checked (earlier.trans started) (finished.trans later) child incomplete

private theorem reread_checked (expected : View) (parent : Location) (index : Nat) (outcome : Exit)
    (format : Readable expected parent.key) (coherent : Coherent expected parent.key)
    (state : Backend.State) (kept : Valid expected state) (count : Nat)
    (fork : view state (forkKey parent.key) = some (toJson count))
    (child : view state (childKey parent.key index) = some (toJson outcome)) :
    ActionChecked expected (do
      let some latest ← load workerDb parent | throw ⟨.protocol, "Missing parent suspension"⟩
      return joinResponse parent latest)
      (fun response final => Notification parent index outcome state final response) state := by
  apply ActionChecked.bind (load_checked expected parent format coherent state kept) kept
  intro result current valid growth seen
  cases seen with
  | missing absent noFork => simp [fork] at noFork
  | completed result completed =>
    apply action_pure
    intro final finalValid later
    exact .wake result (completed.grow later)
  | suspended slots published incomplete settled =>
    apply action_pure
    intro final finalValid later
    exact .waiting state (.refl _) (growth.trans later) child incomplete

private theorem update_slots {expected : View} {parent : Location} {index : Nat} {outcome : Exit}
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

private theorem notify_checked (expected : View) (parent : Location) (index : Nat) (outcome : Exit)
    (format : Readable expected parent.key) (coherent : Coherent expected parent.key)
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true)
    (prescribed : expected (childKey parent.key index) = some (toJson outcome))
    (count : Nat) (inside : index < count) (state : Backend.State) (kept : Valid expected state)
    (fork : view state (forkKey parent.key) = some (toJson count)) :
    ActionChecked expected (do
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
  apply ActionChecked.bind (load_checked expected parent format coherent state kept) kept
  intro result current valid growth observed
  cases observed with
  | missing absent noFork => simp [fork] at noFork
  | completed result completed =>
    apply action_pure
    intro final finalValid later
    exact .wake result (completed.grow later)
  | suspended slots published incomplete settled =>
    have bounded : JournalAdapter.Published (records parent.key (.suspended slots)) expected :=
      fun entry member => valid _ _ (published entry member)
    have size : slots.size = count := toJson_injective (α := Nat) (fun _ => rfl)
      (Option.some.inj ((valid _ _ (published_fork published).1).symm.trans (kept _ _ fork)))
    have inSlots : index < slots.size := by omega
    obtain ⟨recorded, updated⟩ := update_slots inSlots prescribed bounded sameExit
    simp only [recorded]
    apply ActionChecked.bind (action_pure _ (fun value _ => value = Result.settle (slots.set! index (some outcome))) current (fun _ _ _ => rfl)) valid
    intro selected selectedAt selectedValid selectedGrowth selectedValue
    subst selected
    apply ActionChecked.bind (save_checked expected parent _ (agrees_of_published updated comparable) selectedAt selectedValid) selectedValid
    intro ignored publishedAt publishedValid publishedGrowth durable
    have child := (published_fork durable).2 index (by simpa using inSlots) outcome
      (Array.getElem!_set!_self _ _ _ inSlots)
    have prior : Grows state publishedAt := (growth.trans selectedGrowth).trans publishedGrowth
    have reread (ready : Backend.State) (readyValid : Valid expected ready) (later : Grows publishedAt ready) :
        ActionChecked expected (do
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
      apply ActionChecked.bind (save_checked expected parent (.completed result) cache publishedAt publishedValid) publishedValid
      intro ignored ready readyValid later _
      exact reread ready readyValid later

/-- Preconditions for notifying a parent: its descriptor is durable, the child
is in range, and its prescribed outcome agrees with the shared journal. -/
def ParentReady (expected : View) (parent : Location) (index : Nat) (outcome : Exit)
    (state : Backend.State) : Prop :=
  ∃ count, index < count ∧ view state (forkKey parent.key) = some (toJson count) ∧
    expected (childKey parent.key index) = some (toJson outcome) ∧
    Readable expected parent.key ∧ Coherent expected parent.key

/-- Completion preserves its own outcome and justifies the returned work. -/
def Finished (current : Location) (outcome : Exit) (before : Backend.State)
    (response : StepResult) (after : Backend.State) : Prop :=
  CompletedAt (view after) current.key outcome ∧
    match current.parent? with
    | none => response = .done outcome
    | some (parent, index) => Notification parent index outcome before after response

/-- The actual full `finish` action: no atomicity is assumed across its calls.
Every successful return has durable evidence and the correct notification.
The `Safe` contract also covers every interrupted prefix of this action. -/
theorem finish_checked (expected : View) (current : Location) (outcome : Exit)
    (format : Readable expected current.key) (coherent : Coherent expected current.key)
    (comparable : Comparable expected) (sameExit : (outcome == outcome) = true)
    (intended : expected (resultKey current.key) = some (toJson outcome))
    (before state : Backend.State) (kept : Valid expected state) (prior : Grows before state)
    (source : CompletionSource (view before) expected current.key outcome)
    (parents : ∀ parent index, current.parent? = some (parent, index) →
      ParentReady expected parent index outcome before) :
    ActionChecked expected (finish workerDb current outcome) (Finished current outcome before) state := by
  have resume (recordedAt : Backend.State) (valid : Valid expected recordedAt) (growth : Grows state recordedAt)
      (completed : CompletedAt (view recordedAt) current.key outcome) :
      ActionChecked expected (match current.parent? with
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
      apply action_pure
      intro final finalValid later
      exact ⟨completed.grow later, by simp [linked]⟩
    | some pair =>
      obtain ⟨parent, index⟩ := pair
      obtain ⟨count, inside, fork, prescribed, parentFormat, parentCoherent⟩ := parents parent index linked
      have notified := notify_checked expected parent index outcome parentFormat parentCoherent comparable sameExit
        prescribed count inside recordedAt valid ((prior.trans growth) _ _ fork)
      -- Retain completion while the notification reads and publishes more records.
      apply notified.remember.weaken
      intro response final result
      obtain ⟨later, notification⟩ := result
      exact ⟨completed.grow later, by
        simpa only [linked] using notification.grow (prior.trans growth) (.refl _)⟩
  unfold finish
  apply ActionChecked.bind (load_checked expected current format coherent state kept) kept
  intro record observed valid growth seen
  cases seen with
  | missing absent fork =>
    have agrees : Agrees (records current.key (.completed outcome)) expected := by
      apply agrees_of_published _ comparable
      intro entry member
      simp only [records, List.mem_singleton] at member
      subst entry
      exact intended
    apply ActionChecked.bind (save_checked expected current (.completed outcome) agrees observed valid) valid
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
    | completed recorded => exact False.elim (incomplete outcome (recorded.grow prior))

/-- A group already completed before an attempt cannot receive an empty
notification from that attempt, even when it is paused between operations. -/
theorem Notification.completed_before {parent index outcome before after response result}
    (notified : Notification parent index outcome before after response)
    (completed : CompletedAt (view before) parent.key result) :
    response = .runnable #[parent] := by
  cases notified with
  | wake result completed => rfl
  | waiting checked started finished child incomplete =>
    exact False.elim (incomplete result (completed.grow started))


end LeanCloud.Backend.Proofs.Journal

