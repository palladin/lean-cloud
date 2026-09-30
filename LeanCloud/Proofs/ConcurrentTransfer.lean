import LeanCloud.Proofs.ConcurrentAudit

/-! Finite induction over the actual queue's publication graph. Successors are
allocated after their incoming slot, so concurrent consumption and duplicate
attempts cannot create a cycle in responsibility transfers. Empty child
notifications are the remaining case that needs the parent's join argument. -/

namespace LeanCloud.Proofs.ConcurrentAudit
open Lean Simulation SimulationBackend ReplayRecovery
open ConcurrentHandoff (Log)

/-- The checkpoint precedes every possible receipt of this slot. Root work
uses the initial checkpoint; successors use their parent's response checkpoint. -/
def BeforeSlot (checkpoint : Log) (slot : Nat) (final : Log) : Prop :=
  History.Grows checkpoint final ∧ ∀ earlier, History.Grows earlier final →
    slot < earlier.current.transport.messages.size → History.Grows checkpoint earlier

theorem BeforeSlot.initial {final : Log} (growth : History.Grows ⟨SimulationBackend.initial, []⟩ final) (slot : Nat) :
    BeforeSlot ⟨SimulationBackend.initial, []⟩ slot final :=
  ⟨growth, fun _ earlier _ => growth.between earlier (Nat.zero_le _)⟩

theorem BeforeSlot.fresh {tree : ExecutionTree} {checkpoint final : Log} {slot : Nat}
    (valid : Valid tree final) (growth : History.Grows checkpoint final)
    (fresh : checkpoint.current.transport.messages.size ≤ slot) : BeforeSlot checkpoint slot final := by
  refine ⟨growth, ?_⟩
  intro earlier recorded inside
  by_cases ordered : checkpoint.past.length ≤ earlier.past.length
  · exact growth.between recorded ordered
  · have previous := recorded.between growth (by omega)
    have size := ((valid.2.1.earlier growth).lineage previous).size
    omega

theorem Valid.published_done {tree : ExecutionTree} {log acknowledged : Log} {since outcome}
    (valid : Valid tree log) (recorded : History.Grows acknowledged log)
    (published : ConcurrentHandoff.Published since (.done outcome) acknowledged) :
    log.current.completed = some outcome := by
  obtain ⟨previous, next, past, _, written, happened⟩ := published
  have growth : History.Grows (⟨next, previous :: past⟩ : Log) log := happened.trans recorded
  apply (valid.growth growth (.refl _)).completed outcome
  rw [written]
  rfl

/-- Every runnable successor satisfies the induction predicate at a slot
allocated after this checkpoint. Final-result publication is already supplied
by the retirement witness. -/
def Successors (property : Nat → Location → Prop) (checkpointSize : Nat) : StepResult → Prop
  | .done _ => True
  | .runnable locations => ∀ location ∈ locations,
      ∃ newer, checkpointSize ≤ newer ∧ property newer location

/-- Reduce an earlier work item's responsibility to currently retained items
and actual replay responses. The rule for a retired item may use every emitted
successor, including successors consumed before its own acknowledgement.
Induction decreases the number of allocated slots after the selected slot. -/
theorem Valid.induct_work {tree : ExecutionTree} {final : Log} (valid : Valid tree final)
    (property : Nat → Location → Prop)
    (live : ∀ slot message, final.current.transport.messages[slot]? = some (some message) → property slot message.value)
    (retired : ∀ slot location node started finished acknowledged response,
      TreeRoute tree Location.root location node →
      History.Grows started finished → History.Grows finished acknowledged → History.Grows acknowledged final →
      slot < started.current.transport.messages.size →
      ConcurrentJournal.StepProgress tree location node started.current response finished.current →
      ConcurrentHandoff.Published finished.past.length response acknowledged →
      Successors property finished.current.transport.messages.size response → property slot location)
    {before : Log} (growth : History.Grows before final) {slot : Nat} {message : LeaseQueueModel.Message Location}
    (stored : before.current.transport.messages[slot]? = some (some message)) : property slot message.value := by
  rcases valid.work_accounted growth stored with retained | removed
  · obtain ⟨current, held, value⟩ := retained
    rw [← value]
    exact live slot current held
  · obtain ⟨response, node, started, finished, acknowledged, route, executed, later, recorded,
      inside, progress, published⟩ := removed
    apply retired slot message.value node started finished acknowledged response route executed later recorded
      inside progress published
    cases response with
    | done _ => trivial
    | runnable locations =>
      intro location member
      obtain ⟨newer, issued, successor, bound, _, issuedBefore, held, value, _⟩ :=
        ConcurrentHandoff.Published.fresh (valid.2.1.earlier recorded) later published member
      have after : slot < newer := Nat.lt_of_lt_of_le inside
        (Nat.le_trans ((valid.2.1.earlier (later.trans recorded)).lineage executed).size bound)
      have history := issuedBefore.trans recorded
      have allocated : newer < final.current.transport.messages.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp held).choose (valid.2.1.lineage history).size
      refine ⟨newer, bound, ?_⟩
      rw [← value]
      exact Valid.induct_work valid property live retired history held
termination_by final.current.transport.messages.size - slot
decreasing_by omega

end LeanCloud.Proofs.ConcurrentAudit
