import LeanCloud.ReplayFaults
import LeanCloud.Proofs.JournalMerge

/-! Local recovery laws for the worker's atomic journal operations. A fault
before an operation preserves its input; a fault after it preserves its commit.
Every interruption consumes a fault, and retry preserves an idempotent result. -/

namespace LeanCloud.Proofs.WorkerRestart
open ReplayFaults ReplayModel JournalMerge

theorem atomic_cases (label : ReplayFaults.Operation) (operation : δ → α × δ)
    (saved : State δ) :
    let (result, after) := (atomic label operation).run saved
    (result = .ok (operation saved.durable).1 ∧ after.durable = (operation saved.durable).2) ∨
    (result = .error .before ∧ after.durable = saved.durable ∧
      after.faults.remaining.length < saved.faults.remaining.length) ∨
    (result = .error .after ∧ after.durable = (operation saved.durable).2 ∧
      after.faults.remaining.length < saved.faults.remaining.length) := by
  rcases saved with ⟨durable, ⟨remaining, visited, crashes⟩⟩
  cases remaining with
  | nil => simp [ExceptT.run, atomic]
  | cons fault rest =>
    rcases fault with ⟨operation', side⟩
    cases same : operation' == label <;> cases side <;> simp [ExceptT.run, atomic, same, show (Side.before == Side.before) = true from rfl, show (Side.after == Side.before) = false from rfl]

/-- More attempts than faults suffice for an atomic idempotent operation.
Unmatched faults need not fire; matched faults are consumed on interruption. -/
theorem restart_atomic (label : ReplayFaults.Operation) (operation : δ → α × δ)
    (idempotent : ∀ state, operation (operation state).2 = operation state)
    (retries : Nat) (saved : State δ) (enough : saved.faults.remaining.length < retries) :
    let (result, after) := (restart retries ((Except.ok (ε := CloudError)) <$> atomic label operation)).run saved
    result = .ok (operation saved.durable).1 ∧ after.durable = (operation saved.durable).2 := by
  induction retries generalizing saved with
  | zero => omega
  | succ retries ih =>
    have cases := atomic_cases label operation saved
    generalize run : (atomic label operation).run saved = returned at cases
    rcases returned with ⟨result, after⟩
    have executes : (restart (retries + 1) ((Except.ok (ε := CloudError)) <$> atomic label operation)).run saved =
        match result with
        | .ok value => ((Except.ok value : Except CloudError α), after)
        | .error _ => (restart retries ((Except.ok (ε := CloudError)) <$> atomic label operation)).run after := by
      simp only [restart, StateT.run]
      have mapped : ((Except.ok (ε := CloudError)) <$> atomic label operation).run saved =
          (result.map (Except.ok (ε := CloudError)), after) := by
        change (ExceptT.map (Except.ok (ε := CloudError)) (atomic label operation)).run saved = _
        unfold ExceptT.map ExceptT.run ExceptT.mk
        change (ExceptT.bindCont (m := StateM (State δ)) (fun value => pure (Except.ok (ε := CloudError) value))
          ((atomic label operation).run saved).1) ((atomic label operation).run saved).2 = _
        rw [run]
        cases result <;> rfl
      rw [mapped]
      cases result <;> rfl
    rw [executes]
    rcases cases with ⟨rfl, committed⟩ | ⟨rfl, unchanged, fewer⟩ | ⟨rfl, committed, fewer⟩
    · exact ⟨rfl, committed⟩
    · simpa only [unchanged] using ih after (by omega)
    · simpa only [committed, idempotent] using ih after (by omega)

private theorem create_idempotent (key : String) (record : ReplayRecord) (journal : Journal) :
    ReplayModel.store.create key record ((ReplayModel.store.create key record journal).2) =
      ReplayModel.store.create key record journal := by
  cases found : journal.lookup key <;> simp [ReplayModel.store, found]

/-- Reads cannot change durable state, even when interrupted. -/
theorem read_preserves (key : String) (saved : State Journal) :
    ((ReplayFaults.store.read key).run saved).2.durable = saved.durable := by
  have cases := atomic_cases (.read key) (fun journal => (journal.lookup key, journal)) saved
  rcases cases with ⟨_, same⟩ | ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> exact same

/-- Before-commit failure adds nothing; after-commit failure keeps the fresh
record. Either way, all old records and the worker's write region are preserved. -/
theorem write_preserves (region : String → Prop) (key : String) (record : ReplayRecord)
    (owned : region key) (saved : State Journal) :
    Writes region saved.durable ((ReplayFaults.store.create key record).run saved).2.durable := by
  have cases := atomic_cases (.create key) (ReplayModel.store.create key record) saved
  have creates := Writes.create region saved.durable key record owned
  change Writes region saved.durable
    ((atomic (.create key) (ReplayModel.store.create key record)).run saved).2.durable
  rcases cases with ⟨_, same⟩ | ⟨_, same, _⟩ | ⟨_, same, _⟩
  · exact same.symm ▸ creates
  · exact same.symm ▸ Writes.refl region saved.durable
  · exact same.symm ▸ creates

/-- Retrying a read returns the same value and leaves the journal untouched. -/
theorem read_restarts (key : String) (retries : Nat) (saved : State Journal)
    (enough : saved.faults.remaining.length < retries) :
    let (result, after) := (restart retries (Except.ok <$> ReplayFaults.store.read key)).run saved
    result = .ok (saved.durable.lookup key) ∧ after.durable = saved.durable :=
  restart_atomic (.read key) (fun journal => (journal.lookup key, journal)) (fun _ => rfl) retries saved enough

/-- A worker's write survives a lost acknowledgement. Retrying returns the
same canonical record and journal as one uninterrupted create, with no duplicate. -/
theorem write_restarts (key : String) (record : ReplayRecord) (retries : Nat)
    (saved : State Journal) (enough : saved.faults.remaining.length < retries) :
    let expected := ReplayModel.store.create key record saved.durable
    let (result, after) := (restart retries (Except.ok <$> ReplayFaults.store.create key record)).run saved
    result = .ok expected.1 ∧ after.durable = expected.2 :=
  restart_atomic (.create key) _ (create_idempotent key record) retries saved enough

end LeanCloud.Proofs.WorkerRestart
