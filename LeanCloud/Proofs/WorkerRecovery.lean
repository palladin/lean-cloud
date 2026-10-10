import LeanCloud.Proofs.WorkerRestart
import LeanCloud.Proofs.Specification

/-! Whole-attempt recovery. Crashes preserve the worker invariant and consume a
fault; ordinary returns establish the postcondition. The retry loop never catches
workflow errors or borrows another worker's state. -/

namespace LeanCloud.Proofs.WorkerRecovery
open ReplayFaults ReplayModel JournalMerge

/-- A successful operation establishes its postcondition. An interrupted one
still preserves the durable invariant and consumes a pending fault. -/
def Ensures (invariant pre : Journal → Prop) (action : ExceptT CloudError WorkerM α)
    (post : α → Journal → Prop) : Prop :=
  ∀ saved, pre saved.durable →
    let (result, after) := action.run.run saved
    invariant after.durable ∧
    after.faults.remaining.length ≤ saved.faults.remaining.length ∧
    match result with
    | .error _ => after.faults.remaining.length < saved.faults.remaining.length
    | .ok (.error _) => False
    | .ok (.ok value) => post value after.durable

theorem Ensures.consequence {action : ExceptT CloudError WorkerM α}
    (safe : Ensures invariant pre action post)
    (before : ∀ journal, pre' journal → pre journal)
    (after : ∀ value journal, post value journal → post' value journal) :
    Ensures invariant pre' action post' := by
  intro saved valid
  obtain ⟨preserved, bounded, correct⟩ := safe saved (before _ valid)
  refine ⟨preserved, bounded, ?_⟩
  cases returned : (action saved).1 with
  | error side => simpa only [returned] using correct
  | ok value =>
    cases value with
    | error error => simp only [returned] at correct
    | ok value => exact after value _ (by simpa only [returned] using correct)

theorem Ensures.pure (value : α) (implies : ∀ journal, pre journal → invariant journal ∧ post value journal) :
    Ensures invariant pre (pure value) post := by
  intro saved valid
  exact ⟨(implies _ valid).1, Nat.le_refl _, (implies _ valid).2⟩

theorem Ensures.bind {action : ExceptT CloudError WorkerM α} {next : α → ExceptT CloudError WorkerM β}
    (first : Ensures invariant pre action middle)
    (rest : ∀ value, Ensures invariant (fun journal => invariant journal ∧ middle value journal) (next value) post) :
    Ensures invariant pre (action >>= next) post := by
  intro saved valid
  have hfirst := first saved valid
  generalize hr : action.run.run saved = returned at hfirst
  rcases returned with ⟨result, after⟩
  have executes : ∀ (result : Except Side (Except CloudError α)) after,
      action.run.run saved = (result, after) →
      ((action >>= next).run.run saved) =
        match result with
        | .error side => (.error side, after)
        | .ok (.error error) => (.ok (.error error), after)
        | .ok (.ok value) => (next value).run.run after := by
    intro returned state eq
    change (ExceptT.bindCont (m := StateM (State Journal)) _ ((action.run.run saved).1)) ((action.run.run saved).2) = _
    rw [eq]
    cases returned with
    | error side => rfl
    | ok returned => cases returned <;> rfl
  rw [executes result after hr]
  rcases hfirst with ⟨preserved, fewer, good⟩
  cases result with
  | error side => exact ⟨preserved, fewer, good⟩
  | ok result =>
    cases result with
    | error error => exact False.elim good
    | ok value =>
      obtain ⟨preserved, bounded, correct⟩ := rest value after ⟨preserved, good⟩
      refine ⟨preserved, Nat.le_trans bounded fewer, ?_⟩
      cases outcome : (next value after).1 with
      | error side =>
        simp only [outcome] at correct ⊢
        exact Nat.lt_of_lt_of_le correct fewer
      | ok result =>
        cases result <;> simp only [outcome] at correct ⊢ <;> exact correct

private theorem atomic_nonincreasing (label : ReplayFaults.Operation) (operation : Journal → α × Journal)
    (saved : State Journal) :
    ((atomic label operation).run saved).2.faults.remaining.length ≤ saved.faults.remaining.length := by
  rcases saved with ⟨durable, ⟨remaining, visited, crashes⟩⟩
  cases remaining with
  | nil => simp [ExceptT.run, ReplayFaults.atomic]
  | cons fault rest =>
    rcases fault with ⟨operation', side⟩
    cases same : operation' == label <;> cases side <;>
      simp [ExceptT.run, ReplayFaults.atomic, same,
        show (Side.before == Side.before) = true from rfl,
        show (Side.after == Side.before) = false from rfl]

theorem Ensures.atomic (label : ReplayFaults.Operation) (operation : Journal → α × Journal)
    (before : ∀ journal, pre journal → invariant journal)
    (after : ∀ journal, pre journal → invariant (operation journal).2 ∧ post (operation journal).1 (operation journal).2) :
    Ensures invariant pre (liftM (ReplayFaults.atomic label operation)) post := by
  intro saved valid
  have cases := WorkerRestart.atomic_cases label operation saved
  have bounded := atomic_nonincreasing label operation saved
  have mapped : (liftM (ReplayFaults.atomic label operation) : ExceptT CloudError WorkerM α).run.run saved =
      (((ReplayFaults.atomic label operation).run saved).1.map Except.ok, ((ReplayFaults.atomic label operation).run saved).2) := by
    change (ExceptT.map Except.ok (ReplayFaults.atomic label operation)).run saved = _
    unfold ExceptT.map ExceptT.run ExceptT.mk
    change (ExceptT.bindCont (m := StateM (State Journal)) _ ((ReplayFaults.atomic label operation saved).1)) ((ReplayFaults.atomic label operation saved).2) = _
    cases (ReplayFaults.atomic label operation saved).1 <;> rfl
  rw [mapped]
  generalize executed : (ReplayFaults.atomic label operation).run saved = result at cases bounded ⊢
  rcases result with ⟨value, finished⟩
  dsimp only at cases bounded ⊢
  rcases cases with ⟨returned, committed⟩ | ⟨interrupted, unchanged, fewer⟩ | ⟨interrupted, committed, fewer⟩
  · rw [returned, committed]
    exact ⟨(after _ valid).1, bounded, (after _ valid).2⟩
  · rw [interrupted, unchanged]
    exact ⟨before _ valid, bounded, fewer⟩
  · rw [interrupted, committed]
    exact ⟨(after _ valid).1, bounded, fewer⟩

/-- A read preserves its precondition as well as the durable journal. -/
theorem Ensures.read (key : String) (valid : ∀ journal, pre journal → invariant journal) :
    Ensures invariant pre (liftM (ReplayFaults.store.read key))
      (fun value journal => pre journal ∧ value = journal.lookup key) :=
  Ensures.atomic (.read key) (fun journal => (journal.lookup key, journal)) valid
    (fun journal h => ⟨valid journal h, h, rfl⟩)

theorem Ensures.read_bind (key : String) (next : Option ReplayRecord → ExceptT CloudError WorkerM α)
    (valid : ∀ journal, pre journal → invariant journal)
    (rest : ∀ value, Ensures invariant (fun journal => pre journal ∧ value = journal.lookup key) (next value) post) :
    Ensures invariant pre (do let value ← ReplayFaults.store.read key; next value) post := by
  apply (Ensures.read key valid).bind
  intro value
  exact (rest value).consequence (fun _ h => h.2) (fun _ _ h => h)

/-- A partial attempt preserves its durable invariant. A crash consumes a fault;
a normal return establishes the promised result. -/
abbrev Attempt (invariant : Journal → Prop) (post : α → Journal → Prop)
    (action : ExceptT CloudError WorkerM α) : Prop := Ensures invariant invariant action post

/-- Restart the whole action, preserving the journal produced by every failed
attempt. More attempts than pending faults suffice. -/
theorem Attempt.restarts {invariant : Journal → Prop} {post : α → Journal → Prop}
    {action : ExceptT CloudError WorkerM α} (safe : Attempt invariant post action)
    (retries : Nat) (saved : State Journal) (valid : invariant saved.durable)
    (enough : saved.faults.remaining.length < retries) :
    let (result, after) := (restart retries action.run).run saved
    invariant after.durable ∧ after.faults.remaining.length ≤ saved.faults.remaining.length ∧
      ∃ value, result = .ok value ∧ post value after.durable := by
  induction retries generalizing saved with
  | zero => omega
  | succ retries ih =>
    have certified := safe saved valid
    generalize executed : action.run.run saved = returned at certified
    rcases returned with ⟨result, after⟩
    simp only at certified
    change (let (result, after) := match (action.run.run saved).1 with
      | .ok result => (result, (action.run.run saved).2)
      | .error _ => (restart retries action.run).run (action.run.run saved).2
      ; invariant after.durable ∧ after.faults.remaining.length ≤ saved.faults.remaining.length ∧
        ∃ value, result = .ok value ∧ post value after.durable)
    rw [executed]
    rcases certified with ⟨preserved, fewer, resultLaw⟩
    cases result with
    | error side =>
      obtain ⟨preserved, bounded, value, returned, correct⟩ := ih after preserved (by omega)
      exact ⟨preserved, Nat.le_trans bounded fewer, value, returned, correct⟩
    | ok result =>
      cases result with
      | error error => exact False.elim resultLaw
      | ok value => exact ⟨preserved, fewer, value, rfl, resultLaw⟩

end LeanCloud.Proofs.WorkerRecovery
