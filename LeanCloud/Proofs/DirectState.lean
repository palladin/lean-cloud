import LeanCloud.Proofs.Model
import LeanCloud.Proofs.DirectInterpreter

/-! Direct evaluation never reads or changes the replay journal. This is proved
for the actual evaluator, including all children of nested parallel groups. -/

namespace LeanCloud.Proofs
open LeanEff DirectInterpreter.Internal

/-- A state action is independent of the journal and preserves its contents. -/
def JournalIndependent (action : StateT Journal (StateM World) α) : Prop :=
  ∀ journal world,
    action journal world =
      let ((value, _), nextWorld) := action Journal.empty world
      ((value, journal), nextWorld)

namespace JournalIndependent

theorem pure_action (value : α) : JournalIndependent (World := World) (pure value) := by
  intro journal world
  rfl

theorem bind {α β : Type} {action : StateT Journal (StateM World) α}
    {next : α → StateT Journal (StateM World) β}
    (first : JournalIndependent action) (rest : ∀ value, JournalIndependent (next value)) :
    JournalIndependent (action >>= next) := by
  intro journal world
  change (let ((value, journal'), world') := action journal world
    next value journal' world') = _
  rw [first journal world]
  cases executed : action Journal.empty world with
  | mk pair nextWorld => cases pair with
    | mk value ignored =>
      have preserved := first Journal.empty world
      rw [executed] at preserved
      have empty : ignored = Journal.empty := congrArg (fun result => result.1.2) preserved
      subst ignored
      dsimp only
      rw [rest value journal nextWorld]
      change _ = (let ((value, journal'), world') :=
        (let ((value, journal'), world') := action Journal.empty world
         next value journal' world')
        ((value, journal), world'))
      rw [executed]
      rfl

theorem except_bind {α β : Type}
    {action : ExceptT CloudError (StateT Journal (StateM World)) α}
    {next : α → ExceptT CloudError (StateT Journal (StateM World)) β}
    (first : JournalIndependent action.run) (rest : ∀ value, JournalIndependent (next value).run) :
    JournalIndependent (action >>= next).run := by
  have equation : (action >>= next).run = (action.run >>= fun outcome => match outcome with
      | .ok value => (next value).run
      | .error error => pure (.error error)) := by
    funext journal world
    rw [run_bind_state]
    simp only [Bind.bind, StateT.bind]
    cases action.run journal world with
    | mk pair world' => cases pair with
      | mk outcome journal' => cases outcome <;> rfl
  rw [equation]
  apply first.bind
  intro outcome
  cases outcome with
  | ok value => exact rest value
  | error error => exact pure_action _

theorem ofFnM {α : Type} {count : Nat}
    (actions : Fin count → StateT Journal (StateM World) α)
    (independent : ∀ index, JournalIndependent (actions index)) :
    JournalIndependent (Array.ofFnM actions) := by
  induction count with
  | zero => rw [Array.ofFnM_zero]; exact pure_action _
  | succ count ih =>
    rw [Array.ofFnM_succ']
    exact (independent 0).bind fun _ =>
      (ih (fun index => actions index.succ) (fun index => independent index.succ)).bind fun _ => pure_action _

end JournalIndependent

/-- The direct parallel request runs every child before inspecting errors. -/
theorem direct_parallel_run (blobs : BlobModel World) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α) :
    (evalControl (modelStorage blobs) (.parallel codec count branches)).run = (do
      let outcomes ← Array.ofFnM fun index => (eval (modelStorage blobs) (branches index)).run
      pure (outcomes.mapM id)) := by
  funext journal world
  rw [evalControl, run_bind_state]
  dsimp [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
    ExceptT.run, Functor.map, StateT.map]
  cases executed : (Array.ofFnM (m := StateT Journal (StateM World)) fun index =>
    (eval (modelStorage blobs) (branches index)).run) journal world with
  | mk pair nextWorld => cases pair with
    | mk outcomes nextJournal =>
      dsimp only [ExceptT.run] at executed
      simp only [bind, StateT.bind, pure, StateT.pure, executed]
      cases selected : outcomes.mapM id <;>
        rfl

mutual
  theorem direct_journal_independent {World α : Type} (blobs : BlobModel World)
      (program : Cloud (StateM World) α) :
      JournalIndependent (eval (modelStorage blobs) program).run := by
    match program with
    | .pure value => exact JournalIndependent.pure_action _
    | .impure request continuation =>
      rw [eval]
      exact (direct_control_journal_independent blobs request).except_bind
        (fun value => direct_continuation_journal_independent blobs continuation value)
  termination_by structural program

  theorem direct_control_journal_independent {World α : Type} (blobs : BlobModel World)
      (request : Control (StateM World) α) :
      JournalIndependent (evalControl (modelStorage blobs) request).run := by
    match request with
    | .delay => exact JournalIndependent.pure_action _
    | .fail error => exact JournalIndependent.pure_action _
    | .sequential codec operation => exact modelStorage_execute blobs operation
    | .choice codec count branches => exact JournalIndependent.pure_action _
    | .parallel codec count branches =>
      rw [direct_parallel_run]
      exact (JournalIndependent.ofFnM _ (fun index =>
        direct_journal_independent blobs (branches index))).bind fun _ => JournalIndependent.pure_action _
  termination_by structural request

  theorem direct_continuation_journal_independent {World α β : Type} (blobs : BlobModel World)
      (continuation : ArrsF (Control (StateM World)) α β) (value : α) :
      JournalIndependent (evalContinuation (modelStorage blobs) continuation value).run := by
    match continuation with
    | .one k => exact direct_journal_independent blobs (k value)
    | .append first rest =>
      rw [evalContinuation]
      exact (direct_continuation_journal_independent blobs first value).except_bind
        (fun value => direct_continuation_journal_independent blobs rest value)
  termination_by structural continuation
end

/-- Direct evaluation preserves any supplied journal, on success and failure. -/
theorem direct_preserves_journal (blobs : BlobModel World) (program : Cloud (StateM World) α)
    (journal : Journal) (world : World) :
    ((eval (modelStorage blobs) program).run journal world).1.2 = journal := by
  rw [direct_journal_independent blobs program journal world]
  rfl

/-- Mapping the direct result changes neither state and leaves errors intact. -/
theorem direct_map_run (blobs : BlobModel World) (program : Cloud (StateM World) α)
    (f : α → β) (journal : Journal) (world : World) :
    (eval (modelStorage blobs) (f <$> program)).run journal world =
      let ((outcome, finalJournal), finalWorld) := (eval (modelStorage blobs) program).run journal world
      ((outcome.map f, finalJournal), finalWorld) := by
  rw [DirectInterpreter.eval_map, map_eq_pure_bind, run_bind_state]
  cases executed : (eval (modelStorage blobs) program).run journal world with
  | mk pair nextWorld => cases pair with
    | mk outcome nextJournal => cases outcome <;> rfl

end LeanCloud.Proofs
