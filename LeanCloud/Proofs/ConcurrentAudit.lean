import LeanCloud.Proofs.ConcurrentHandoff
import LeanCloud.Proofs.ConcurrentLoop

/-! Connect removal certificates to actual replay steps. A permission contains
the received payload, the original program's route, and historical step progress.
It assumes no successful workflow result or future queue delivery. -/

namespace LeanCloud.Proofs.ConcurrentAudit
open Lean LeanEff Simulation SimulationBackend ReplayRecovery
open ConcurrentHandoff (Log)

def Permission (tree : ExecutionTree) : ConcurrentHandoff.Permission := fun since receipt response log =>
  ∃ location node before after, ∃ _route : TreeRoute tree Location.root location node,
    ConcurrentHandoff.Received location receipt before ∧ History.Grows before after ∧ History.Grows after log ∧
    after.past.length = since ∧ ConcurrentJournal.StepProgress tree location node before.current response after.current

theorem Permission.grow {tree since receipt response before after}
    (permitted : Permission tree since receipt response before) (growth : History.Grows before after) :
    Permission tree since receipt response after := by
  obtain ⟨location, node, started, finished, route, received, executed, later, offset, progress⟩ := permitted
  exact ⟨location, node, started, finished, route, received, executed, later.trans growth, offset, progress⟩

def Valid (tree : ExecutionTree) (log : Log) : Prop :=
  ConcurrentQueue.Valid tree log.current ∧ ConcurrentHandoff.Valid (Permission tree) log ∧
    History.Ordered ConcurrentQueue.Grows log

def Grows (before after : Log) : Prop := ConcurrentQueue.Grows before.current after.current ∧ History.Grows before after

theorem Grows.refl (log : Log) : Grows log log := ⟨.refl _, .refl _⟩

theorem Grows.trans {before middle after} (first : Grows before middle) (last : Grows middle after) :
    Grows before after := ⟨first.1.trans last.1, first.2.trans last.2⟩

theorem Valid.initial (tree : ExecutionTree) : Valid tree ⟨SimulationBackend.initial, []⟩ :=
  ⟨ConcurrentQueue.Valid.initial tree, ConcurrentHandoff.Valid.initial _ _, History.Ordered.initial _ _⟩

theorem Valid.advance {tree : ExecutionTree} {log : Log} (valid : Valid tree log) (elapsed : Nat) :
    Valid tree (History.advance SimulationBackend.advance elapsed log) := by
  refine ⟨valid.1.advance elapsed, ⟨.advance _ _, ?_, valid.2.1⟩,
    valid.2.2.append ConcurrentQueue.Grows.refl (fun a b => a.trans b) (ConcurrentQueue.Grows.advance elapsed _)⟩
  intro slot message stored removed
  change log.current.transport.messages[slot]? = some none at removed
  rw [stored] at removed
  cases removed

theorem Grows.advance (elapsed : Nat) (log : Log) :
    Grows log (History.advance SimulationBackend.advance elapsed log) :=
  ⟨ConcurrentQueue.Grows.advance elapsed log.current, History.advance_grows _ _ _⟩

theorem Valid.growth {tree : ExecutionTree} {log before after : Log} (valid : Valid tree log)
    (growth : History.Grows before after) (recorded : History.Grows after log) :
    ConcurrentQueue.Grows before.current after.current :=
  (valid.2.2.earlier recorded).growth ConcurrentQueue.Grows.refl growth

/-- A removed message is accounted for by replay progress at that exact
payload and by publication after the step. Slot identity connects the saved
receipt to the removed message even if the receipt was delivered long ago. -/
theorem Valid.removal {tree : ExecutionTree} {log : Log} (valid : Valid tree log)
    {before after : Durable} {past : List Durable} {slot : Nat} {message : LeaseQueueModel.Message Location}
    (recorded : after :: before :: past <:+ log.states)
    (stored : before.transport.messages[slot]? = some (some message))
    (removed : after.transport.messages[slot]? = some none) :
    ∃ response node started finished, ∃ _route : TreeRoute tree Location.root message.value node,
      History.Grows started finished ∧ History.Grows finished ⟨before, past⟩ ∧
      slot < started.current.transport.messages.size ∧
      ConcurrentJournal.StepProgress tree message.value node started.current response finished.current ∧
      ConcurrentHandoff.Published finished.past.length response ⟨before, past⟩ := by
  obtain ⟨since, receipt, response, slotEq, _ack, permission, published⟩ :=
    valid.2.1.removal recorded slot message stored removed
  obtain ⟨location, node, started, finished, route, received, executed, later, offset, progress⟩ := permission
  have atAck : ConcurrentHandoff.Valid (Permission tree) ⟨before, past⟩ :=
    (valid.2.1.earlier (before := ⟨after, before :: past⟩) recorded).2.2
  have same : message.value = location := ConcurrentHandoff.Received.payload atAck
    (received.grow (executed.trans later)) (by rwa [slotEq])
  have inside := ConcurrentHandoff.Received.inside (atAck.earlier (executed.trans later)) received
  rw [slotEq] at inside
  subst location
  exact ⟨response, node, started, finished, route, executed, later, inside, progress, by rwa [offset]⟩

/-- Any earlier live item is still retained or was retired by a real step
whose response was published. This is historical accountability; recursive
workflow coverage must still account for the successors and parent wakes. -/
theorem Valid.work_accounted {tree : ExecutionTree} {before after : Log}
    (valid : Valid tree after) (growth : History.Grows before after)
    {slot : Nat} {message : LeaseQueueModel.Message Location}
    (stored : before.current.transport.messages[slot]? = some (some message)) :
    (∃ current, after.current.transport.messages[slot]? = some (some current) ∧ current.value = message.value) ∨
      ∃ response node started finished acknowledged, ∃ _route : TreeRoute tree Location.root message.value node,
        History.Grows started finished ∧ History.Grows finished acknowledged ∧ History.Grows acknowledged after ∧
        slot < started.current.transport.messages.size ∧
        ConcurrentJournal.StepProgress tree message.value node started.current response finished.current ∧
        ConcurrentHandoff.Published finished.past.length response acknowledged := by
  rcases valid.2.1.retained_or_removed growth stored with retained | removed
  · exact .inl retained
  · obtain ⟨previous, next, past, _, ⟨⟨current, held, value⟩, deleted⟩, recorded⟩ := removed
    obtain ⟨response, node, started, finished, route, executed, later, inside, progress, published⟩ :=
      valid.removal recorded held deleted
    rw [value] at route progress
    have acknowledged : History.Grows (⟨previous, past⟩ : Log) after :=
      List.IsSuffix.trans ⟨[next], rfl⟩ recorded
    exact .inr ⟨response, node, started, finished, ⟨previous, past⟩, route,
      executed, later, acknowledged, inside, progress, published⟩

private theorem combine {tree : ExecutionTree} {source : M α} {initial : Log}
    {post : α → Durable → Prop} {historyPost : α → Log → Prop}
    (semantic : Safe (ConcurrentQueue.Valid tree) ConcurrentQueue.Grows post (.ofProgram source) initial.current)
    (certified : Safe (ConcurrentHandoff.Valid (Permission tree)) History.Grows historyPost
      (.ofProgram (History.program source)) initial) :
    Safe (Valid tree) Grows (fun value final => post value final.current ∧ historyPost value final)
      (.ofProgram (History.program source)) initial := by
  have lifted := History.record_safe semantic ConcurrentQueue.Grows.refl (fun a b => a.trans b) initial.past
  rw [History.worker_program] at lifted
  exact lifted.combine certified (fun _ h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) (fun _ a b => ⟨a.1, b, a.2⟩)
    (fun _ _ h => ⟨h, h.2⟩) (fun _ _ h _ => h)

/-- Recording a queue-preserving worker action preserves every earlier
acknowledgement certificate, through all of its physical Db requests. -/
private theorem frame {tree : ExecutionTree} {source : M α} {initial : Log}
    {post : α → Durable → Prop}
    (safe : Safe (ConcurrentQueue.Valid tree) ConcurrentQueue.Grows post (.ofProgram source) initial.current)
    (valid : Valid tree initial)
    (uses : Uses ReplayFootprint.JournalOnly source) :
    Safe (Valid tree) Grows (fun value final => post value final.current)
      (.ofProgram (History.program source)) initial := by
  have lifted := History.record_safe safe ConcurrentQueue.Grows.refl (fun a b => a.trans b) initial.past
  rw [History.worker_program] at lifted
  let allowed := fun {β : Type} (action : Log → β × Log) =>
    ∀ log, ConcurrentHandoff.Valid (Permission tree) log → ConcurrentHandoff.Valid (Permission tree) (action log).2
  have footprint : Uses allowed (History.program source) := uses.record (by
    intro β action only log certified
    apply ConcurrentHandoff.NoRemoval.preserves (permit := Permission tree) (initial := log) (valid := certified)
      (lineage := fun state => by rw [(only state).1]; exact .refl _)
    intro state slot message stored removed
    rw [(only state).1, stored] at removed
    cases removed)
  apply lifted.refine (fun log => ⟨.refl _, .refl _⟩)
    (fun a b => ⟨a.1.trans b.1, a.2.trans b.2⟩) ⟨valid.1, valid.2.2⟩ allowed footprint
      (fun _ h => ⟨h.1, h.2.2⟩) (fun h => h)
  intro β action permitted current kept semantic growth
  exact ⟨⟨semantic.1, permitted current kept.2.1, semantic.2⟩, growth⟩

/-- Polling returns actual work with its active route and receipt evidence,
and always crosses a backend boundary, even when the queue is idle. -/
theorem poll_safe (tree : ExecutionTree) (duration : Nat) (worker : SimulationBackend.Worker)
    (initial : Log) (valid : Valid tree initial) :
    Safe (Valid tree) Grows
      (fun returned final => ∃ work, returned.1 = .ok work ∧
        ConcurrentQueue.Next tree (work, returned.2) final.current ∧ ConcurrentHandoff.Polled (work, returned.2) final ∧
        initial.past.length < final.past.length)
      (.ofProgram (History.program ((liftM (queue duration).next :
        ExceptT CloudError (StateT SimulationBackend.Worker M) Work).run worker))) initial := by
  change Safe _ _ _ (.ofProgram (History.program ((queue duration).next.run worker >>=
    fun pair => pure (Except.ok pair.1, pair.2)))) initial
  rw [History.program_bind]
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    (combine (ConcurrentQueue.next_safe tree duration worker initial.current)
      (ConcurrentHandoff.next_advances (Permission tree) duration worker initial)) valid
  intro returned current kept h
  exact .finished fun final finalValid later =>
    ⟨returned.1, rfl, h.1.grow later.1, h.2.1.grow later.2, Nat.lt_of_lt_of_le h.2.2 later.2.length⟩

/-- Polling reaches the caller's actual continuation, with the returned work
and local receipt. For an item, `Next` supplies its active program route and
`Polled` supplies the durable dequeue witness. Neither assumes processing. -/
theorem poll_reaches (tree : ExecutionTree) (duration : Nat) (worker : SimulationBackend.Worker)
    (initial : Log) (valid : Valid tree initial)
    (next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (suspended : Simulation.Worker Log (Except CloudError α × SimulationBackend.Worker))
    (continuing : suspended.Continues (History.program ((do
      let work ← (queue duration).next
      next work : ExceptT CloudError (StateT SimulationBackend.Worker M) α).run worker))) :
    Reaches (Valid tree) Grows (fun suspended final => ∃ work handle,
      suspended.Continues (History.program ((next work).run handle)) ∧
      ConcurrentQueue.Next tree (work, handle) final.current ∧
      ConcurrentHandoff.Polled (work, handle) final ∧ initial.past.length < final.past.length)
      suspended initial := by
  let resume := fun returned : Except CloudError Work × SimulationBackend.Worker =>
    History.program (ExceptT.bindCont next returned.1 returned.2)
  have same : suspended.Continues (History.program ((liftM (queue duration).next :
      ExceptT CloudError (StateT SimulationBackend.Worker M) Work).run worker) >>= resume) := by
    change suspended.Continues (History.program ((liftM (queue duration).next :
      ExceptT CloudError (StateT SimulationBackend.Worker M) Work).run worker >>= _)) at continuing
    rwa [History.program_bind] at continuing
  apply ((poll_safe tree duration worker initial valid).reaches_continuation
    Grows.refl (fun a b => a.trans b) valid resume suspended same).weaken
  intro reached final kept result
  obtain ⟨⟨outcome, handle⟩, remaining, work, same, active, received, advanced⟩ := result
  dsimp only at same
  subst outcome
  exact ⟨work, handle, remaining, active, received, advanced⟩

private theorem complete_action {tree : ExecutionTree} (duration : Nat) (location : Location)
    (receipt : LeaseQueueModel.Receipt) (response : StepResult) (initial : Log) (valid : Valid tree initial)
    (emitted : ConcurrentJournal.Emits tree response initial.current)
    (permitted : Permission tree initial.past.length receipt response initial) :
    Safe (Valid tree) Grows
      (fun returned final => returned = (.ok (), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
        ConcurrentQueue.FinalStored response final.current ∧
        ConcurrentHandoff.Published initial.past.length response final)
      (.ofProgram (History.program ((liftM ((queue duration).complete location response) :
        ExceptT CloudError (StateT SimulationBackend.Worker M) Unit).run ⟨(), some (location, receipt)⟩))) initial := by
  change Safe _ _ _ (.ofProgram (History.program (((queue duration).complete location response).run
    ⟨(), some (location, receipt)⟩ >>= fun pair => pure (Except.ok pair.1, pair.2)))) initial
  rw [History.program_bind]
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    (combine (ConcurrentQueue.complete_safe duration location receipt response initial.current valid.1 emitted)
      (ConcurrentHandoff.complete_safe (fun _ _ _ _ _ growth permit => permit.grow growth)
        duration location receipt response initial valid.2.1 permitted)) valid
  intro returned current kept h
  obtain ⟨⟨rfl, stored⟩, _, published⟩ := h
  apply Safe.finished
  intro final finalValid growth
  refine ⟨rfl, ?_, published.grow growth.2⟩
  cases response with
  | runnable _ => trivial
  | done outcome => exact growth.1.completed outcome stored

/-- A particular delivered step has produced its response, and the adapter
has published that response. The witnesses retain the actual step checkpoint;
successors need not remain in the queue after publication. -/
def PublishedStep (tree : ExecutionTree) (current : Location) (node : ExecutionTree)
    (initial : Log) (response : StepResult) (final : Log) : Prop :=
  ∃ executed, Grows initial executed ∧ Grows executed final ∧
    ConcurrentJournal.StepProgress tree current node initial.current response executed.current ∧
    ConcurrentJournal.Emits tree response executed.current ∧
    ConcurrentHandoff.Published executed.past.length response final

theorem PublishedStep.grow {tree current node initial response before after}
    (published : PublishedStep tree current node initial response before) (growth : Grows before after) :
    PublishedStep tree current node initial response after := by
  obtain ⟨executed, started, finished, progress, emitted, published⟩ := published
  exact ⟨executed, started, finished.trans growth, progress, emitted, published.grow growth.2⟩

/-- The actual step and publication return a response and clear this worker's
receipt. Each publication certificate refers to the real step checkpoint. -/
theorem delivered_safe {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (duration fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) (receipt : LeaseQueueModel.Receipt)
    (initial : Log) (valid : Valid tree initial) (active : route.Activated (ConcurrentJournal.view initial.current))
    (received : ConcurrentHandoff.Received current receipt initial) :
    Safe (Valid tree) Grows (fun returned final => ∃ response,
      returned = (.ok response, (⟨(), none⟩ : SimulationBackend.Worker)) ∧
      PublishedStep tree current node initial response final)
      (.ofProgram (History.program ((do
        let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current
        (queue duration).complete current response
        pure response).run ⟨(), some (current, receipt)⟩))) initial := by
  change Safe _ _ _ (.ofProgram (History.program
    ((ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current).run
      ⟨(), some (current, receipt)⟩ >>= _))) initial
  rw [History.program_bind]
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    ((frame (ConcurrentQueue.step_safe whole supported route comparable sameExit initial.current valid.1 active
      fuel enough ⟨(), some (current, receipt)⟩) valid
      (ReplayFootprint.step fuel program supported current ⟨(), some (current, receipt)⟩)).remember
        (fun a b => a.trans b) initial (.refl _)) valid
  intro returned executed kept done
  obtain ⟨growth, response, rfl, emitted, progress⟩ := done
  have permission : Permission tree executed.past.length receipt response executed :=
    ⟨current, node, initial, executed, route, received, growth.2, .refl _, rfl, progress⟩
  change Safe _ _ _ (.ofProgram (History.program
    ((liftM ((queue duration).complete current response) : ExceptT CloudError (StateT SimulationBackend.Worker M) Unit).run
      ⟨(), some (current, receipt)⟩ >>= _))) executed
  rw [History.program_bind]
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    ((complete_action duration current receipt response executed kept emitted permission).remember
      (fun a b => a.trans b) executed (.refl _)) kept
  intro returned final finalValid completed
  obtain ⟨later, rfl, _, published⟩ := completed
  apply Safe.finished
  intro last lastValid extended
  exact ⟨response, rfl, executed, growth, later.trans extended, progress, emitted, published.grow extended.2⟩

/-- Processing a delivery reaches the caller's actual next code, after
publishing the response and clearing its local receipt. This is a finite prefix
of the original worker, not an assumption that its remaining loop succeeds. -/
theorem delivered_continues {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (duration fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) (receipt : LeaseQueueModel.Receipt)
    (initial : Log) (valid : Valid tree initial) (active : route.Activated (ConcurrentJournal.view initial.current))
    (received : ConcurrentHandoff.Received current receipt initial)
    (next : StepResult → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (suspended : Simulation.Worker Log (Except CloudError α × SimulationBackend.Worker))
    (continuing : suspended.Continues (History.program ((do
      let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current
      (queue duration).complete current response
      next response).run ⟨(), some (current, receipt)⟩))) :
    Reaches (Valid tree) Grows (fun suspended final => ∃ response,
      suspended.Continues (History.program ((next response).run ⟨(), none⟩)) ∧
      PublishedStep tree current node initial response final) suspended initial := by
  let first := ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current
  let finish := fun response => (liftM ((queue duration).complete current response) :
    ExceptT CloudError (StateT SimulationBackend.Worker M) Unit)
  let processed := do
    let response ← first
    finish response
    pure response
  let handle : SimulationBackend.Worker := ⟨(), some (current, receipt)⟩
  have grouped : Equivalent ((processed >>= next).run handle)
      ((first >>= fun response => finish response >>= fun _ => next response).run handle) :=
    Equivalent.action_retain first finish next handle
  let resume := fun returned : Except CloudError StepResult × SimulationBackend.Worker =>
    History.program (ExceptT.bindCont next returned.1 returned.2)
  have same : suspended.Continues (History.program (processed.run handle) >>= resume) := by
    have same := continuing.equivalent grouped.symm.record
    change suspended.Continues (History.program (processed.run handle >>= _)) at same
    rwa [History.program_bind] at same
  apply ((delivered_safe whole supported route comparable sameExit duration fuel enough receipt initial valid active received).reaches_continuation
    Grows.refl (fun a b => a.trans b) valid resume suspended same).weaken
  intro reached final kept result
  obtain ⟨returned, remaining, response, rfl, published⟩ := result
  exact ⟨response, remaining, published⟩

/-- Once a delivery enters the real step, adequate traversal fuel guarantees
it reaches response publication. The following worker continuation is arbitrary:
this prefix proof does not require the whole attempt to finish. -/
theorem delivered_reaches {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (duration fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) (receipt : LeaseQueueModel.Receipt)
    (initial : Log) (valid : Valid tree initial) (active : route.Activated (ConcurrentJournal.view initial.current))
    (received : ConcurrentHandoff.Received current receipt initial)
    (next : StepResult → ExceptT CloudError (StateT SimulationBackend.Worker M) α) :
    Reaches (Valid tree) Grows (fun _ final => ∃ response, PublishedStep tree current node initial response final)
      (.ofProgram (History.program ((do
        let response ← ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current
        (queue duration).complete current response
        next response).run ⟨(), some (current, receipt)⟩))) initial := by
  apply (delivered_continues whole supported route comparable sameExit duration fuel enough receipt
    initial valid active received next _ (Simulation.Worker.continues_program _)).weaken
  intro reached final kept result
  obtain ⟨response, _, published⟩ := result
  exact ⟨response, published⟩

/-- An incorrect fuel error is possible only after enough durable boundaries
have occurred to consume the budget. Workflow errors themselves still count
as the correct expected outcome, even if they use the same error value. -/
def BoundedAnswers [Codec α] (tree : ExecutionTree) (budget origin : Nat)
    (returned : Except CloudError α × SimulationBackend.Worker) (final : Log) : Prop :=
  returned.1 = ConcurrentQueue.expected tree ∨
    (returned.1 = .error ConcurrentQueue.exhausted ∧ budget + origin ≤ sizeOf tree + final.past.length)

theorem BoundedAnswers.mono [Codec α] {tree budget origin budget' origin' returned final}
    (answer : BoundedAnswers (α := α) tree budget origin returned final)
    (bound : budget' + origin' ≤ budget + origin) : BoundedAnswers tree budget' origin' returned final :=
  answer.imp id (fun stopped => ⟨stopped.1, Nat.le_trans bound stopped.2⟩)

theorem BoundedAnswers.forget [Codec α] {tree budget origin returned final}
    (answer : BoundedAnswers (α := α) tree budget origin returned final) :
    ConcurrentQueue.Answers tree returned final.current := answer.imp id And.left

private theorem result_safe [Codec α] (tree : ExecutionTree) (worker : SimulationBackend.Worker) (initial : Log)
    {budget origin : Nat} :
    Safe (Valid tree) Grows (BoundedAnswers (α := α) tree budget origin)
      (.ofProgram (History.program
        ((ReplayInterpreter.Internal.result (m := StateT SimulationBackend.Worker M) tree.exit).run worker))) initial := by
  rw [ConcurrentQueue.result_eq]
  exact .finished fun _ _ _ => .inl rfl

/-- Every acknowledgement in the actual worker loop is justified by its
received location, the replay step's progress, and prior publication of the
response. Certificates cover atomic prefixes, including a lost ack reply. -/
theorem run_safe [Codec α] {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration fuel : Nat) (worker : SimulationBackend.Worker) (initial : Log) (valid : Valid tree initial) :
    Safe (Valid tree) Grows (BoundedAnswers (α := α) tree fuel initial.past.length)
      (.ofProgram (History.program ((ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) fuel program).run worker))) initial := by
  induction fuel generalizing worker initial with
  | zero =>
    apply Safe.finished
    intro final kept growth
    exact .inr ⟨rfl, by have length := growth.2.length; omega⟩
  | succ fuel ih =>
    have resume (worker : SimulationBackend.Worker) (current : Log) (kept : Valid tree current)
        (advanced : initial.past.length < current.past.length) :=
      (ih worker current kept).weaken (post' := BoundedAnswers (α := α) tree (fuel + 1) initial.past.length)
        (fun _ _ _ answer => answer.mono (by omega))
    rw [ReplayInterpreter.Internal.run]
    change Safe _ _ _ (.ofProgram (History.program
      ((liftM (queue duration).next : ExceptT CloudError (StateT SimulationBackend.Worker M) Work).run worker >>= _))) initial
    rw [History.program_bind]
    apply Safe.bind Grows.refl (fun a b => a.trans b) (poll_safe tree duration worker initial valid) valid
    intro returned polled kept done
    rcases returned with ⟨outcome, worker⟩
    obtain ⟨work, same, next, received, advanced⟩ := done
    dsimp only at same
    subst outcome
    cases work with
    | completed outcome =>
      have same := next.2.1
      subst outcome
      exact result_safe tree worker polled
    | idle => exact resume worker polled kept advanced
    | item location =>
      obtain ⟨receipt, delivered, node, route, active⟩ := next
      obtain ⟨observed, delivery, received⟩ := received
      rw [delivered] at delivery
      cases delivery
      change Safe _ _ _ (.ofProgram (History.program
        ((ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs (fuel + 1) program location).run worker >>= _))) polled
      rw [History.program_bind]
      apply Safe.bind Grows.refl (fun a b => a.trans b)
        ((frame (ConcurrentQueue.step_bounded whole supported route comparable (sameExit _ _ route.member)
          polled.current kept.1 active (fuel + 1) worker) kept
          (ReplayFootprint.step (fuel + 1) program supported location worker)).remember
            (fun a b => a.trans b) polled (.refl _)) kept
      intro returned executed executedValid result
      obtain ⟨growth, result⟩ := result
      rcases result with ⟨stopped, short⟩ | ⟨response, rfl, emitted, progress⟩
      · rcases returned with ⟨outcome, handle⟩
        dsimp only at stopped
        subst outcome
        apply Safe.finished
        intro final kept later
        exact .inr ⟨rfl, by have length := (growth.trans later).2.length; omega⟩
      · have permission : Permission tree executed.past.length receipt response executed :=
          ⟨location, node, polled, executed, route, received, growth.2, .refl _, rfl, progress⟩
        cases worker with
        | mk backend delivery =>
          cases backend
          dsimp only at delivered
          subst delivery
          change Safe _ _ _ (.ofProgram (History.program
            ((liftM ((queue duration).complete location response) : ExceptT CloudError (StateT SimulationBackend.Worker M) Unit).run
              ⟨(), some (location, receipt)⟩ >>= _))) executed
          rw [History.program_bind]
          apply Safe.bind Grows.refl (fun a b => a.trans b)
            ((complete_action duration location receipt response executed executedValid emitted permission).remember
              (fun a b => a.trans b) polled growth) executedValid
          intro returned published publishedValid done
          obtain ⟨publishedGrowth, rfl, _stored, _published⟩ := done
          cases response with
          | done outcome =>
            change outcome = tree.exit at emitted
            subst outcome
            exact result_safe tree _ published
          | runnable _ =>
            exact resume _ published publishedValid (Nat.lt_of_lt_of_le advanced publishedGrowth.2.length)

/-- Every finite schedule of the original interpreter has a recorded history
whose removals are certified. No queue-delivery, termination, or successful
attempt is assumed; any prefix may end with crashed or suspended workers. -/
theorem attempts_certified [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat) (events : List (Event count))
    (final : Simulation.State Durable (Except CloudError α × SimulationBackend.Worker) count)
    (executed :
      let start := fun worker => attempt (fuel worker) duration program input
      Simulation.run start SimulationBackend.advance events
        (Simulation.State.initial SimulationBackend.initial start) = .ok final) :
    ∃ past, Grows ⟨SimulationBackend.initial, []⟩ ⟨final.durable, past⟩ ∧ Valid tree ⟨final.durable, past⟩ ∧
      past.length ≤ events.length ∧ ∀ worker returned, (final.workers worker).outcome? = some returned →
        BoundedAnswers tree (fuel worker) 0 returned ⟨final.durable, past⟩ := by
  let start := fun worker => attempt (fuel worker) duration program input
  let recorded := fun worker => History.program (start worker)
  have fresh worker log (valid : Valid tree log) :
      Safe (Valid tree) Grows (BoundedAnswers tree (fuel worker) 0)
        (.ofProgram (recorded worker)) log :=
    (run_safe whole (supported.map codec.encode) comparable sameExit duration (fuel worker) _ log valid).weaken _
      (fun _ _ _ answer => answer.mono (by omega))
  have initial : AllSafe (Valid tree) Grows (fun worker => BoundedAnswers tree (fuel worker) 0)
      (History.state [] (Simulation.State.initial SimulationBackend.initial start)) := by
    refine ⟨Valid.initial tree, fun worker => ?_⟩
    change Safe _ _ _ (History.worker (.ofProgram (start worker))) _
    rw [History.worker_program]
    exact fresh worker _ (Valid.initial tree)
  obtain ⟨past, lifted, bound⟩ := History.run_correspondence start SimulationBackend.advance events _ final [] executed
  obtain ⟨growth, kept, workers⟩ := Simulation.run_safe (valid := Valid tree) (grows := Grows)
    Grows.refl (fun a b => a.trans b) recorded (History.advance SimulationBackend.advance)
    (fun worker => BoundedAnswers tree (fuel worker) 0) fresh
    (fun elapsed log valid => ⟨valid.advance elapsed, Grows.advance elapsed log⟩) events initial lifted
  refine ⟨past, growth, kept, by simpa using bound, ?_⟩
  intro worker returned finished
  apply (workers worker).returned Grows.refl kept
  simpa only [History.state, History.worker_outcome] using finished

/-- The same certificates hold at every point of any original infinite trace.
History records the actual events; it adds no scheduler or delivery assumption. -/
theorem trace_certified [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat)
    (trace : Simulation.Trace (fun worker => attempt (fuel worker) duration program input) SimulationBackend.advance)
    (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
      (fun worker => attempt (fuel worker) duration program input)) :
    (∀ n, Valid tree ((History.trace trace).states n).durable) ∧
      ∀ before after, before ≤ after →
        Grows ((History.trace trace).states before).durable ((History.trace trace).states after).durable := by
  have fresh worker log (valid : Valid tree log) :
      Safe (Valid tree) Grows (fun returned final => ConcurrentQueue.Answers tree returned final.current)
        (.ofProgram (History.program (attempt (fuel worker) duration program input))) log :=
    (run_safe whole (supported.map codec.encode) comparable sameExit duration (fuel worker) _ log valid).weaken _
      (fun _ _ _ answer => answer.forget)
  have initial : AllSafe (Valid tree) Grows (fun _ returned final => ConcurrentQueue.Answers tree returned final.current)
      ((History.trace trace).states 0) := by
    change AllSafe _ _ _ (History.state [] (trace.states 0))
    rw [initialized]
    refine ⟨Valid.initial tree, fun worker => ?_⟩
    change Safe _ _ _ (History.worker (.ofProgram (attempt (fuel worker) duration program input))) _
    rw [History.worker_program]
    exact fresh worker _ (Valid.initial tree)
  have checked := (History.trace trace).invariants Grows.refl (fun a b => a.trans b) fresh
    (fun elapsed log valid => ⟨valid.advance elapsed, Grows.advance elapsed log⟩) initial
  exact ⟨fun n => (checked.1 n).1, checked.2⟩

end LeanCloud.Proofs.ConcurrentAudit
