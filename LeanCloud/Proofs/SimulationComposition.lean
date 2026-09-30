import LeanCloud.Proofs.SimulationSafety
import LeanCloud.Proofs.SimulationHistory
import LeanCloud.LeaseQueue

/-! Composition for the simulator's real suspended computations. The private
tree only erases continuation-queue association for this proof; atomic operation
and response boundaries remain unchanged. No monad-law instance is asserted
for the concrete freer syntax. -/

namespace LeanCloud.Simulation
open LeanEff

private inductive Tree (δ α : Type) where
  | pure : α → Tree δ α
  | atomic {β : Type} : (δ → β × δ) → (β → Tree δ α) → Tree δ α

private def Tree.bind (program : Tree δ α) (next : α → Tree δ β) : Tree δ β :=
  match program with
  | .pure value => next value
  | .atomic operation rest => .atomic operation (fun value => (rest value).bind next)

private theorem Tree.bind_assoc (program : Tree δ α) (first : α → Tree δ β)
    (second : β → Tree δ γ) :
    (program.bind first).bind second = program.bind (fun value => (first value).bind second) := by
  induction program with
  | pure value => rfl
  | atomic operation rest ih => simp only [Tree.bind]; congr 1; funext value; exact ih value

mutual
  private def tree (program : SimM δ α) : Tree δ α :=
    match program with
    | .pure value => .pure value
    | .impure (.step operation) next => .atomic operation (treeArr next)
  private def treeArr (next : ArrsF (Atomic δ) α β) (value : α) : Tree δ β :=
    match next with
    | .one next => tree (next value)
    | .append first rest => (treeArr first value).bind (treeArr rest)
end

private theorem tree_bind (program : SimM δ α) (next : α → SimM δ β) :
    tree (program >>= next) = (tree program).bind (fun value => tree (next value)) := by
  cases program with
  | pure value => rfl
  | impure operation rest => cases operation; rfl

private theorem tree_pure (value : α) : tree (Pure.pure value : SimM δ α) = .pure value := rfl

private theorem tree_viewAppend (first : ArrsF (Atomic δ) α β) (rest : ArrsF (Atomic δ) β γ)
    (value : α) :
    (match ArrsF.viewLAppend first rest with
      | .one next => tree (next value)
      | .cons next tail => (tree (next value)).bind (treeArr tail)) =
    (treeArr first value).bind (treeArr rest) := by
  cases first with
  | one next => rfl
  | append left right =>
    rw [ArrsF.viewLAppend, tree_viewAppend left (.append right rest), treeArr, Tree.bind_assoc]
    rfl
termination_by sizeOf first

private theorem tree_view (next : ArrsF (Atomic δ) α β) (value : α) :
    (match ArrsF.viewL next with
      | .one next => tree (next value)
      | .cons next tail => (tree (next value)).bind (treeArr tail)) = treeArr next value := by
  cases next with
  | one next => rfl
  | append first rest => exact tree_viewAppend first rest value

private theorem tree_apply (next : ArrsF (Atomic δ) α β) (value : α) :
    tree (ArrsF.apply next value) = treeArr next value := by
  rw [ArrsF.apply]
  have viewed := tree_view next value
  cases h : ArrsF.viewL next with
  | one first => simpa only [h] using viewed
  | cons first rest =>
    change tree ((first value) >>= ArrsF.apply rest) = _
    rw [tree_bind]
    have ih : (fun value => tree (ArrsF.apply rest value)) = treeArr rest :=
      funext (tree_apply rest)
    rw [ih]
    simpa only [h] using viewed
termination_by sizeOf next
decreasing_by simpa [h] using ArrsF.viewL_rest_lt next

/-- The same atomic operations and replies, ignoring only association of the
freer continuation queue. This does not combine operation boundaries. -/
def Equivalent (first second : SimM δ α) : Prop := tree first = tree second

namespace Equivalent

theorem refl (program : SimM δ α) : Equivalent program program := rfl

theorem symm {first second : SimM δ α} (same : Equivalent first second) :
    Equivalent second first := Eq.symm same

theorem trans {first second third : SimM δ α}
    (one : Equivalent first second) (two : Equivalent second third) :
    Equivalent first third := Eq.trans one two

theorem bind {first second : SimM δ α} (same : Equivalent first second)
    {left right : α → SimM δ β} (next : ∀ value, Equivalent (left value) (right value)) :
    Equivalent (first >>= left) (second >>= right) := by
  simp only [Equivalent, tree_bind]
  rw [same]
  exact congrArg _ (funext next)

theorem request (operation : δ → β × δ) (left right : ArrsF (Atomic δ) β α)
    (next : ∀ value, Equivalent (ArrsF.apply left value) (ArrsF.apply right value)) :
    Equivalent (.impure (.step operation) left) (.impure (.step operation) right) := by
  change Tree.atomic operation (treeArr left) = Tree.atomic operation (treeArr right)
  apply congrArg (Tree.atomic operation)
  funext value
  simpa only [Equivalent, tree_apply] using next value

/-- Reassociation changes only the freer continuation queue, not primitive
requests or their reply boundaries. This also applies beneath local state and
Cloud errors, without asserting monad laws for the concrete syntax. -/
theorem action_bind_assoc (first : ExceptT ε (StateT σ (SimM δ)) α)
    (next : α → ExceptT ε (StateT σ (SimM δ)) β)
    (last : β → ExceptT ε (StateT σ (SimM δ)) γ) (handle : σ) :
    Equivalent (((first >>= next) >>= last).run handle)
      ((first >>= fun value => next value >>= last).run handle) := by
  change tree ((first.run handle >>= fun pair => ExceptT.bindCont next pair.1 pair.2) >>=
    fun pair => ExceptT.bindCont last pair.1 pair.2) =
      tree (first.run handle >>= fun pair => ExceptT.bindCont (fun value => next value >>= last) pair.1 pair.2)
  simp only [tree_bind, Tree.bind_assoc]
  congr 1
  funext pair
  rcases pair with ⟨result, handle⟩
  cases result with
  | error error => rfl
  | ok value => exact (tree_bind (next value |>.run handle) _).symm

theorem action_bind {first second : ExceptT ε (StateT σ (SimM δ)) α}
    (same : ∀ handle, Equivalent (first.run handle) (second.run handle))
    {left right : α → ExceptT ε (StateT σ (SimM δ)) β}
    (next : ∀ value handle, Equivalent ((left value).run handle) ((right value).run handle)) (handle : σ) :
    Equivalent ((first >>= left).run handle) ((second >>= right).run handle) := by
  apply (same handle).bind
  intro pair
  rcases pair with ⟨result, handle⟩
  cases result with
  | error error => exact .refl _
  | ok value => exact next value handle

theorem action_retain (first : ExceptT ε (StateT σ (SimM δ)) α)
    (after : α → ExceptT ε (StateT σ (SimM δ)) Unit)
    (next : α → ExceptT ε (StateT σ (SimM δ)) β) (handle : σ) :
    Equivalent (((do
      let value ← first
      after value
      pure value : ExceptT ε (StateT σ (SimM δ)) α) >>= next).run handle)
      ((do let value ← first; after value; next value).run handle) :=
  (action_bind_assoc first (fun value => after value >>= fun _ => pure value) next handle).trans
    (action_bind (fun handle => .refl (first.run handle))
      (fun value handle => action_bind_assoc (after value) (fun _ => pure value) next handle) handle)

end Equivalent

private def Tree.uses (allowed : {β : Type} → (δ → β × δ) → Prop) : Tree δ α → Prop
  | .pure _ => True
  | .atomic operation next => allowed operation ∧ ∀ value, (next value).uses allowed

/-- Every primitive request satisfies `allowed`, including requests reached
after any reply. This describes the existing computation's effects. -/
def Uses (allowed : {β : Type} → (δ → β × δ) → Prop) (program : SimM δ α) : Prop :=
  (tree program).uses allowed

private theorem Tree.uses_bind {allowed : {β : Type} → (δ → β × δ) → Prop}
    {program : Tree δ α} {next : α → Tree δ β} (first : program.uses allowed)
    (rest : ∀ value, (next value).uses allowed) : (program.bind next).uses allowed := by
  induction program with
  | pure value => exact rest value
  | atomic operation next ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩

theorem Uses.pure (allowed : {β : Type} → (δ → β × δ) → Prop) (value : α) :
    Uses allowed (pure value) := trivial

theorem Uses.atomic {allowed : {β : Type} → (δ → β × δ) → Prop} (operation : δ → α × δ)
    (permitted : allowed operation) : Uses allowed (SimM.atomic operation) := ⟨permitted, fun _ => trivial⟩

theorem Uses.bind {allowed : {β : Type} → (δ → β × δ) → Prop}
    {program : SimM δ α} {next : α → SimM δ β}
    (first : Uses allowed program) (rest : ∀ value, Uses allowed (next value)) :
    Uses allowed (program >>= next) := by
  unfold Uses
  rw [tree_bind]
  exact Tree.uses_bind first rest

private def Tree.record : Tree δ α → Tree (History.Store δ) α
  | .pure value => .pure value
  | .atomic action next => .atomic (History.operation action) (fun value => (next value).record)

private theorem Tree.record_bind (source : Tree δ α) (next : α → Tree δ β) :
    (source.bind next).record = source.record.bind (fun value => (next value).record) := by
  induction source with
  | pure value => rfl
  | atomic action rest ih =>
    simp only [Tree.bind, Tree.record]
    congr 1
    funext value
    exact ih value

mutual
  private theorem tree_record (source : SimM δ α) : tree (History.program source) = (tree source).record := by
    match source with
    | .pure value => rfl
    | .impure (.step action) next =>
      simp only [History.program, tree, Tree.record]
      congr 1
      funext value
      exact treeArr_record next value
  termination_by structural source
  private theorem treeArr_record (next : ArrsF (Atomic δ) α β) (value : α) :
      treeArr (History.continuation next) value = (treeArr next value).record := by
    match next with
    | .one next => exact tree_record (next value)
    | .append first rest =>
      simp only [History.continuation, treeArr, Tree.record_bind, treeArr_record first value]
      congr 1
      funext value
      exact treeArr_record rest value
  termination_by structural next
end

theorem Equivalent.record {first second : SimM δ α} (same : Equivalent first second) :
    Equivalent (History.program first) (History.program second) := by
  unfold Equivalent
  rw [tree_record, tree_record, same]

/-- Recording an operation preserves its primitive footprint. This lets the
worker's existing no-queue-write proof protect acknowledgement certificates. -/
theorem Uses.record {allowed : {β : Type} → (δ → β × δ) → Prop}
    {recorded : {β : Type} → (History.Store δ → β × History.Store δ) → Prop}
    {source : SimM δ α} (uses : Uses allowed source)
    (preserved : ∀ {β} (action : δ → β × δ), allowed action → recorded (History.operation action)) :
    Uses recorded (History.program source) := by
  have lift (meaning : Tree δ α) : meaning.uses allowed → meaning.record.uses recorded := by
    induction meaning with
    | pure value => intro _; trivial
    | atomic action next ih => exact fun permitted => ⟨preserved action permitted.1, fun value => ih value (permitted.2 value)⟩
  unfold Uses
  rw [tree_record]
  exact lift _ uses

/-- The leased adapter carries the caller's receipt through a worker action.
Its atomic behavior is exactly that of the original backend action. -/
def WithHandle (source : ExceptT ε (StateT σ (SimM δ)) α)
    (target : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) (SimM δ)) α) : Prop :=
  ∀ worker, Equivalent (LeaseQueue.liftBackend source.run worker) (target.run worker)

namespace WithHandle

theorem pure (value : α) : WithHandle (pure value : ExceptT ε (StateT σ (SimM δ)) α)
    (pure value : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) (SimM δ)) α) := by
  intro worker
  rfl

theorem throw (error : ε) : WithHandle (throw error : ExceptT ε (StateT σ (SimM δ)) α)
    (throw error : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) (SimM δ)) α) := by
  intro worker
  rfl

theorem lift (action : StateT σ (SimM δ) α) :
    WithHandle (liftM action : ExceptT ε (StateT σ (SimM δ)) α)
      (liftM (LeaseQueue.liftBackend (ρ := ρ) action) :
        ExceptT ε (StateT (LeaseQueue.Worker σ ρ) (SimM δ)) α) := by
  intro worker
  change tree ((action worker.backend >>= fun pair => Pure.pure ((Except.ok pair.1 : Except ε α), pair.2)) >>=
    fun pair => Pure.pure (pair.1, { worker with backend := pair.2 })) =
    tree ((action worker.backend >>= fun pair => Pure.pure (pair.1, { worker with backend := pair.2 })) >>=
      fun pair => Pure.pure ((Except.ok pair.1 : Except ε α), pair.2))
  simp only [tree_bind, Tree.bind_assoc, tree_pure, Tree.bind]

theorem bind {source : ExceptT ε (StateT σ (SimM δ)) α}
    {target : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) (SimM δ)) α}
    (same : WithHandle source target)
    {left : α → ExceptT ε (StateT σ (SimM δ)) β}
    {right : α → ExceptT ε (StateT (LeaseQueue.Worker σ ρ) (SimM δ)) β}
    (next : ∀ value, WithHandle (left value) (right value)) :
    WithHandle (source >>= left) (target >>= right) := by
  intro worker
  change tree ((source.run worker.backend >>= fun pair =>
    ExceptT.bindCont left pair.1 pair.2) >>= fun pair =>
      Pure.pure (pair.1, { worker with backend := pair.2 })) =
    tree (target.run worker >>= fun pair =>
      ExceptT.bindCont right pair.1 pair.2)
  simp only [tree_bind]
  rw [← same worker]
  simp only [LeaseQueue.liftBackend, tree_bind, Tree.bind_assoc, tree_pure, Tree.bind]
  congr 1
  funext pair
  rcases pair with ⟨outcome, backend⟩
  cases outcome with
  | error error => rfl
  | ok value =>
    simpa only [Equivalent, LeaseQueue.liftBackend, tree_bind, tree_pure, ExceptT.bindCont, ExceptT.run] using
      next value { worker with backend }

end WithHandle

private inductive TreePrefix (stop : α → Prop) : Tree δ α → Tree δ α → Prop where
  | pure (value : α) : TreePrefix stop (.pure value) (.pure value)
  | stopped (value : α) (permitted : stop value) (remaining : Tree δ α) :
      TreePrefix stop (.pure value) remaining
  | atomic {β : Type} (operation : δ → β × δ) (left right : β → Tree δ α)
      (rest : ∀ value, TreePrefix stop (left value) (right value)) :
      TreePrefix stop (.atomic operation left) (.atomic operation right)

private theorem TreePrefix.refl (stop : α → Prop) (program : Tree δ α) :
    TreePrefix stop program program := by
  induction program with
  | pure value => exact .pure value
  | atomic operation rest ih => exact .atomic operation rest rest ih

private theorem TreePrefix.trans {stop : α → Prop} {first middle last : Tree δ α}
    (before : TreePrefix stop first middle) (after : TreePrefix stop middle last) : TreePrefix stop first last := by
  induction before generalizing last with
  | pure value => exact after
  | stopped value allowed remaining => exact .stopped value allowed last
  | atomic operation left right next ih =>
    cases after with
    | atomic _ _ final rest => exact .atomic operation left final (fun value => ih value (rest value))

private theorem TreePrefix.bind {stop : α → Prop} {halt : β → Prop}
    {first second : Tree δ α} (same : TreePrefix stop first second)
    {left right : α → Tree δ β}
    (short : ∀ value, stop value → ∀ remaining, TreePrefix halt (left value) remaining)
    (next : ∀ value, TreePrefix halt (left value) (right value)) :
    TreePrefix halt (first.bind left) (second.bind right) := by
  induction same with
  | pure value => exact next value
  | stopped value permitted remaining => exact short value permitted _
  | atomic operation first second rest ih => exact .atomic operation _ _ ih

/-- The same primitive computation, allowing the first program to return early
only at a result satisfying `stop`. No effects or replies may be skipped. -/
def Prefix (stop : α → Prop) (first second : SimM δ α) : Prop :=
  TreePrefix stop (tree first) (tree second)

theorem Prefix.trans {stop : α → Prop} {first middle last : SimM δ α}
    (before : Prefix stop first middle) (after : Prefix stop middle last) : Prefix stop first last :=
  TreePrefix.trans before after

theorem Equivalent.prefix {first second : SimM δ α} (same : Equivalent first second) (stop : α → Prop) :
    Prefix stop first second := by
  change TreePrefix stop (tree first) (tree second)
  rw [same]
  exact TreePrefix.refl _ _

theorem Equivalent.apply_append (next : ArrsF (Atomic δ) α β) (value : α) (last : β → SimM δ γ) :
    Equivalent (ArrsF.apply (next.append (.one last)) value) (ArrsF.apply next value >>= last) := by
  simp only [Equivalent, tree_apply, treeArr, tree_bind]

/-- Suspended workers follow the same requests and saved replies. A permitted
early return leaves the other worker paused at its remaining computation. -/
inductive Worker.Prefix (stop : α → Prop) : Worker δ α → Worker δ α → Prop where
  | waiting {β : Type} (operation : δ → β × δ) (left right : ArrsF (Atomic δ) β α)
      (next : ∀ value, Simulation.Prefix stop (ArrsF.apply left value) (ArrsF.apply right value)) :
      Worker.Prefix stop (.waiting operation left) (.waiting operation right)
  | responding {β : Type} (value : β) (left right : ArrsF (Atomic δ) β α)
      (next : Simulation.Prefix stop (ArrsF.apply left value) (ArrsF.apply right value)) :
      Worker.Prefix stop (.responding value left) (.responding value right)
  | stopped : Worker.Prefix stop .stopped .stopped
  | finished (value : α) : Worker.Prefix stop (.finished value) (.finished value)
  | truncated (value : α) (permitted : stop value) (remaining : Worker δ α) :
      Worker.Prefix stop (.finished value) remaining

theorem Worker.Prefix.trans {stop : α → Prop} {first middle last : Worker δ α}
    (before : Worker.Prefix stop first middle) (after : Worker.Prefix stop middle last) : Worker.Prefix stop first last := by
  cases before with
  | waiting operation left right next =>
    cases after with
    | waiting _ _ final rest => exact .waiting operation left final (fun value => (next value).trans (rest value))
  | responding value left right next =>
    cases after with
    | responding _ _ final rest => exact .responding value left final (next.trans rest)
  | stopped => cases after; exact .stopped
  | finished value => exact after
  | truncated value allowed remaining => exact .truncated value allowed last

theorem Worker.Prefix.refl (stop : α → Prop) (worker : Worker δ α) : Worker.Prefix stop worker worker := by
  cases worker with
  | waiting operation next => exact .waiting operation next next (fun value => (Equivalent.refl _).prefix stop)
  | responding value next => exact .responding value next next ((Equivalent.refl _).prefix stop)
  | stopped => exact .stopped
  | finished value => exact .finished value

theorem Prefix.workers {stop : α → Prop} {first second : SimM δ α}
    (same : Prefix stop first second) :
    Worker.Prefix stop (.ofProgram first) (.ofProgram second) := by
  cases first with
  | pure value =>
    cases second with
    | pure result =>
      cases same with
      | pure => exact .finished _
      | stopped _ permitted _ => exact .truncated _ permitted _
    | impure operation next =>
      cases operation
      cases same with
      | stopped _ permitted _ => exact .truncated _ permitted _
  | impure operation left =>
    cases operation with
    | step operation =>
      cases second with
      | pure value => cases same
      | impure request right =>
        cases request with
        | step action =>
          cases same with
          | atomic _ _ _ rest =>
            apply Worker.Prefix.waiting
            intro value
            simpa only [Prefix, tree_apply] using rest value

theorem Worker.Prefix.returned {stop : α → Prop} {first second : Worker δ α}
    (same : Worker.Prefix stop first second) {value : α}
    (finished : first.outcome? = some value) : stop value ∨ second.outcome? = some value := by
  cases same with
  | waiting | responding | stopped => cases finished
  | finished => cases finished; exact .inr rfl
  | truncated _ permitted _ => cases finished; exact .inl permitted

/-- The first action follows exactly the second action's primitive sequence,
but may stop early with this error. Used for bounded traversal, not crashes. -/
def Truncates (error : ε) (first second : ExceptT ε (StateT σ (SimM δ)) α) : Prop :=
  ∀ handle, TreePrefix (fun returned => returned.1 = .error error)
    (tree (first.run handle)) (tree (second.run handle))

namespace Truncates

theorem program {error : ε} {first second : ExceptT ε (StateT σ (SimM δ)) α}
    (same : Truncates error first second) (handle : σ) :
    Prefix (fun returned => returned.1 = .error error) (first.run handle) (second.run handle) :=
  same handle

theorem refl (error : ε) (action : ExceptT ε (StateT σ (SimM δ)) α) :
    Truncates error action action := fun _ => TreePrefix.refl _ _

theorem stop (error : ε) (action : ExceptT ε (StateT σ (SimM δ)) α) :
    Truncates error (throw error) action := by
  intro handle
  change TreePrefix _ (.pure (Except.error error, handle)) _
  exact TreePrefix.stopped (stop := fun returned : Except ε α × σ => returned.1 = .error error)
    (Except.error error, handle) rfl _

theorem bind {error : ε} {first second : ExceptT ε (StateT σ (SimM δ)) α}
    (same : Truncates error first second)
    {left right : α → ExceptT ε (StateT σ (SimM δ)) β}
    (next : ∀ value, Truncates error (left value) (right value)) :
    Truncates error (first >>= left) (second >>= right) := by
  intro handle
  change TreePrefix _ (tree (first.run handle >>= fun pair => ExceptT.bindCont left pair.1 pair.2))
    (tree (second.run handle >>= fun pair => ExceptT.bindCont right pair.1 pair.2))
  simp only [tree_bind]
  apply TreePrefix.bind (same handle)
  · intro pair stopped remaining
    rcases pair with ⟨result, handle⟩
    dsimp only at stopped
    subst result
    change TreePrefix _ (.pure (Except.error error, handle)) remaining
    exact TreePrefix.stopped (stop := fun returned : Except ε β × σ => returned.1 = .error error)
      (Except.error error, handle) rfl remaining
  · intro pair
    rcases pair with ⟨result, handle⟩
    cases result with
    | error error => exact .pure _
    | ok value => simpa only [ExceptT.bindCont, ExceptT.run] using next value handle

end Truncates

private inductive TreeSafe (valid : δ → Prop) (grows : δ → δ → Prop)
    (post : α → δ → Prop) : Tree δ α → δ → Prop where
  | pure {value state} (safe : ∀ current, valid current → grows state current → post value current) :
      TreeSafe valid grows post (.pure value) state
  | atomic {β : Type} {operation : δ → β × δ} {next : β → Tree δ α} {state}
      (commit : ∀ current, valid current → grows state current →
        valid (operation current).2 ∧ grows current (operation current).2)
      (safe : ∀ current, valid current → grows state current →
        ∀ delivered, valid delivered → grows (operation current).2 delivered →
          TreeSafe valid grows post (next (operation current).1) delivered) :
      TreeSafe valid grows post (.atomic operation next) state

private theorem TreeSafe.bind {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    {post : α → δ → Prop} {goal : β → δ → Prop} {program : Tree δ α} {state : δ}
    (safe : TreeSafe valid grows post program state) (kept : valid state)
    (next : α → Tree δ β)
    (resume : ∀ value current, valid current → post value current → TreeSafe valid grows goal (next value) current) :
    TreeSafe valid grows goal (program.bind next) state := by
  induction safe with
  | pure done => exact resume _ _ kept (done _ kept (refl _))
  | atomic commit safe ih =>
    exact .atomic commit fun current currentValid growth delivered deliveredValid later =>
      ih current currentValid growth delivered deliveredValid later deliveredValid

private def workerTree (worker : Worker δ α) : Option (Tree δ α) :=
  match worker with
  | .waiting operation next => some (.atomic operation (treeArr next))
  | .responding value next => some (treeArr next value)
  | .finished value => some (.pure value)
  | .stopped => none

private theorem workerTree_program (program : SimM δ α) :
    workerTree (.ofProgram program) = some (tree program) := by
  cases program with
  | pure value => rfl
  | impure operation next => cases operation; rfl

/-- The worker's remaining atomic computation is this program, ignoring
continuation-queue association. A saved reply is already fixed; delivering it
still requires the actual simulator's resume event. -/
def Worker.Continues (worker : Worker δ α) (program : SimM δ α) : Prop :=
  workerTree worker = some (tree program)

theorem Worker.continues_program (program : SimM δ α) :
    (Worker.ofProgram program).Continues program := workerTree_program program

theorem Worker.continues_responding (next : ArrsF (Atomic δ) β α) (value : β) :
    (Worker.responding value next).Continues (ArrsF.apply next value) := by
  change some (treeArr next value) = some (tree (ArrsF.apply next value))
  rw [tree_apply]

theorem Worker.Continues.equivalent {worker : Worker δ α} {first second : SimM δ α}
    (continuing : worker.Continues first) (same : Equivalent first second) : worker.Continues second :=
  continuing.trans (congrArg some same)

private theorem TreeSafe.mono {valid : δ → Prop} {grows : δ → δ → Prop}
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {program : Tree δ α} {before after : δ}
    (safe : TreeSafe valid grows post program before) (growth : grows before after) :
    TreeSafe valid grows post program after := by
  cases safe with
  | pure done => exact .pure fun current kept later => done current kept (trans growth later)
  | atomic commit safe =>
    exact .atomic
      (fun current kept later => commit current kept (trans growth later))
      (fun current kept later => safe current kept (trans growth later))

private theorem safe_tree {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {worker : Worker δ α} {state : δ}
    (safe : Safe valid grows post worker state) :
    ∀ program, workerTree worker = some program → valid state → TreeSafe valid grows post program state := by
  induction safe with
  | @waiting β operation next state commit safe ih =>
    intro program same kept
    cases same
    apply TreeSafe.atomic commit
    intro current currentValid growth delivered deliveredValid later
    have ready : TreeSafe valid grows post (treeArr next (operation current).1) (operation current).2 :=
      ih current currentValid growth _ rfl (commit current currentValid growth).1
    exact TreeSafe.mono (grows := grows) (before := (operation current).2) (after := delivered) trans ready later
  | @responding β value next state safe ih =>
    intro program same kept
    have equation : workerTree (.ofProgram (ArrsF.apply next value)) = some program := by
      rw [workerTree_program, tree_apply]
      exact same
    exact ih _ kept (refl _) program equation kept
  | finished done => intro program same kept; cases same; exact .pure done
  | stopped => intro program same; cases same

private theorem tree_safe {valid : δ → Prop} {grows : δ → δ → Prop}
    {post : α → δ → Prop} {meaning : Tree δ α} {state : δ}
    (safe : TreeSafe valid grows post meaning state) :
    ∀ program : SimM δ α, tree program = meaning → Safe valid grows post (.ofProgram program) state := by
  induction safe with
  | pure done =>
    intro program same
    cases program with
    | pure value => cases same; exact .finished done
    | impure operation next => cases operation; cases same
  | atomic commit safe ih =>
    intro program same
    cases program with
    | pure value => cases same
    | impure operation next =>
      cases operation
      cases same
      apply Safe.waiting commit
      intro current kept growth
      apply Safe.responding
      intro delivered deliveredValid later
      exact ih current kept growth delivered deliveredValid later _ (tree_apply next _)

private theorem TreePrefix.safe {valid : δ → Prop} {grows : δ → δ → Prop}
    {post : α → δ → Prop} {stop : α → Prop} {first second : Tree δ α}
    (bounded : TreePrefix stop first second) {state : δ}
    (safe : TreeSafe valid grows post second state) :
    TreeSafe valid grows (fun returned final => stop returned ∨ post returned final) first state := by
  induction bounded generalizing state with
  | pure value =>
    cases safe with
    | pure done => exact .pure fun current valid growth => .inr (done current valid growth)
  | stopped value permitted remaining => exact .pure fun _ _ _ => .inl permitted
  | atomic operation first second rest ih =>
    cases safe with
    | atomic commit next =>
      exact .atomic commit fun current valid growth delivered deliveredValid later =>
        ih _ (next current valid growth delivered deliveredValid later)

private inductive TreeReaches (valid : δ → Prop) (grows : δ → δ → Prop)
    (goal : Tree δ α → δ → Prop) : Tree δ α → δ → Prop where
  | arrived {program state} (reached : ∀ current, valid current → grows state current → goal program current) :
      TreeReaches valid grows goal program state
  | atomic {β : Type} {operation : δ → β × δ} {next : β → Tree δ α} {state}
      (remaining : ∀ current, valid current → grows state current →
        ∀ delivered, valid delivered → grows (operation current).2 delivered →
          TreeReaches valid grows goal (next (operation current).1) delivered) :
      TreeReaches valid grows goal (.atomic operation next) state

private theorem TreeReaches.mono {valid : δ → Prop} {grows : δ → δ → Prop}
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {goal : Tree δ α → δ → Prop} {program : Tree δ α} {before after : δ}
    (progress : TreeReaches valid grows goal program before) (growth : grows before after) :
    TreeReaches valid grows goal program after := by
  cases progress with
  | arrived reached => exact .arrived fun current kept later => reached current kept (trans growth later)
  | atomic remaining => exact .atomic fun current kept later => remaining current kept (trans growth later)

private theorem TreeSafe.reaches_bind {valid : δ → Prop} {grows : δ → δ → Prop}
    {post : α → δ → Prop} {goal : Tree δ β → δ → Prop} {program : Tree δ α} {state : δ}
    (safe : TreeSafe valid grows post program state) (next : α → Tree δ β)
    (reached : ∀ value current, valid current → post value current → goal (next value) current) :
    TreeReaches valid grows goal (program.bind next) state := by
  induction safe with
  | pure done => exact .arrived fun current kept growth => reached _ current kept (done current kept growth)
  | atomic commit safe ih => exact .atomic ih

private theorem tree_reaches_goal {valid : δ → Prop} {grows : δ → δ → Prop}
    {goal : Tree δ α → δ → Prop} {meaning : Tree δ α} {state : δ}
    (progress : TreeReaches valid grows goal meaning state) :
    ∀ program : SimM δ α, tree program = meaning →
      Reaches valid grows (fun worker current => ∃ meaning, workerTree worker = some meaning ∧ goal meaning current) (.ofProgram program) state := by
  induction progress with
  | arrived reached =>
    intro program same
    exact .arrived fun current kept growth => ⟨_, (workerTree_program program).trans (congrArg some same), reached current kept growth⟩
  | atomic remaining ih =>
    intro program same
    cases program with
    | pure value => cases same
    | impure operation next =>
      cases operation
      cases same
      apply Reaches.waiting
      intro current kept growth
      apply Reaches.responding
      intro delivered deliveredValid later
      exact ih current kept growth delivered deliveredValid later _ (tree_apply next _)

private theorem tree_reaches {valid : δ → Prop} {grows : δ → δ → Prop}
    {goal : δ → Prop} {meaning : Tree δ α} {state : δ}
    (progress : TreeReaches valid grows (fun _ current => goal current) meaning state)
    (program : SimM δ α) (same : tree program = meaning) :
    Reaches valid grows (fun _ current => goal current) (.ofProgram program) state :=
  (tree_reaches_goal progress program same).weaken (fun _ _ _ ⟨_, _, reached⟩ => reached)

private theorem reaches_tree {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {goal : δ → Prop} {worker : Worker δ α} {state : δ}
    (progress : Reaches valid grows (fun _ current => goal current) worker state) :
    ∀ meaning, workerTree worker = some meaning →
      ∀ current, valid current → grows state current → TreeReaches valid grows (fun _ current => goal current) meaning current := by
  induction progress with
  | arrived reached =>
    intro meaning _ current kept growth
    exact .arrived fun final valid later => reached final valid (trans growth later)
  | waiting remaining ih =>
    intro meaning same current kept prior
    cases same
    exact .atomic fun committed valid growth delivered deliveredValid later =>
      ih committed valid (trans prior growth) _ rfl delivered deliveredValid later
  | @responding β value next state remaining ih =>
    intro meaning same current kept growth
    have equation : workerTree (.ofProgram (ArrsF.apply next value)) = some meaning := by
      rw [workerTree_program, tree_apply]
      exact same
    exact ih current kept growth _ equation current kept (refl _)

private theorem tree_reaches_worker_goal {valid : δ → Prop} {grows : δ → δ → Prop}
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {goal : Tree δ α → δ → Prop} {meaning : Tree δ α} {state : δ}
    (progress : TreeReaches valid grows goal meaning state) (worker : Worker δ α)
    (same : workerTree worker = some meaning) : Reaches valid grows (fun worker current => ∃ meaning, workerTree worker = some meaning ∧ goal meaning current) worker state := by
  cases worker with
  | waiting operation next =>
    cases same
    cases progress with
    | arrived reached => exact .arrived fun current kept growth => ⟨_, rfl, reached current kept growth⟩
    | atomic remaining =>
      exact .waiting fun current kept growth => .responding fun delivered deliveredValid later =>
        tree_reaches_goal (remaining current kept growth delivered deliveredValid later) _ (tree_apply next _)
  | responding value next =>
    cases same
    exact .responding fun current kept growth =>
      tree_reaches_goal (TreeReaches.mono (grows := grows) trans progress growth) _ (tree_apply next value)
  | finished value =>
    cases same
    cases progress with
    | arrived reached => exact .arrived fun current kept growth => ⟨_, rfl, reached current kept growth⟩
  | stopped => cases same

private theorem tree_reaches_worker {valid : δ → Prop} {grows : δ → δ → Prop}
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {goal : δ → Prop} {meaning : Tree δ α} {state : δ}
    (progress : TreeReaches valid grows (fun _ current => goal current) meaning state) (worker : Worker δ α)
    (same : workerTree worker = some meaning) : Reaches valid grows (fun _ current => goal current) worker state :=
  (tree_reaches_worker_goal (grows := grows) trans progress worker same).weaken
    (fun _ _ _ ⟨_, _, reached⟩ => reached)

/-- Finishing a finite prefix exposes the actual continuation and its returned
value. The larger worker may still be waiting, hold a saved reply, or be done;
no successful execution of the continuation is assumed. -/
theorem Safe.reaches_continuation {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {program : SimM δ α} {state : δ}
    (safe : Safe valid grows post (.ofProgram program) state) (kept : valid state)
    (next : α → SimM δ β) (worker : Worker δ β) (same : worker.Continues (program >>= next)) :
    Reaches valid grows (fun worker current => ∃ value, worker.Continues (next value) ∧ post value current)
      worker state := by
  have progress : TreeReaches valid grows
      (fun remaining current => ∃ value, remaining = tree (next value) ∧ post value current)
      ((tree program).bind (fun value => tree (next value))) state :=
    (safe_tree refl trans safe _ (workerTree_program _) kept).reaches_bind
      (fun value => tree (next value)) (fun value _ _ done => ⟨value, rfl, done⟩)
  have related : workerTree worker = some ((tree program).bind (fun value => tree (next value))) :=
    same.trans (congrArg some (tree_bind program next))
  apply (tree_reaches_worker_goal (grows := grows) trans progress worker related).weaken
  intro reached current valid result
  obtain ⟨meaning, suspended, value, equivalent, done⟩ := result
  exact ⟨value, suspended.trans (congrArg some equivalent), done⟩

/-- Apply a prefix-progress proof to the actual suspended continuation,
including the case where a reply still awaits delivery. -/
theorem Reaches.continues {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {goal : δ → Prop} {program : SimM δ α} {worker : Worker δ α} {state : δ}
    (progress : Reaches valid grows (fun _ current => goal current) (.ofProgram program) state)
    (kept : valid state) (same : worker.Continues program) :
    Reaches valid grows (fun _ current => goal current) worker state :=
  tree_reaches_worker (grows := grows) trans
    (reaches_tree refl trans progress _ (workerTree_program _) state kept (refl _)) worker same

private theorem TreeSafe.bind_reaches {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    {post : α → δ → Prop} {goal : δ → Prop} {program : Tree δ α} {state : δ}
    (safe : TreeSafe valid grows post program state) (kept : valid state) (next : α → Tree δ β)
    (resume : ∀ value current, valid current → post value current → TreeReaches valid grows (fun _ current => goal current) (next value) current) :
    TreeReaches valid grows (fun _ current => goal current) (program.bind next) state := by
  induction safe with
  | pure done => exact resume _ _ kept (done _ kept (refl _))
  | atomic commit safe ih =>
    exact .atomic fun current valid growth delivered deliveredValid later =>
      ih current valid growth delivered deliveredValid later deliveredValid

/-- Compose a finite safe action with a continuation that reaches a durable
milestone. The continuation can keep running after that milestone. -/
theorem Safe.bind_reaches {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {goal : δ → Prop} {program : SimM δ α} {state : δ}
    (safe : Safe valid grows post (.ofProgram program) state) (kept : valid state)
    (next : α → SimM δ β)
    (resume : ∀ value current, valid current → post value current →
      Reaches valid grows (fun _ current => goal current) (.ofProgram (next value)) current) :
    Reaches valid grows (fun _ current => goal current) (.ofProgram (program >>= next)) state := by
  apply tree_reaches (meaning := (tree program).bind (fun value => tree (next value)))
  · apply TreeSafe.bind_reaches refl (safe_tree refl trans safe _ (workerTree_program _) kept) kept
    intro value current valid done
    exact reaches_tree refl trans (resume value current valid done) _ (workerTree_program _) current valid (refl _)
  · exact tree_bind program next

/-- Reach a durable milestone established by a finite action at the beginning
of a larger worker. Nothing is assumed about the remaining continuation's
termination. Atomic requests and saved-response boundaries stay unchanged. -/
theorem Safe.reaches_bind {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {goal : δ → Prop} {program : SimM δ α} {state : δ}
    (safe : Safe valid grows post (.ofProgram program) state) (kept : valid state)
    (next : α → SimM δ β)
    (reached : ∀ value current, valid current → post value current → goal current) :
    Reaches valid grows (fun _ current => goal current) (.ofProgram (program >>= next)) state :=
  tree_reaches ((safe_tree refl trans safe _ (workerTree_program _) kept).reaches_bind
    (fun value => tree (next value)) reached) _ (tree_bind program next)

/-- Compose actual suspended computations without identifying the different
continuation-queue shapes produced by monad reassociation. -/
theorem Safe.bind {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {goal : β → δ → Prop} {program : SimM δ α} {state : δ}
    (safe : Safe valid grows post (.ofProgram program) state) (kept : valid state)
    (next : α → SimM δ β)
    (resume : ∀ value current, valid current → post value current →
      Safe valid grows goal (.ofProgram (next value)) current) :
    Safe valid grows goal (.ofProgram (program >>= next)) state := by
  apply tree_safe (meaning := (tree program).bind (fun value => tree (next value)))
  · apply TreeSafe.bind refl (safe_tree refl trans safe _ (workerTree_program _) kept) kept
    intro value current currentValid done
    exact safe_tree refl trans (resume value current currentValid done) _ (workerTree_program _) currentValid
  · exact tree_bind program next

/-- Transfer a safety proof without changing any atomic boundary or result. -/
theorem Safe.equivalent {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {first second : SimM δ α} {state : δ}
    (safe : Safe valid grows post (.ofProgram first) state) (kept : valid state)
    (same : Equivalent first second) :
    Safe valid grows post (.ofProgram second) state :=
  tree_safe (safe_tree refl trans safe _ (workerTree_program _) kept) second same.symm

/-- Strengthen a computation's invariant using its primitive footprint. Other
workers may interfere according to the new growth relation; only this worker's
own commits must satisfy `allowed`. -/
theorem Safe.refine {valid stronger : δ → Prop} {grows refinedGrows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : α → δ → Prop} {program : SimM δ α} {state : δ}
    (safe : Safe valid grows post (.ofProgram program) state) (kept : valid state)
    (allowed : {β : Type} → (δ → β × δ) → Prop) (uses : Uses allowed program)
    (implies : ∀ current, stronger current → valid current)
    (growth : ∀ {before after}, refinedGrows before after → grows before after)
    (commit : ∀ {β} (operation : δ → β × δ), allowed operation →
      ∀ current, stronger current → valid (operation current).2 → grows current (operation current).2 →
        stronger (operation current).2 ∧ refinedGrows current (operation current).2) :
    Safe stronger refinedGrows post (.ofProgram program) state := by
  have checked := safe_tree refl trans safe _ (workerTree_program _) kept
  refine tree_safe (meaning := tree program) ?_ program rfl
  change (tree program).uses allowed at uses
  generalize equation : tree program = meaning at checked uses ⊢
  clear safe kept equation
  induction checked with
  | pure done => exact .pure fun current valid later => done current (implies current valid) (growth later)
  | atomic step next ih =>
    apply TreeSafe.atomic
    · intro current valid later
      have original := step current (implies current valid) (growth later)
      exact commit _ uses.1 current valid original.1 original.2
    · intro current valid later delivered deliveredValid deliveredGrowth
      exact ih current (implies current valid) (growth later) delivered
        (implies delivered deliveredValid) (growth deliveredGrowth) (uses.2 _)

/-- A traversal with less fuel preserves the same state invariants. If it
returns before the longer traversal, its result is the specified fuel error. -/
theorem Safe.truncates {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    {post : (Except ε α × σ) → δ → Prop} {first second : ExceptT ε (StateT σ (SimM δ)) α}
    {error : ε} {handle : σ} {state : δ}
    (safe : Safe valid grows post (.ofProgram (second.run handle)) state) (kept : valid state)
    (bounded : Truncates error first second) :
    Safe valid grows (fun returned final => returned.1 = .error error ∨ post returned final)
      (.ofProgram (first.run handle)) state :=
  tree_safe ((bounded handle).safe (safe_tree refl trans safe _ (workerTree_program _) kept)) _ rfl

end LeanCloud.Simulation
