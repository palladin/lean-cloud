import LeanCloud.Simulation
import LeanCloud.Proofs.ArrayEffects

/-! Assertions for existing SimM computations. An atomic reply carries a stable
postcondition into its saved continuation. These are proof rules over lean-eff's
syntax, not another interpreter or a change to the simulator. -/

namespace LeanCloud.Proofs.SimulationLogic
open LeanEff Simulation

structure Rules (δ : Type) where
  invariant : δ → Prop
  interference : δ → δ → Prop
  orphanInterference : δ → δ → Prop
  guarantee : Bool → δ → δ → Prop

variable {δ : Type} (rules : Rules δ)

namespace Rules

def Stable (relation : δ → δ → Prop) (assertion : δ → Prop) : Prop :=
  ∀ before after, rules.invariant before → rules.invariant after →
    relation before after → assertion before → assertion after

def Implies (first second : δ → Prop) : Prop :=
  ∀ world, rules.invariant world → first world → second world

/-- Remote requests must retain their precondition even after their process
restarts. Local requests disappear on a crash, so only ordinary interference
stability is needed for them. -/
structure Operation (remote : Bool) (operation : δ → α × δ)
    (pre : δ → Prop) (post : α → δ → Prop) : Prop where
  waiting : rules.Stable rules.interference pre
  orphan : remote = true → rules.Stable rules.orphanInterference pre
  replying : ∀ value, rules.Stable rules.interference (post value)
  execute : ∀ world, rules.invariant world → pre world →
    let (value, after) := operation world
    rules.invariant after ∧ rules.guarantee remote world after ∧ post value after

mutual
  def Program (rules : Rules δ) (pre : δ → Prop) (post : α → δ → Prop) : SimM δ α → Prop
    | .pure _ value => rules.Implies pre (post value)
    | .impure _ (.step remote _ operation) next =>
        ∃ required reply,
          rules.Implies pre required ∧ rules.Operation remote operation required reply ∧
            rules.Continuation reply post next
  termination_by structural program => program

  def Continuation (rules : Rules δ) (pre : α → δ → Prop) (post : β → δ → Prop) : ArrsF (Atomic δ) Empty α β → Prop
    | .one next => ∀ value, rules.Program (pre value) post (next value)
    | .append first rest =>
        ∃ middle, rules.Continuation pre middle first ∧ rules.Continuation middle post rest
  termination_by structural next => next
end

/-- A proof may select a witness from the current precondition. Each witness's
reply assertion stays attached to that witness while execution is suspended. -/
theorem Operation.exists_contract {ι : Sort v} {remote : Bool} {operation : δ → α × δ}
    {pre : ι → δ → Prop} {post : ι → α → δ → Prop}
    (valid : ∀ index, rules.Operation remote operation (pre index) (post index)) :
    rules.Operation remote operation (fun world => ∃ index, pre index world)
      (fun value world => ∃ index, post index value world) := by
  constructor
  · intro before after first last moves ⟨index, holds⟩
    exact ⟨index, (valid index).waiting before after first last moves holds⟩
  · intro remote before after first last moves ⟨index, holds⟩
    exact ⟨index, (valid index).orphan remote before after first last moves holds⟩
  · intro value before after first last moves ⟨index, holds⟩
    exact ⟨index, (valid index).replying value before after first last moves holds⟩
  · intro world invariant ⟨index, holds⟩
    obtain ⟨last, guarantee, result⟩ := (valid index).execute world invariant holds
    exact ⟨last, guarantee, index, result⟩

mutual
  theorem Program.exists_contract {ι : Sort v} (program : SimM δ α)
      {pre : ι → δ → Prop} {post : ι → α → δ → Prop}
      (valid : ∀ index, rules.Program (pre index) (post index) program) :
      rules.Program (fun world => ∃ index, pre index world)
        (fun value world => ∃ index, post index value world) program :=
    match program with
    | .pure _ value => fun world invariant ⟨index, holds⟩ => ⟨index, valid index world invariant holds⟩
    | .impure _ (.step _ _ _) next => by
      classical
      let required := fun index => Classical.choose (valid index)
      let reply := fun index => Classical.choose (Classical.choose_spec (valid index))
      have evidence := fun index => Classical.choose_spec (Classical.choose_spec (valid index))
      refine ⟨fun world => ∃ index, required index world, fun value world => ∃ index, reply index value world, ?_,
        Operation.exists_contract rules (fun index => (evidence index).2.1),
        Continuation.exists_contract next (fun index => (evidence index).2.2)⟩
      intro world invariant ⟨index, holds⟩
      exact ⟨index, (evidence index).1 world invariant holds⟩
  termination_by structural program

  theorem Continuation.exists_contract {ι : Sort v} (next : ArrsF (Atomic δ) Empty α β)
      {pre : ι → α → δ → Prop} {post : ι → β → δ → Prop}
      (valid : ∀ index, rules.Continuation (pre index) (post index) next) :
      rules.Continuation (fun value world => ∃ index, pre index value world)
        (fun value world => ∃ index, post index value world) next :=
    match next with
    | .one next => fun value => Program.exists_contract (next value) (fun index => valid index value)
    | .append first rest => by
      classical
      let middle := fun index => Classical.choose (valid index)
      have evidence := fun index => Classical.choose_spec (valid index)
      exact ⟨fun value world => ∃ index, middle index value world,
        Continuation.exists_contract first (fun index => (evidence index).1),
        Continuation.exists_contract rest (fun index => (evidence index).2)⟩
  termination_by structural next
end

theorem Program.weaken {pre required : δ → Prop} {post : α → δ → Prop} {program : SimM δ α}
    (valid : rules.Program required post program) (implies : rules.Implies pre required) :
    rules.Program pre post program := by
  cases program with
  | pure info value => exact fun world invariant holds => valid world invariant (implies world invariant holds)
  | impure info request next =>
    cases request
    obtain ⟨needed, reply, entails, operation, continuation⟩ := valid
    exact ⟨needed, reply, fun world invariant holds => entails world invariant (implies world invariant holds),
      operation, continuation⟩

/-- Facts that survive both interference and the computation's own writes may
be retained alongside every operation's result. -/
structure Frame (assertion : δ → Prop) : Prop where
  interference : rules.Stable rules.interference assertion
  orphan : rules.Stable rules.orphanInterference assertion
  operation : ∀ remote, rules.Stable (rules.guarantee remote) assertion

theorem Operation.frame {remote : Bool} {operation : δ → α × δ}
    {pre assertion : δ → Prop} {post : α → δ → Prop}
    (valid : rules.Operation remote operation pre post) (framed : rules.Frame assertion) :
    rules.Operation remote operation (fun world => pre world ∧ assertion world)
      (fun value world => post value world ∧ assertion world) := by
  constructor
  · intro before after first last moves holds
    exact ⟨valid.waiting before after first last moves holds.1,
      framed.interference before after first last moves holds.2⟩
  · intro remote before after first last moves holds
    exact ⟨valid.orphan remote before after first last moves holds.1,
      framed.orphan before after first last moves holds.2⟩
  · intro value before after first last moves holds
    exact ⟨valid.replying value before after first last moves holds.1,
      framed.interference before after first last moves holds.2⟩
  · intro world invariant holds
    obtain ⟨invariant', guarantee, result⟩ := valid.execute world invariant holds.1
    exact ⟨invariant', guarantee, result,
      framed.operation remote _ _ invariant invariant' guarantee holds.2⟩

mutual
  theorem Program.frame (program : SimM δ α) {pre assertion : δ → Prop} {post : α → δ → Prop}
      (valid : rules.Program pre post program) (framed : rules.Frame assertion) :
      rules.Program (fun world => pre world ∧ assertion world)
        (fun value world => post value world ∧ assertion world) program :=
    match program with
    | .pure _ value => fun world invariant holds => ⟨valid world invariant holds.1, holds.2⟩
    | .impure _ (.step _ _ _) next => by
      obtain ⟨required, reply, entails, operation, continuation⟩ := valid
      exact ⟨fun world => required world ∧ assertion world, fun value world => reply value world ∧ assertion world,
        fun world invariant holds => ⟨entails world invariant holds.1, holds.2⟩,
        operation.frame rules framed, Continuation.frame next continuation framed⟩
  termination_by structural program

  theorem Continuation.frame (next : ArrsF (Atomic δ) Empty α β)
      {pre : α → δ → Prop} {assertion : δ → Prop} {post : β → δ → Prop}
      (valid : rules.Continuation pre post next) (framed : rules.Frame assertion) :
      rules.Continuation (fun value world => pre value world ∧ assertion world)
        (fun value world => post value world ∧ assertion world) next :=
    match next with
    | .one next => fun value => Program.frame (next value) (valid value) framed
    | .append first rest => by
      obtain ⟨middle, firstValid, restValid⟩ := valid
      exact ⟨fun value world => middle value world ∧ assertion world,
        Continuation.frame first firstValid framed, Continuation.frame rest restValid framed⟩
  termination_by structural next
end

mutual
  theorem Program.weaken_post (program : SimM δ α) {pre : δ → Prop} {post weaker : α → δ → Prop}
      (valid : rules.Program pre post program) (implies : ∀ value, rules.Implies (post value) (weaker value)) :
      rules.Program pre weaker program :=
    match program with
    | .pure _ value => fun world invariant holds => implies value world invariant (valid world invariant holds)
    | .impure _ (.step _ _ _) next => by
      obtain ⟨needed, reply, entails, operation, continuation⟩ := valid
      exact ⟨needed, reply, entails, operation, Continuation.weaken_post next continuation implies⟩
  termination_by structural program

  theorem Continuation.weaken_post (next : ArrsF (Atomic δ) Empty α β)
      {pre : α → δ → Prop} {post weaker : β → δ → Prop}
      (valid : rules.Continuation pre post next) (implies : ∀ value, rules.Implies (post value) (weaker value)) :
      rules.Continuation pre weaker next :=
    match next with
    | .one next => fun value => Program.weaken_post (next value) (valid value) implies
    | .append first rest => by
      obtain ⟨middle, firstValid, restValid⟩ := valid
      exact ⟨middle, firstValid, Continuation.weaken_post rest restValid implies⟩
  termination_by structural next
end

theorem Program.exists_pre {ι : Sort v} {program : SimM δ α}
    {pre : ι → δ → Prop} {post : α → δ → Prop}
    (valid : ∀ index, rules.Program (pre index) post program) :
    rules.Program (fun world => ∃ index, pre index world) post program :=
  (Program.exists_contract rules program valid).weaken_post rules program
    (fun _ _ _ ⟨_, holds⟩ => holds)

mutual
  theorem Program.impossible (program : SimM δ α) :
      rules.Program (fun _ => False) (fun _ _ => False) program :=
    match program with
    | .pure _ _ => fun _ _ impossible => impossible
    | .impure _ (.step _ _ _) next =>
      ⟨fun _ => False, fun _ _ => False, fun _ _ impossible => impossible,
        ⟨fun _ _ _ _ _ impossible => impossible,
          fun _ _ _ _ _ _ impossible => impossible,
          fun _ _ _ _ _ _ impossible => impossible,
          fun _ _ impossible => impossible.elim⟩,
        Continuation.impossible next⟩
  termination_by structural program

  theorem Continuation.impossible (next : ArrsF (Atomic δ) Empty α β) :
      rules.Continuation (fun _ _ => False) (fun _ _ => False) next :=
    match next with
    | .one next => fun value => Program.impossible (next value)
    | .append first rest => ⟨fun _ _ => False, Continuation.impossible first, Continuation.impossible rest⟩
  termination_by structural next
end

theorem Program.assuming (fact : Prop) {program : SimM δ α} {pre : δ → Prop} {post : α → δ → Prop}
    (valid : fact → rules.Program pre post program) :
    rules.Program (fun world => fact ∧ pre world) post program := by
  classical
  by_cases holds : fact
  · exact (valid holds).weaken rules (fun _ _ required => required.2)
  · apply Program.weaken rules
    · apply Program.weaken_post rules _ (Program.impossible rules _)
      exact fun _ _ _ impossible => impossible.elim
    · exact fun _ _ required => holds required.1

theorem bind {pre : δ → Prop} {middle : α → δ → Prop} {post : β → δ → Prop}
    {program : SimM δ α} {next : α → SimM δ β}
    (first : rules.Program pre middle program)
    (rest : ∀ value, rules.Program (middle value) post (next value)) :
    rules.Program pre post (EffF.bind program next) := by
  cases program with
  | pure info value => exact (rest value).weaken rules first
  | impure info request continuation =>
    cases request
    obtain ⟨required, reply, entails, operation, continuation⟩ := first
    exact ⟨required, reply, entails, operation, middle, continuation, rest⟩

/-- An ordinary loop retains its invariant through every body and saved
continuation. This follows the actual loop without monad-law assumptions. -/
theorem forIn_list (items : List α) (initial : β) (body : α → β → SimM δ (ForInStep β))
    (pre : δ → Prop)
    (valid : ∀ item ∈ items, ∀ state, rules.Program pre (fun _ => pre) (body item state)) :
    rules.Program pre (fun _ => pre) (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact fun _ _ holds => holds
  | cons item items ih =>
    rw [List.forIn_cons]
    apply rules.bind (valid item (by simp) initial)
    intro step
    cases step with
    | done _ => exact fun _ _ holds => holds
    | yield next => exact ih next (fun item member => valid item (by simp [member]))

theorem forIn_array (items : Array α) (initial : β) (body : α → β → SimM δ (ForInStep β))
    (pre : δ → Prop)
    (valid : ∀ item ∈ items, ∀ state, rules.Program pre (fun _ => pre) (body item state)) :
    rules.Program pre (fun _ => pre) (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact rules.forIn_list _ initial body pre (fun item member => valid item (by simpa using member))

theorem send (remote : Bool) (label : String) (operation : δ → α × δ)
    {pre : δ → Prop} {post : α → δ → Prop} (valid : rules.Operation remote operation pre post) :
    rules.Program pre post (EffF.send (.step remote label operation)) :=
  ⟨pre, post, fun _ _ holds => holds, valid, fun _ _ _ holds => holds⟩

theorem except_bind {pre : δ → Prop} {middle : α → δ → Prop} {post : Except ε β → δ → Prop}
    {program : ExceptT ε (SimM δ) α} {next : α → ExceptT ε (SimM δ) β}
    (first : rules.Program pre (fun result => match result with
      | .ok value => middle value | .error error => post (.error error)) program.run)
    (rest : ∀ value, rules.Program (middle value) post (next value).run) :
    rules.Program pre post (program >>= next).run := by
  apply rules.bind first
  intro result
  cases result with
  | ok value => exact rest value
  | error error => exact fun _ _ holds => holds

theorem except_lift {pre : δ → Prop} {middle : α → δ → Prop} {post : Except ε α → δ → Prop}
    {program : SimM δ α} (valid : rules.Program pre middle program)
    (returns : ∀ value, rules.Implies (middle value) (post (.ok value))) :
    rules.Program pre post (ExceptT.lift (ε := ε) program).run :=
  rules.bind valid (fun value => returns value)

/-- A computation succeeds with a specified value and retains its precondition.
The precondition can express all records needed by an ongoing join or replay. -/
def Returns (pre : δ → Prop) (program : ExceptT ε (SimM δ) α) (value : α) : Prop :=
  rules.Program pre (fun result world => result = .ok value ∧ pre world) program.run

theorem returns_pure (pre : δ → Prop) (value : α) :
    rules.Returns pre (Pure.pure value : ExceptT ε (SimM δ) α) value :=
  fun _ _ holds => ⟨rfl, holds⟩

theorem except_bind_known {pre middle : δ → Prop} {post : Except ε β → δ → Prop}
    (program : ExceptT ε (SimM δ) α) (next : α → ExceptT ε (SimM δ) β) (value : α)
    (first : rules.Program pre (fun result world => result = .ok value ∧ middle world) program.run)
    (rest : rules.Program middle post (next value).run) :
    rules.Program pre post (program >>= next).run := by
  apply rules.bind first
  intro returned
  classical
  by_cases same : returned = .ok value
  · subst returned
    exact rest.weaken rules (fun _ _ holds => holds.2)
  · apply Program.weaken rules
    · apply Program.weaken_post rules _ (Program.impossible rules _)
      exact fun _ _ _ impossible => impossible.elim
    · exact fun _ _ holds => same holds.1

theorem except_bind_value {pre : δ → Prop} {post : Except ε β → δ → Prop}
    (program : ExceptT ε (SimM δ) α) (next : α → ExceptT ε (SimM δ) β) (value : α)
    (first : rules.Returns pre program value) (rest : rules.Program pre post (next value).run) :
    rules.Program pre post (program >>= next).run :=
  rules.except_bind_known program next value first rest

theorem returns_bind {pre : δ → Prop} (program : ExceptT ε (SimM δ) α)
    (next : α → ExceptT ε (SimM δ) β) (value : α) (result : β)
    (first : rules.Returns pre program value) (rest : rules.Returns pre (next value) result) :
    rules.Returns pre (program >>= next) result :=
  rules.except_bind_value program next value first rest

theorem returns_mapM (pre : δ → Prop) (items : Array α) (body : α → ExceptT ε (SimM δ) β)
    (expected : α → β) (valid : ∀ item ∈ items, rules.Returns pre (body item) (expected item)) :
    rules.Returns pre (items.mapM body) (items.map expected) :=
  array_mapM_returns (m := ExceptT ε (SimM δ)) (rules.Returns pre)
    (fun value => rules.returns_pure pre value)
    (fun first next value result => rules.returns_bind first next value result) items body expected valid

private def View (pre : α → δ → Prop) (post : β → δ → Prop) : ArrsF.ViewL (Atomic δ) Empty α β → Prop
  | .one next => ∀ value, rules.Program (pre value) post (next value)
  | .cons next rest => ∃ middle,
      (∀ value, rules.Program (pre value) middle (next value)) ∧ rules.Continuation middle post rest

private theorem viewLAppend (first : ArrsF (Atomic δ) Empty α β) (rest : ArrsF (Atomic δ) Empty β γ)
    {pre : α → δ → Prop} {middle : β → δ → Prop} {post : γ → δ → Prop}
    (firstValid : rules.Continuation pre middle first) (restValid : rules.Continuation middle post rest) :
    rules.View pre post (first.viewLAppend rest) := by
  cases first with
  | one next => exact ⟨middle, firstValid, restValid⟩
  | append first second =>
    obtain ⟨between, firstValid, secondValid⟩ := firstValid
    exact viewLAppend first (second.append rest) firstValid ⟨middle, secondValid, restValid⟩
termination_by sizeOf first

private theorem viewL (next : ArrsF (Atomic δ) Empty α β)
    {pre : α → δ → Prop} {post : β → δ → Prop} (valid : rules.Continuation pre post next) :
    rules.View pre post next.viewL := by
  cases next with
  | one next => exact valid
  | append first rest =>
    obtain ⟨middle, firstValid, restValid⟩ := valid
    exact viewLAppend rules first rest firstValid restValid

/-- Applying the actual continuation queue preserves the asserted relationship
between its reply and the world. No syntactic monad laws are assumed for EffF. -/
theorem apply (next : ArrsF (Atomic δ) Empty α β) {pre : α → δ → Prop} {post : β → δ → Prop}
    (valid : rules.Continuation pre post next) (value : α) :
    rules.Program (pre value) post (next.apply value) := by
  have viewed := viewL rules next valid
  rw [ArrsF.apply]
  split
  next continuation found =>
    rw [found] at viewed
    exact viewed value
  next continuation rest found =>
    rw [found] at viewed
    obtain ⟨middle, firstValid, restValid⟩ := viewed
    exact bind rules (firstValid value) (apply rest restValid)
termination_by sizeOf next
decreasing_by
  have smaller := ArrsF.viewL_rest_lt next
  simp_all

/-- A suspended actor retains an assertion about the actual reply value, not
just a restriction on the effects of every possible continuation. -/
def ActorValid (post : α → δ → Prop) : Actor δ α → δ → Prop
  | .waiting remote _ operation next, world =>
      ∃ required reply, required world ∧ rules.Operation remote operation required reply ∧
        rules.Continuation reply post next
  | .responding value next, world =>
      ∃ reply, reply value world ∧ (∀ value, rules.Stable rules.interference (reply value)) ∧
        rules.Continuation reply post next
  | .stopped, _ => True
  | .finished value, world => post value world

theorem ofProgram {pre : δ → Prop} {post : α → δ → Prop} {program : SimM δ α} {world : δ}
    (valid : rules.Program pre post program) (invariant : rules.invariant world) (holds : pre world) :
    rules.ActorValid post (Actor.ofProgram program) world := by
  cases program with
  | pure info value => exact valid world invariant holds
  | impure info request next =>
    cases request
    obtain ⟨required, reply, entails, operation, continuation⟩ := valid
    exact ⟨required, reply, entails world invariant holds, operation, continuation⟩

theorem ActorValid.advance {post : α → δ → Prop} {actor : Actor δ α} {before after : δ}
    (valid : rules.ActorValid post actor before)
    (postStable : ∀ value, rules.Stable rules.interference (post value))
    (first : rules.invariant before) (last : rules.invariant after) (moves : rules.interference before after) :
    rules.ActorValid post actor after := by
  cases actor with
  | waiting remote label operation next =>
    obtain ⟨required, reply, holds, operation, continuation⟩ := valid
    exact ⟨required, reply, operation.waiting before after first last moves holds, operation, continuation⟩
  | responding value next =>
    obtain ⟨reply, holds, stable, continuation⟩ := valid
    exact ⟨reply, stable value before after first last moves holds, stable, continuation⟩
  | stopped => trivial
  | finished value => exact postStable value before after first last moves valid

end Rules
end LeanCloud.Proofs.SimulationLogic
