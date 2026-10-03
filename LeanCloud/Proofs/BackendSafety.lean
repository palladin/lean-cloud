import LeanCloud.Proofs.BackendProgram

/-! Safety under arbitrary service transitions and interference. The commit
obligation survives a crash even when its continuation has been discarded. -/

namespace LeanCloud.Backend.Proofs
open LeanEff Execution

/-- A request must be safe at every permitted later state and for every reply
allowed by the primitive contract. Replies retain their observed value even
when other workers change storage before the continuation runs. -/
inductive Safe (valid : Backend.State → Prop) (grows : Backend.State → Backend.State → Prop)
    (post : α → Backend.State → Prop) : Program α → Backend.State → Prop where
  | pure {value state}
      (done : ∀ current, valid current → grows state current → post value current) :
      Safe valid grows post (.pure value) state
  | request {β : Type} {operation : Request β} {next : β → Program α} {state}
      (commit : ∀ before value after, valid before → grows state before →
        Commits before operation value after → valid after ∧ grows before after)
      (resume : ∀ before value after, valid before → grows state before →
        Commits before operation value after →
        Safe valid grows post (next value) after) :
      Safe valid grows post (.request operation next) state

variable {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
  {post : α → Backend.State → Prop}

theorem Safe.mono {program state after} (safe : Safe valid grows post program state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c) (growth : grows state after) :
    Safe valid grows post program after := by
  cases safe with
  | pure done => exact .pure fun current kept later => done current kept (trans growth later)
  | request commit resume =>
    exact .request
      (fun current value final kept later law => commit current value final kept (trans growth later) law)
      (fun current value final kept later law => resume current value final kept (trans growth later) law)

theorem Safe.weaken {program state} (safe : Safe valid grows post program state)
    (other : α → Backend.State → Prop)
    (implies : ∀ value current, valid current → post value current → other value current) :
    Safe valid grows other program state := by
  induction safe with
  | pure done => exact .pure fun current kept growth => implies _ current kept (done current kept growth)
  | request commit resume ih => exact .request commit ih

theorem Safe.remember {program state} (safe : Safe valid grows post program state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (before : Backend.State) (prior : grows before state) :
    Safe valid grows (fun value final => grows before final ∧ post value final) program state := by
  induction safe with
  | pure done => exact .pure fun current kept growth => ⟨trans prior growth, done current kept growth⟩
  | request commit resume ih =>
    exact .request commit fun current value after kept growth law =>
      ih current value after kept growth law (trans prior (trans growth (commit current value after kept growth law).2))

theorem Safe.bind {program : Program α} {next : α → Program β}
    {first : α → Backend.State → Prop} {post : β → Backend.State → Prop} {state}
    (refl : ∀ current, grows current current)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (safe : Safe valid grows first program state) (kept : valid state)
    (resume : ∀ value current, valid current → grows state current → first value current →
      Safe valid grows post (next value) current) :
    Safe valid grows post (program.bind next) state := by
  induction safe with
  | pure done => exact resume _ _ kept (refl _) (done _ kept (refl _))
  | @request β operation rest state commit remaining ih =>
    apply Safe.request commit
    intro current value after currentValid growth law
    obtain ⟨afterValid, later⟩ := commit current value after currentValid growth law
    apply ih current value after currentValid growth law afterValid
    intro answer final finalValid last result
    exact resume answer final finalValid (trans growth (trans later last)) result

/-- Safety of a concrete freer program, without changing its execution. -/
abbrev ProgramSafe (valid : Backend.State → Prop) (grows : Backend.State → Backend.State → Prop)
    (post : α → Backend.State → Prop) (program : M α) (state : Backend.State) : Prop :=
  Safe valid grows post (Program.ofEff program) state

theorem ProgramSafe.bind {program : M α} {next : α → M β}
    {first : α → Backend.State → Prop} {post : β → Backend.State → Prop} {state}
    (refl : ∀ current, grows current current)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (safe : ProgramSafe valid grows first program state) (kept : valid state)
    (resume : ∀ value current, valid current → grows state current → first value current →
      ProgramSafe valid grows post (next value) current) :
    ProgramSafe valid grows post (program >>= next) state := by
  unfold ProgramSafe
  rw [Program.ofEff_bind]
  exact Safe.bind refl trans safe kept resume

/-- Refine a local invariant using the program's actual request footprint.
Other workers may still make every change allowed by the stronger interference
relation; this only constrains the current program's own operations. -/
theorem Safe.refine {valid stronger : Backend.State → Prop}
    {grows refined : Backend.State → Backend.State → Prop}
    {post : α → Backend.State → Prop} {program : Program α} {state : Backend.State}
    (safe : Safe valid grows post program state)
    (allowed : {β : Type} → Request β → Prop) (uses : program.uses allowed)
    (implies : ∀ current, stronger current → valid current)
    (growth : ∀ {before after}, refined before after → grows before after)
    (commits : ∀ {β} (operation : Request β), allowed operation → ∀ before value after,
      stronger before → Commits before operation value after → valid after → grows before after →
      stronger after ∧ refined before after) :
    Safe stronger refined post program state := by
  induction safe with
  | pure done =>
    exact .pure fun current kept later => done current (implies current kept) (growth later)
  | @request β operation next state commit resume ih =>
    apply Safe.request
    · intro before value after kept later law
      obtain ⟨valid, grows⟩ := commit before value after (implies before kept) (growth later) law
      exact commits operation uses.1 before value after kept law valid grows
    · intro before value after kept later law
      exact ih before value after (implies before kept) (growth later) law (uses.2 value)

/-- The commit certificate remains necessary when `next = none`: an orphaned
request can still change durable storage. Saved replies need only certify their
own continuation; they do not repeat the operation when delivered. -/
def CallSafe (valid : Backend.State → Prop) (grows : Backend.State → Backend.State → Prop)
    (post : Nat → α → Backend.State → Prop) (call : Call α) (state : Backend.State) : Prop :=
  match call with
  | .pending owner operation next =>
    (∀ before value after, valid before → grows state before →
      Commits before operation value after → valid after ∧ grows before after) ∧
    (∀ before value after, valid before → grows state before →
      Commits before operation value after → ∀ rest, next = some rest →
      Safe valid grows (post owner.worker) (Program.ofArrs rest value) after)
  | .committed owner _ value next =>
    ∀ rest, next = some rest → Safe valid grows (post owner.worker) (Program.ofArrs rest value) state
  | .retired => True

theorem CallSafe.mono {post : Nat → α → Backend.State → Prop} {call state after}
    (safe : CallSafe valid grows post call state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c) (growth : grows state after) :
    CallSafe valid grows post call after := by
  cases call with
  | pending owner operation next =>
    exact ⟨fun current value final kept later law => safe.1 current value final kept (trans growth later) law,
      fun current value final kept later law rest same => safe.2 current value final kept (trans growth later) law rest same⟩
  | committed owner operation value next =>
    exact fun rest same => (safe rest same).mono trans growth
  | retired => trivial

theorem CallSafe.orphan {post : Nat → α → Backend.State → Prop} {call state}
    (safe : CallSafe valid grows post call state) (owner : Owner) :
    CallSafe valid grows post (call.orphan owner) state := by
  cases call with
  | pending caller operation next =>
    simp only [Call.orphan]
    split
    · exact ⟨safe.1, fun _ _ _ _ _ _ _ impossible => by cases impossible⟩
    · exact safe
  | committed caller operation value next =>
    simp only [Call.orphan]
    split
    · exact fun _ impossible => by cases impossible
    · exact safe
  | retired => trivial

private def AtEach {α : Type u} (items : Array α) (property : Nat → α → Prop) : Prop :=
  ∀ index value, items[index]? = some value → property index value

private theorem AtEach.set {α : Type u} {items : Array α} {property : Nat → α → Prop}
    (kept : AtEach items property) (index : Nat) (value : α) (safe : property index value) :
    AtEach (items.setIfInBounds index value) property := by
  intro other actual found
  rw [Array.getElem?_setIfInBounds] at found
  split at found
  · rename_i same
    subst other
    split at found
    · cases found; exact safe
    · cases found
  · exact kept other actual found

private theorem AtEach.push {α : Type u} {items : Array α} {property : Nat → α → Prop}
    (kept : AtEach items property) (value : α) (safe : property items.size value) :
    AtEach (items.push value) property := by
  intro index actual found
  rw [Array.getElem?_push] at found
  split at found
  · rename_i same
    subst index
    cases found
    exact safe
  · exact kept index actual found

private theorem AtEach.map {α : Type u} {β : Type v} {items : Array α}
    {property : Nat → α → Prop} {other : Nat → β → Prop}
    (kept : AtEach items property) (f : α → β)
    (preserved : ∀ index value, property index value → other index (f value)) :
    AtEach (items.map f) other := by
  intro index actual found
  rw [Array.getElem?_map] at found
  cases seen : items[index]? with
  | none => simp [seen] at found
  | some value =>
    simp only [seen, Option.map_some] at found
    cases found
    exact preserved index value (kept index value seen)

def WorkerSafe (valid : Backend.State → Prop) (grows : Backend.State → Backend.State → Prop)
    (post : Nat → α → Backend.State → Prop) (index : Nat) (worker : Worker α)
    (state : Backend.State) : Prop :=
  match worker.status with
  | .finished value => Safe valid grows (post index) (.pure value) state
  | _ => True

theorem WorkerSafe.mono {post : Nat → α → Backend.State → Prop} {index worker state after}
    (safe : WorkerSafe valid grows post index worker state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c) (growth : grows state after) :
    WorkerSafe valid grows post index worker after := by
  unfold WorkerSafe at safe ⊢
  cases seen : worker.status <;> simp only [seen] at safe ⊢ <;> try trivial
  exact Safe.mono safe trans growth

structure AllSafe (valid : Backend.State → Prop) (grows : Backend.State → Backend.State → Prop)
    (post : Nat → α → Backend.State → Prop) (state : Execution.State α) : Prop where
  services : valid state.services
  workers : ∀ index worker, state.workers[index]? = some worker →
    WorkerSafe valid grows post index worker state.services
  calls : ∀ (index : Nat) call, state.calls[index]? = some call → CallSafe valid grows post call state.services

variable {post : Nat → α → Backend.State → Prop}

theorem AllSafe.grow {state : Execution.State α} {after : Backend.State}
    (safe : AllSafe valid grows post state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : valid after) (growth : grows state.services after) :
    AllSafe valid grows post { state with services := after } :=
  ⟨kept, fun index worker found => (safe.workers index worker found).mono trans growth,
    fun index call found => (safe.calls index call found).mono trans growth⟩

theorem AllSafe.setCall {state : Execution.State α} (safe : AllSafe valid grows post state)
    (index : Nat) (call : Call α) (kept : CallSafe valid grows post call state.services) :
    AllSafe valid grows post { state with calls := state.calls.setIfInBounds index call } :=
  ⟨safe.services, safe.workers, AtEach.set safe.calls index call kept⟩

theorem AllSafe.activate {state : Execution.State α} (safe : AllSafe valid grows post state)
    (owner : Owner) (program : M α)
    (fresh : ProgramSafe valid grows (post owner.worker) program state.services) :
    AllSafe valid grows post (activate owner program state) := by
  cases program with
  | pure value =>
    exact ⟨safe.services, AtEach.set safe.workers owner.worker _ fresh, safe.calls⟩
  | impure operation next =>
    refine ⟨safe.services, AtEach.set safe.workers owner.worker _ trivial,
      AtEach.push safe.calls _ ?_⟩
    cases fresh with
    | request commit resume =>
      refine ⟨commit, ?_⟩
      intro before value after kept growth law rest same
      cases same
      exact resume before value after kept growth law

/-- Every legal abstract transition preserves the global invariant and all
remaining continuation obligations. In particular the commit case does not
require the issuing worker to be alive. -/
theorem Transition.safe {programs : Array (M α)} {action before after}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ index program, programs[index]? = some program → ∀ state,
      valid state → ProgramSafe valid grows (post index) program state)
    (transition : Transition programs action before after)
    (safe : AllSafe valid grows post before) :
    grows before.services after.services ∧ AllSafe valid grows post after := by
  cases transition with
  | @commit β before call owner operation next value services issued lawful =>
    have pending := safe.calls call _ issued
    obtain ⟨kept, growth⟩ := pending.1 before.services value services safe.services (refl _) lawful
    refine ⟨growth, (safe.grow trans kept growth).setCall call _ ?_⟩
    exact pending.2 before.services value services safe.services (refl _) lawful
  | @reply call before after executed =>
    simp only [Execution.step] at executed
    split at executed
    next β owner operation value next found =>
      have responding := safe.calls call _ found
      have retired := safe.setCall call .retired trivial
      cases next with
      | none =>
        simp only at executed
        cases executed
        exact ⟨refl _, retired⟩
      | some rest =>
        simp only at executed
        split at executed
        · cases executed
          refine ⟨by simpa only [activate_preserves] using refl before.services,
            retired.activate owner (ArrsF.apply rest value) ?_⟩
          change Safe valid grows _ (Program.ofEff (ArrsF.apply rest value)) _
          rw [Program.ofEff_apply]
          exact responding rest rfl
        · cases executed
    next => cases executed
  | @crash worker before after executed =>
    simp only [Execution.step] at executed
    split at executed
    next handle found =>
      split at executed
      · cases executed
        refine ⟨refl _, safe.services, AtEach.set safe.workers worker _ trivial, ?_⟩
        exact AtEach.map safe.calls _ (fun _ call kept => kept.orphan _)
      all_goals cases executed
    next => cases executed
  | @restart worker before after executed =>
    simp only [Execution.step] at executed
    split at executed
    next handle found =>
      split at executed
      next program entry =>
        split at executed
        · cases executed
          exact ⟨by simpa only [activate_preserves] using refl before.services,
            safe.activate _ program (fresh worker program entry before.services safe.services)⟩
        all_goals cases executed
      next => cases executed
    next => cases executed

theorem AllSafe.initial (programs : Array (M α)) (services : Backend.State)
    (kept : valid services)
    (fresh : ∀ index program, programs[index]? = some program → ∀ state,
      valid state → ProgramSafe valid grows (post index) program state) :
    AllSafe valid grows post (Execution.initial services programs) := by
  have fold (indices : List Nat) (state : Execution.State α)
      (safe : AllSafe valid grows post state) :
      AllSafe valid grows post (indices.foldl (fun current worker =>
        match programs[worker]? with
        | none => current
        | some program => Execution.activate ⟨worker, 0⟩ program current) state) := by
    induction indices generalizing state with
    | nil => exact safe
    | cons worker rest ih =>
      simp only [List.foldl_cons]
      cases seen : programs[worker]? with
      | none => exact ih state safe
      | some program => exact ih _ (safe.activate _ program (fresh worker program seen _ safe.services))
  apply fold
  refine ⟨kept, ?_, ?_⟩
  · exact AtEach.map (fun _ _ _ => trivial) _ (fun _ _ _ => trivial)
  · intro index call impossible
    simp at impossible

theorem AllSafe.returned {state : Execution.State α} (safe : AllSafe valid grows post state)
    (refl : ∀ current, grows current current) (index : Nat) (worker : Worker α) (value : α)
    (found : state.workers[index]? = some worker) (returned : worker.status = .finished value) :
    post index value state.services := by
  have result := safe.workers index worker found
  simp only [WorkerSafe, returned] at result
  cases result with
  | pure done => exact done state.services safe.services (refl _)

end LeanCloud.Backend.Proofs
