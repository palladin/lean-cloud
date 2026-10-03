import LeanCloud.Proofs.BackendScheduling

namespace LeanCloud.Backend.Proofs
open LeanEff Execution

/-- The worker's actual volatile continuation, normalized only for freer
association. The call identity remains part of the concrete execution state. -/
inductive Continues (owner : Owner) : Program α → Execution.State α → Prop where
  | pure {value state}
      (held : state.workers[owner.worker]? = some ⟨owner.attempt, .finished value⟩) :
      Continues owner (.pure value) state
  | request {β : Type} {operation : Request β} {next : ArrsF Request β α} {state id}
      (held : Waiting owner id operation next state) :
      Continues owner (.request operation (Program.ofArrs next)) state

theorem activate_continues (state : Execution.State α) (owner : Owner) (program : M α)
    (inside : owner.worker < state.workers.size) :
    Continues owner (Program.ofEff program) (activate owner program state) := by
  cases program with
  | pure value => exact .pure (by simp [activate, inside])
  | impure operation next =>
    exact .request (id := state.calls.size) ⟨by simp [activate, inside], by simp [activate]⟩

theorem Continues.request_view {owner : Owner} {operation : Request β} {next : β → Program α} {state}
    (held : Continues owner (.request operation next) state) :
    ∃ id, ∃ rest : ArrsF Request β α, Waiting owner id operation rest state ∧ Program.ofArrs rest = next := by
  cases held with
  | request waiting => exact ⟨_, _, waiting, rfl⟩

/-- Every certified finite computation finishes once its caller stops crashing
and service commits/replies are weakly fair. Interfering workers and orphaned
commits still follow the full shared service contracts. -/
theorem Safe.eventually_returns {programs : Array (M α)}
    (trace : Execution.Schedule programs) (fair : trace.WeaklyFair)
    {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : α → Backend.State → Prop}
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ time, valid (trace.states time).services)
    (growth : ∀ first last, first ≤ last → grows (trace.states first).services (trace.states last).services)
    {program state} (safe : Safe valid grows post program state)
    {owner : Owner} (time : Nat) (held : Continues owner program (trace.states time))
    (noCrash : trace.NoCrashesAfter owner.worker time)
    (prior : grows state (trace.states time).services) :
    ∃ later value, time ≤ later ∧
      (trace.states later).workers[owner.worker]? = some ⟨owner.attempt, .finished value⟩ ∧
      post value (trace.states later).services := by
  induction safe generalizing time with
  | pure done =>
    cases held with
    | pure present => exact ⟨time, _, Nat.le_refl _, present, done _ (kept time) prior⟩
  | request commit resume ih =>
    cases held with
    | @request β operation next _ id present =>
      obtain ⟨committedAt, afterCommit, waiting, event⟩ := trace.eventually_commit fair present noCrash
      obtain ⟨value, saved, law⟩ := waiting.committed (trace.execution committedAt _ event)
      have before := trans prior (growth time committedAt afterCommit)
      obtain ⟨repliedAt, afterReply, responding, reply⟩ := trace.eventually_reply fair saved
        (fun n beyond => noCrash n (by omega))
      have activated := responding.replied (trace.execution repliedAt _ reply)
      have inside := (Array.getElem?_eq_some_iff.mp responding.1).choose
      have continuing : Continues owner (Program.ofArrs next value) (trace.states (repliedAt + 1)) := by
        rw [activated, ← Program.ofEff_apply]
        exact activate_continues _ owner _ inside
      obtain ⟨finishedAt, returned, later, finished, result⟩ :=
        ih (trace.states committedAt).services value (trace.states (committedAt + 1)).services
          (kept committedAt) before law (repliedAt + 1) continuing
          (fun n beyond => noCrash n (by omega)) (growth _ _ (by omega))
      exact ⟨finishedAt, returned, by omega, finished, result⟩

theorem Safe.responding_returns {programs : Array (M α)}
    (trace : Execution.Schedule programs) (fair : trace.WeaklyFair)
    {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : α → Backend.State → Prop}
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ time, valid (trace.states time).services)
    (growth : ∀ first last, first ≤ last → grows (trace.states first).services (trace.states last).services)
    {owner : Owner} {id : Nat} {operation : Request β} {value : β} {next : ArrsF Request β α}
    {state} (safe : Safe valid grows post (Program.ofArrs next value) state)
    (time : Nat) (held : Responds owner id operation value next (trace.states time))
    (noCrash : trace.NoCrashesAfter owner.worker time)
    (prior : grows state (trace.states time).services) :
    ∃ later returned, time ≤ later ∧
      (trace.states later).workers[owner.worker]? = some ⟨owner.attempt, .finished returned⟩ ∧
      post returned (trace.states later).services := by
  obtain ⟨replyAt, beyond, responding, reply⟩ := trace.eventually_reply fair held noCrash
  have activated := responding.replied (trace.execution replyAt _ reply)
  have continuing : Continues owner (Program.ofArrs next value) (trace.states (replyAt + 1)) := by
    rw [activated, ← Program.ofEff_apply]
    exact activate_continues _ owner _ (Array.getElem?_eq_some_iff.mp responding.1).choose
  obtain ⟨later, returned, beyondReturn, finished, result⟩ := Safe.eventually_returns
    (valid := valid) (grows := grows) (post := post) trace fair (fun a b => trans a b) kept growth safe
    (replyAt + 1) continuing (fun n after => noCrash n (by omega))
    (trans prior (growth time (replyAt + 1) (by omega)))
  exact ⟨later, returned, by omega, finished, result⟩

end LeanCloud.Backend.Proofs
