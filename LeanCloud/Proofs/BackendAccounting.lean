import LeanCloud.Proofs.BackendQueue
import LeanCloud.Proofs.BackendReports

namespace LeanCloud.Backend.Proofs.Accounting
open Lean LeanCloud.Proofs

/-- Every successor has a distinct later publication identity, allocated after
the replay response. It may already have been acknowledged by another worker. -/
def Issued (checkpoint : Backend.State) (location : Location) (final : Backend.State) : Prop :=
  ∃ (id : Nat) (message : Backend.Message),
    checkpoint.queue.messages.size ≤ id ∧ final.queue.messages[id]? = some message ∧
    message.location = location ∧ Journal.Grows checkpoint message.published.state

def Successors (checkpoint : Backend.State) (response : StepResult) (final : Backend.State) : Prop :=
  match response with
  | .done _ => True
  | .runnable locations => ∀ location ∈ locations, Issued checkpoint location final

theorem Issued.grow {checkpoint location before after}
    (issued : Issued checkpoint location before) (growth : Worker.Grows before after) :
    Issued checkpoint location after := by
  obtain ⟨id, message, fresh, stored, same, born⟩ := issued
  obtain ⟨current, stored, payload, birth, _⟩ := growth.queue.messages id message stored
  exact ⟨id, current, fresh, stored, payload.trans same, by simpa only [birth] using born⟩

theorem Successors.grow {checkpoint response before after}
    (published : Successors checkpoint response before) (growth : Worker.Grows before after) :
    Successors checkpoint response after := by
  cases response with
  | done _ => trivial
  | runnable locations =>
    exact fun location member => (published location member).grow growth

/-- Acknowledgement is justified by an actual replay response and prior durable
publication. Snapshots refer to primitive boundaries, not atomic workflow steps. -/
def Retired (tree : ExecutionTree) (id : Nat) (location : Location) (birth : DbSnapshot)
    (state : Backend.State) : Prop :=
  ∃ node before after response, ∃ _ : TreeRoute tree Location.root location node,
    Journal.Grows birth.state before ∧ Worker.Grows before after ∧ Worker.Grows after state ∧
    id < before.queue.messages.size ∧
    Worker.Valid tree after ∧ Journal.Emits tree response after ∧
    Journal.StepProgress tree location node before response after ∧
    Worker.FinalStored response state ∧ Successors after response state

theorem Retired.grow {tree id location birth before after}
    (retired : Retired tree id location birth before) (growth : Worker.Grows before after) :
    Retired tree id location birth after := by
  obtain ⟨node, start, finish, response, route, born, executed, later, inside, valid, emitted, progress, stored, successors⟩ := retired
  exact ⟨node, start, finish, response, route, born, executed, later.trans growth, inside,
    valid, emitted, progress, stored.grow growth, successors.grow growth⟩

structure Valid (tree : ExecutionTree) (state : Backend.State) : Prop where
  safety : Worker.Valid tree state
  retired : ∀ (id : Nat) (message : Backend.Message), state.queue.messages[id]? = some message →
    message.acknowledged = true → Retired tree id message.location message.published state

theorem Valid.initial (tree : ExecutionTree) : Valid tree Replay.initial := by
  refine ⟨Worker.Valid.initial tree, ?_⟩
  intro id message stored acknowledged
  have same : message = { location := Location.root } := by
    have := Array.mem_of_getElem? stored
    simpa [Replay.initial] using this
  subst message
  cases acknowledged

def Outstanding (state : Backend.State) : Prop :=
  ∃ (id : Nat) (message : Backend.Message), state.queue.messages[id]? = some message ∧
    message.acknowledged = false ∧ ¬ Journal.OpenReport message.location state state

private theorem report {tree final} (valid : Valid tree final)
    (unfinished : Worker.completed final ≠ some (toJson tree.exit))
    (noWork : ¬ Outstanding final) (id : Nat) (message : Backend.Message)
    (stored : final.queue.messages[id]? = some message) :
    Journal.OpenReport message.location message.published.state final := by
  cases acked : message.acknowledged with
  | false =>
    have reported : Journal.OpenReport message.location final final := by
      apply Classical.byContradiction
      intro absent
      exact noWork ⟨id, message, stored, acked, absent⟩
    exact reported.grow (valid.safety.published id message stored) (.refl _)
  | true =>
    obtain ⟨node, before, after, response, route, born, executed, later, inside,
      _afterValid, _emitted, progress, persisted, successors⟩ := valid.retired id message stored acked
    apply progress.open_report valid.safety.ordered born executed.journal later.journal
    · intro outcome same
      subst response
      have expected := valid.safety.completed (toJson outcome) persisted
      exact unfinished (persisted.trans (congrArg some expected))
    · intro locations same location member
      subst response
      obtain ⟨next, child, fresh, found, rfl, issued⟩ := successors location member
      have nextInside : next < final.queue.messages.size := (Array.getElem?_eq_some_iff.mp found).choose
      have newer : id < next := Nat.lt_of_lt_of_le inside (Nat.le_trans executed.queue.size fresh)
      exact (report valid unfinished noWork next child found).grow issued (.refl _)
termination_by final.queue.messages.size - id
decreasing_by omega

/-- Publication-before-acknowledgement and the join argument prevent loss of
all useful work. Fairness and termination are separate obligations. -/
theorem no_loss {tree final} (valid : Valid tree final)
    (root : ∃ message, final.queue.messages[0]? = some message ∧ message.location = Location.root) :
    Worker.completed final = some (toJson tree.exit) ∨ Outstanding final := by
  classical
  by_cases finished : Worker.completed final = some (toJson tree.exit)
  · exact .inl finished
  by_cases pending : Outstanding final
  · exact .inr pending
  obtain ⟨message, stored, same⟩ := root
  obtain ⟨parent, index, outcome, checked, linked, _⟩ := report valid finished pending 0 message stored
  rw [same] at linked
  exact False.elim (Location.ReportsTo.not_root linked)

end LeanCloud.Backend.Proofs.Accounting
