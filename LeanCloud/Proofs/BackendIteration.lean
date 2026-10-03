import LeanCloud.Proofs.BackendHandoff
import LeanCloud.Proofs.BackendEquivalence
import LeanCloud.Proofs.ReplayIteration

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs Accounting

abbrev Outcome := Except String (Except CloudError (Option Exit) × Replay.Worker)

def afterPoll (traversal : Nat) (program : Cloud Replay.M Json) :
    Work → ExceptT CloudError (StateT Replay.Worker Replay.M) (Option Exit)
  | .idle => pure none
  | .completed outcome => pure (some outcome)
  | .item location => do
    let response ← ReplayInterpreter.Internal.step Replay.db Replay.noBlobs traversal program location
    Replay.queue.complete location response
    pure (match response with | .done outcome => some outcome | .runnable _ => none)

def program (traversal : Nat) (source : Cloud Replay.M Json) : Backend.M Outcome :=
  ((ReplayIteration.iteration Replay.db Replay.noBlobs Replay.queue traversal source).run ⟨(), none⟩).run

def again : Outcome → Bool
  | .ok (.ok none, _) => true
  | _ => false

def Returned (tree : ExecutionTree) (actual : Except CloudError (Option Exit))
    (worker : Replay.Worker) (state : Backend.State) : Prop :=
  ∃ outcome, actual = .ok outcome ∧ worker = ⟨(), none⟩ ∧
    ∀ value, outcome = some value → value = tree.exit ∧ Worker.completed state = some (toJson value)

def Published (tree : ExecutionTree) (location : Location) (node : ExecutionTree)
    (before : Backend.State) (response : StepResult) (final : Backend.State) : Prop :=
  ∃ after, Worker.Grows before after ∧ Worker.Grows after final ∧ Worker.Valid tree after ∧
    Journal.StepProgress tree location node before response after ∧ Journal.Emits tree response after ∧
    Worker.FinalStored response final ∧ Successors after response final

theorem Published.grow {tree location node before response current final}
    (published : Published tree location node before response current)
    (growth : Worker.Grows current final) : Published tree location node before response final := by
  obtain ⟨after, first, last, valid, progress, emitted, stored, successors⟩ := published
  exact ⟨after, first, last.trans growth, valid, progress, emitted, stored.grow growth, successors.grow growth⟩

theorem selected_checked {source : Cloud Replay.M Json} {tree location node}
    (whole : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root location node)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true)
    (traversal : Nat) (enough : route.prefixSteps + 1 ≤ traversal)
    (receipt : Receipt) (before : Backend.State) (valid : Accounting.Valid tree before)
    (active : route.Activated (Journal.view before)) (received : Worker.Received location receipt before) :
    Accounting.Checked tree ((afterPoll traversal source (.item location)).run)
      (fun actual worker final => Returned tree actual worker final ∧
        ∃ response, Published tree location node before response final)
      ⟨(), some (location, receipt)⟩ before := by
  have stepped : Accounting.Checked tree
      ((ReplayInterpreter.Internal.step Replay.db Replay.noBlobs traversal source location).run)
      (fun actual worker final => ∃ response, actual = .ok response ∧
        worker = ⟨(), some (location, receipt)⟩ ∧ Journal.Emits tree response final ∧
        Journal.StepProgress tree location node before response final)
      ⟨(), some (location, receipt)⟩ before := by
    apply Safe.weaken (step_checked whole supported route comparable sameExit before valid active traversal enough _)
    intro returned final kept result
    obtain ⟨response, rfl, emitted, progress⟩ := result
    exact ⟨.ok response, _, rfl, response, rfl, rfl, emitted, progress⟩
  unfold afterPoll
  apply Worker.Checked.bind stepped valid
  intro actual worker after kept growth result
  obtain ⟨response, rfl, rfl, emitted, progress⟩ := result
  apply Worker.Checked.bind (Worker.Checked.except
    (complete_published_checked (comparable_completion tree comparable) location receipt response route
      before after valid.safety growth received progress kept emitted)
    (ε := CloudError) kept (fun _ _ _ _ later done =>
      ⟨done.1, done.2.1.grow later, done.2.2.grow later⟩)) kept
  intro actual worker final bounded later result
  obtain ⟨value, rfl, rfl, stored, successors⟩ := result
  apply Worker.checked_pure
  intro last lastValid extended
  refine ⟨?_, response, ⟨after, growth, later.trans extended, kept.safety, progress,
    emitted, stored.grow extended, successors.grow extended⟩⟩
  cases response with
  | runnable locations => exact ⟨none, rfl, rfl, by intro value impossible; cases impossible⟩
  | done outcome =>
    exact ⟨some outcome, rfl, rfl, by
      intro value equal
      cases equal
      exact ⟨emitted, extended.completed _ stored⟩⟩

theorem checked {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (state : Backend.State) (valid : Accounting.Valid tree state) :
    ProgramSafe (Accounting.Valid tree) Worker.Grows
      (fun returned final => ∃ actual worker, returned = .ok (actual, worker) ∧ Returned tree actual worker final)
      (program traversal source) state := by
  change Accounting.Checked tree
    ((ReplayIteration.iteration Replay.db Replay.noBlobs Replay.queue traversal source).run)
      (Returned tree) ⟨(), none⟩ state
  unfold ReplayIteration.iteration
  apply Worker.Checked.bind (Worker.Checked.except (Accounting.next_checked tree _ state valid)
    (ε := CloudError) valid (fun _ _ _ _ growth next => next.grow growth)) valid
  intro actual handle polled kept growth done
  obtain ⟨work, rfl, next⟩ := done
  cases work with
  | idle =>
    have clean : handle = ⟨(), none⟩ := by cases handle; simp_all [Worker.Next]
    exact .pure fun _ _ _ => ⟨.ok none, handle, rfl, none, rfl, clean, by intro _ impossible; cases impossible⟩
  | completed outcome =>
    have clean : handle = ⟨(), none⟩ := by cases handle; simp_all [Worker.Next]
    exact .pure fun final bounded later => ⟨.ok (some outcome), handle, rfl,
      some outcome, rfl, clean, by intro value equal; cases equal; exact ⟨next.2.1, later.completed _ next.2.2⟩⟩
  | item location =>
    obtain ⟨receipt, held, ⟨node, route, active⟩, received⟩ := next
    cases handle with
    | mk backend delivery =>
      cases backend
      dsimp only at held
      subst delivery
      exact Worker.Checked.weaken
        (selected_checked whole supported route comparable (sameExit _ _ route.member) traversal
          (Nat.le_trans route.fuel_bound enough) receipt polled kept active received)
        (fun _ _ _ result => result.1)

end LeanCloud.Backend.Proofs.Iteration
