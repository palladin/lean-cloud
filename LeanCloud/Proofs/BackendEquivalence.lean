import LeanCloud.Proofs.BackendLoop
import LeanCloud.Proofs.SimulationEvaluation

namespace LeanCloud.Backend.Proofs
open Lean LeanEff LeanCloud.Proofs

private theorem final_record (tree : ExecutionTree) (root : Location) :
    ∃ key, (key, toJson tree.exit) ∈ tree.records root := by
  cases tree with
  | terminal outcome => exact ⟨JournalDb.resultKey root.key, by simp [ExecutionTree.records,
      ExecutionTree.nodes, ExecutionTree.ownRecords, ExecutionTree.exit, ExecutionTree.outcome]⟩
  | delay next =>
    simpa only [ExecutionTree.records, ExecutionTree.nodes, ExecutionTree.exit, ExecutionTree.outcome] using final_record next root
  | fork children outcome next =>
    cases next with
    | none =>
      refine ⟨JournalDb.resultKey root.key, ?_⟩
      simp [ExecutionTree.records, ExecutionTree.nodes, ExecutionTree.ownRecords,
        ExecutionTree.exit, ExecutionTree.outcome]
    | some next =>
      obtain ⟨key, stored⟩ := final_record next root.next
      refine ⟨key, ?_⟩
      simp only [ExecutionTree.records, ExecutionTree.nodes, List.flatMap_cons,
        List.flatMap_append, List.mem_append]
      exact .inr (.inr stored)
termination_by sizeOf tree

theorem comparable_completion (tree : ExecutionTree)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root)) :
    (toJson tree.exit == toJson tree.exit) = true := by
  obtain ⟨key, stored⟩ := final_record tree Location.root
  exact comparable key _ (tree.journal_contains Location.root (by simp [Location.root]) _ stored)

namespace Worker

/-- Actual interpreter programs, one fuel budget per worker slot. -/
def attempts [Codec α] (program : ι → Cloud Replay.M α) (input : ι) (fuel : Array Nat) :
    Array (Backend.M (Except String (Except CloudError α × Replay.Worker))) :=
  fuel.map (fun budget => Replay.attempt budget program input)

theorem attempts_safe [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (fuel : Array Nat) (trace : Execution.Trace (attempts program input fuel))
    (initialized : trace.states 0 = Execution.initial Replay.initial (attempts program input fuel))
    (time : Nat) :
    Valid tree (trace.states time).services ∧
      ∀ (index : Nat) (worker : Execution.Worker (Except String (Except CloudError α × Replay.Worker))) returned,
        (trace.states time).workers[index]? = some worker →
        worker.status = .finished returned →
        ∃ actual handle, returned = .ok (actual, handle) ∧ Answers tree actual handle (trace.states time).services := by
  let post := fun (_ : Nat) (returned : Except String (Except CloudError α × Replay.Worker)) final =>
    ∃ actual handle, returned = .ok (actual, handle) ∧ Answers tree actual handle final
  have fresh (index : Nat) attempt (found : (attempts program input fuel)[index]? = some attempt)
      state (valid : Valid tree state) : ProgramSafe (Valid tree) Grows (post index) attempt state := by
    simp only [attempts, Array.getElem?_map] at found
    cases budget : fuel[index]? with
    | none => simp [budget] at found
    | some amount =>
      simp only [budget, Option.map_some] at found
      cases found
      exact run_checked whole (supported.map codec.encode) comparable sameExit
        (comparable_completion tree comparable) amount ⟨(), none⟩ state valid
  have initial : AllSafe (Valid tree) Grows post (trace.states 0) := by
    rw [initialized]
    exact AllSafe.initial _ _ (Valid.initial tree) fresh
  have safe := (trace_safe Grows.refl (fun a b => a.trans b) fresh trace initial time).2
  exact ⟨safe.services, fun index worker returned found done => safe.returned Grows.refl index worker returned found done⟩

end Worker

/-- Comparison assumptions concern only the serialization of workflow values.
They impose no workflow-specific obligation on the Db or queue. -/
def RecordedComparisons [codec : Codec α] (program : Cloud Replay.M α) : Prop :=
  ∀ tree, Expansion (codec.encode <$> program) tree →
    ReplayRecovery.Comparable (tree.journal Location.root) ∧
    ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true

theorem direct_expected [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    (law : CodecLaw codec) (blobs : BlobStorage σ Replay.M) {tree : ExecutionTree}
    (expansion : Expansion (codec.encode <$> program input) tree) :
    (DirectInterpreter.interpret blobs program input).run = pure (Worker.expected tree) := by
  obtain ⟨outcome, evaluated, encoded⟩ := expansion.evaluation.map_cases (program input) codec.encode
  have decoded : Worker.expected (α := α) tree = outcome := by
    unfold Worker.expected ExecutionTree.exit
    rw [encoded]
    cases outcome with
    | error error => rfl
    | ok value =>
      change (ReplayInterpreter.Internal.decode (m := Id) codec (codec.encode value)).run = .ok value
      simp only [ReplayInterpreter.Internal.decode, law value]
      rfl
  rw [decoded]
  exact evaluated.simulation blobs

theorem expected_exit [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    (law : CodecLaw codec) {tree : ExecutionTree}
    (expansion : Expansion (codec.encode <$> program input) tree) :
    (match Worker.expected (α := α) tree with
      | .ok value => Exit.success (codec.encode value)
      | .error error => .failure error) = tree.exit := by
  obtain ⟨outcome, _, encoded⟩ := expansion.evaluation.map_cases (program input) codec.encode
  unfold Worker.expected ExecutionTree.exit
  rw [encoded]
  cases outcome with
  | error error => rfl
  | ok value =>
    change (match (ReplayInterpreter.Internal.decode (m := Id) codec (codec.encode value)).run with
      | .ok value => Exit.success (codec.encode value)
      | .error error => .failure error) = Exit.success (codec.encode value)
    simp only [ReplayInterpreter.Internal.decode, law value]
    rfl

def encodedOutcome [codec : Codec α] : Except CloudError α → Exit
  | .ok value => .success (codec.encode value)
  | .error error => .failure error

def MatchesOrExhausted [Codec α] (expected : Except CloudError α)
    (returned : Except String (Except CloudError α × Replay.Worker)) (state : Backend.State) : Prop :=
  match returned with
  | .error _ => False
  | .ok (actual, _) =>
    (actual = expected ∧ Worker.completed state = some (toJson (encodedOutcome expected))) ∨
      actual = .error Worker.exhausted

/-- Safety for arbitrary contract-based executions, including orphaned commits,
post-acknowledgement duplicates and stale receipts. Fairness is not required.
The direct result is independent of every scheduling and recovery decision. -/
theorem concurrent_output_safety [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    (codecLaw : CodecLaw codec) (pureProgram : PureProgram (program input))
    (blobs : BlobStorage σ Replay.M) (comparisons : RecordedComparisons (program input)) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    ∃ expected : Except CloudError α, direct = pure expected ∧
      ∀ (fuel : Array Nat) (trace : Execution.Trace (Worker.attempts program input fuel)),
        trace.states 0 = Execution.initial Replay.initial (Worker.attempts program input fuel) →
        ∀ time,
          (∀ value, Worker.completed (trace.states time).services = some value →
            value = toJson (encodedOutcome expected)) ∧
          ∀ (index : Nat) (worker : Execution.Worker (Except String (Except CloudError α × Replay.Worker))) returned,
            (trace.states time).workers[index]? = some worker → worker.status = .finished returned →
            MatchesOrExhausted expected returned (trace.states time).services := by
  obtain ⟨tree, expansion⟩ := (pureProgram.map codec.encode).expansion
  obtain ⟨comparable, sameExit⟩ := comparisons tree expansion
  refine ⟨Worker.expected tree, direct_expected program input codecLaw blobs expansion, ?_⟩
  intro fuel trace initialized time
  have same : encodedOutcome (Worker.expected (α := α) tree) = tree.exit := expected_exit program input codecLaw expansion
  obtain ⟨valid, outputs⟩ := Worker.attempts_safe program input expansion pureProgram comparable sameExit fuel trace initialized time
  refine ⟨?_, ?_⟩
  · intro value stored
    rw [same]
    exact valid.completed value stored
  · intro index worker returned found done
    obtain ⟨actual, handle, rfl, result⟩ := outputs index worker returned found done
    simpa only [MatchesOrExhausted, Worker.Answers, same] using result

end LeanCloud.Backend.Proofs
