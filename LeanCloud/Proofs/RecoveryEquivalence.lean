import LeanCloud.Proofs.RestartExecution

/-! Public interpreter equivalence through finite crashes, using the physical
immutable journal and leased queue. Attempts are serialized; the environment
advances time and fairly delivers retained work. Only returned outcomes are
compared with direct evaluation, not durable state or operation histories. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

/-- Direct evaluation of the original program is a pure outcome. Replay returns
that same outcome from an empty journal, the root message, and any finite fault script.
The environment laws quantify over actual traces; neither completed replay nor
agreement with direct evaluation is assumed. JSON comparison reflexivity is
explicit because Lean's partial JSON comparison has no general proof instance. -/
theorem same_output [codec : Codec α]
    (program : ι → Cloud (CrashModel.M Journal) α) (input : ι)
    (law : CodecLaw codec) (supported : PureProgram (program input))
    (blobs : BlobStorage Worker M)
    (faults : Faults) (elapsed : State Durable → Nat)
    (comparison : ∀ tree, Expansion (codec.encode <$> program input) tree →
      ReplayRecovery.Comparable (tree.journal Location.root) ∧
      ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (fair : ∀ tree, Expansion (codec.encode <$> program input) tree →
      ∀ trace : Trace (codec.encode <$> program input) blobs,
        trace.states 0 = ⟨initial, faults⟩ → trace.Clocked elapsed →
        (∀ n, sizeOf tree ≤ trace.fuel n) → trace.FairDelivery) :
    ∃ outcome,
      (DirectInterpreter.interpret (noBlobs : BlobStorage Unit _) program input).run = pure outcome ∧
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ retryBound, ∀ retries, retryBound ≤ retries →
        let execution := LeanCloud.interpret workerDb blobs (clockedQueue elapsed) fuel
          (journalMap.program ∘ program) input
        let attempt := execution.run ⟨(), none⟩
        let (result, _) := (CrashM.restart retries attempt).run ⟨initial, faults⟩
        match result with
        | .ok (actual, _) => actual = outcome
        | .error _ => False := by
  obtain ⟨tree, expansion⟩ := (supported.map codec.encode).expansion
  obtain ⟨trace, start, clocked, budget⟩ := clocked_trace_exists (codec.encode <$> program input) blobs
    elapsed (sizeOf tree) ⟨initial, faults⟩
  obtain ⟨comparable, sameExit⟩ := comparison tree expansion
  have enough n : sizeOf tree ≤ trace.fuel n := by simp only [budget n, Nat.le_refl]
  have valid : Valid tree (trace.states 0).durable := by rw [start]; exact valid_initial tree
  have covered : Covered tree (trace.states 0).durable := by rw [start]; exact covered_initial tree
  obtain ⟨outcome, evaluated, encoded⟩ := expansion.evaluation.map_cases (program input) codec.encode
  refine ⟨outcome, evaluated.effect_free noBlobs, ?_⟩
  have decoded : ReplayModel.decodeExit (α := α) tree.exit = outcome := by
    unfold ExecutionTree.exit
    rw [encoded]
    cases outcome with
    | error error => rfl
    | ok value => exact ReplayModel.decodeExit_encoded law value
  obtain ⟨bound, recovered⟩ := trace.run_eventually_restart (α := α) expansion (supported.map codec.encode)
    comparable sameExit elapsed clocked enough valid covered (fair tree expansion trace start clocked enough)
  refine ⟨bound, ?_⟩
  intro fuel sufficient
  obtain ⟨final, retryBound, finished⟩ := recovered fuel sufficient
  refine ⟨retryBound, ?_⟩
  intro retries retryEnough
  have returned := finished retries retryEnough
  rw [start] at returned
  rw [BackendMap.program_map, decoded] at returned
  dsimp only [LeanCloud.interpret, Function.comp_def]
  rw [returned]

end LeanCloud.Proofs.SharedRecovery
