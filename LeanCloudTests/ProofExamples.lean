import LeanCloud.Proofs.MainTheorems

/-! Checked applications of the public equivalence theorems to a workflow with captured
values, delayed pure execution, and nested parallel groups. -/

open Lean LeanEff LeanCloud LeanCloud.Proofs SimulationBackend
namespace LeanCloudTests.ProofExamples

private theorem bool_roundtrip : Pure.RoundTrips (inferInstance : Codec Bool) := by
  intro value
  cases value <;> rfl

private def child [Monad m] (captured : Bool) : Cloud m Bool :=
  .impure none .delay (.one fun _ => .pure none captured)

private theorem child_meaning [Monad m] (captured : Bool) : Pure.Evaluation (child (m := m) captured) (.ok captured) :=
  .delay _ (by simpa [ArrsF.apply, ArrsF.viewL] using Pure.Evaluation.pure (info := none) (m := m) captured)

private def nested [Monad m] (captured : Bool) : Cloud m Bool :=
  .impure none (.parallel (inferInstance : Codec Bool) 2
    (fun index => child (if index.val = 0 then captured else !captured)))
    (.one fun values => .pure none values[0]!)

private theorem nested_meaning [Monad m] (captured : Bool) : Pure.Evaluation (nested (m := m) captured) (.ok captured) := by
  apply Pure.Evaluation.parallelOk (outcomes := fun index => .ok (if index.val = 0 then captured else !captured))
    (values := #[captured, !captured])
  · exact bool_roundtrip
  · intro index
    exact child_meaning _
  · simp [Array.ofFn_succ, Array.mapM_eq_mapM_toList, List.mapM_cons] <;> rfl
  · simpa [ArrsF.apply, ArrsF.viewL] using Pure.Evaluation.pure (info := none) (m := m) captured

private def source [Monad m] (_ : Unit) : Cloud m Json :=
  .impure none (.command (inferInstance : Codec Bool) (.exec "captured" fun _ => pure true))
    (.one fun captured =>
      .impure none (.parallel (inferInstance : Codec Bool) 2
        (fun index => if index.val = 0 then nested captured else child (!captured)))
        (.one fun values => .pure none (toJson values)))

private theorem source_meaning [Monad m] : Pure.Evaluation (source (m := m) ()) (.ok (toJson #[true, false])) := by
  unfold source
  apply Pure.Evaluation.exec (body := fun _ => true)
  · rfl
  · simp only [ArrsF.apply, ArrsF.viewL]
    apply Pure.Evaluation.parallelOk (outcomes := fun index => .ok (if index.val = 0 then true else false))
      (values := #[true, false])
    · exact bool_roundtrip
    · intro index
      by_cases first : index.val = 0
      · simpa only [first, ite_true] using nested_meaning true
      · simpa only [first, ite_false, Bool.not_true] using child_meaning false
    · simp [Array.ofFn_succ, Array.mapM_eq_mapM_toList, List.mapM_cons] <;> rfl
    · simpa [ArrsF.apply, ArrsF.viewL] using Pure.Evaluation.pure (info := none) (m := m) (toJson #[true, false])

-- The same actual source is evaluated directly: no transformation or world.
example : (DirectInterpreter.interpret blobs source ()).run =
    EffF.pure none (.ok (toJson #[true, false])) :=
  PureDirect.evaluation_matches_direct blobs source_meaning

-- All actor starts and all valid traces, not a hand-selected scheduler path.
example (workers turns fuel duration : Nat)
    (final : Simulation.State World Unit (workers + 1))
    (history : SchedulerOwnership.Trace (start turns fuel duration source ()) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration source ())) final)
    (finished : final.world.scheduler.finished = true) :
    match final.world.records.lookup (ReplayStore.returnKey Location.root) with
    | none => False
    | some record =>
      (DirectInterpreter.interpret blobs source ()).run =
        EffF.pure none ((ReplayInterpreter.result (m := Id) (α := Json) record.outcome).run) :=
  completed_replay_matches_direct workers turns fuel duration source () ⟨_, source_meaning⟩
    (fun _ => rfl) final history finished

-- Completion is obtained from the public theorem, not assumed here.
example :
    ∃ sufficientFuel, ∀ workers turns fuel duration, sufficientFuel ≤ fuel →
      ∀ run : DeploymentProgress.Run (start (workers := workers) turns fuel duration source ()),
      DeploymentProgress.MakesProgress workers turns fuel duration source () run →
      ∃ index,
        (run.state index).world.scheduler.finished = true ∧
        (run.state index).world.records.lookup (ReplayStore.returnKey Location.root) =
          some ⟨ReplayStore.returnRequest, .success (toJson #[true, false])⟩ := by
  obtain ⟨bound, agrees⟩ := concurrent_replay_matches_direct source () ⟨_, source_meaning⟩ (fun _ => rfl)
  refine ⟨bound, ?_⟩
  intro workers turns fuel duration enough run progress
  obtain ⟨index, finished, _⟩ := agrees workers turns fuel duration enough run progress
  exact ⟨index, finished, ConcurrentSafety.completed_result workers turns fuel duration source ()
    source_meaning (run.reachable index) finished⟩

-- The basic theorem requires no trace, processing window, or populated journal.
example :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      ((LeanCloud.SequentialReplay.interpret ReplayModel.store ReplayModel.noBlobs fuel source ()).run []).1 =
        ((DirectInterpreter.interpret ReplayModel.noBlobs source ()).run []).1 :=
  sequential_replay_matches_direct source () ⟨_, source_meaning⟩ (fun _ => rfl)

end LeanCloudTests.ProofExamples

