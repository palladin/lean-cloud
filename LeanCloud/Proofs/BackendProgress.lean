import LeanCloud.Proofs.BackendReconstruction

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalAdapter JournalDb ReplayRecovery


theorem Finished.grow {current outcome before after response initial final}
    (finished : Finished current outcome before response after)
    (earlier : Grows initial before) (later : Grows after final) :
    Finished current outcome initial response final := by
  refine ⟨finished.1.grow later, ?_⟩
  cases linked : current.parent? with
  | none => simpa only [linked] using finished.2
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    have notified : Notification parent index outcome before after response := by
      simpa only [linked] using finished.2
    simpa only [linked] using notified.grow earlier later

/-- What the selected command actually did. Checkpoints describe earlier
observations, while all published records remain present in the final state. -/
inductive CommandProgress (current : Location) (before : Backend.State) :
    ExecutionTree → StepResult → Backend.State → Prop where
  | finished {node response after} (recorded : Finished current node.exit before response after) :
      CommandProgress current before node response after
  | initialized {children result next count after} (size : children.length = count)
      (checked : Backend.State) (started : Grows before checked) (later : Grows checked after)
      (noResult : view checked (resultKey current.key) = none)
      (noFork : view checked (forkKey current.key) = none)
      (published : JournalAdapter.Published
        (records current.key (Result.settle (Array.replicate count none))) (view after)) :
      CommandProgress current before (.fork children result next)
        (.runnable (if count == 0 then #[current] else Array.ofFn fun i : Fin count => current.child i.val)) after
  | waiting {children result next count after} (size : children.length = count)
      (slots : Array (Option Exit)) (slotSize : slots.size = count)
      (checked : Backend.State) (started : Grows before checked) (later : Grows checked after)
      (incomplete : ∀ outcome, ¬ CompletedAt (view checked) current.key outcome)
      (settled : Result.settle slots = .suspended slots)
      (published : JournalAdapter.Published (records current.key (.suspended slots)) (view after)) :
      CommandProgress current before (.fork children result next)
        (.runnable ((Array.ofFn fun i : Fin count => i.val).filterMap fun i =>
          if slots[i]!.isNone then some (current.child i) else none)) after
  | joined {children value next after}
      (completed : CompletedAt (view after) current.key (.success value)) :
      CommandProgress current before (.fork children (.ok value) (some next)) (.runnable #[current.next]) after

theorem CommandProgress.grow {current before node response after initial final}
    (progress : CommandProgress current before node response after)
    (earlier : Grows initial before) (later : Grows after final) :
    CommandProgress current initial node response final := by
  cases progress with
  | finished recorded => exact .finished (recorded.grow earlier later)
  | initialized size checked started observed noResult noFork published =>
    exact .initialized size checked (earlier.trans started) (observed.trans later) noResult noFork
      (fun entry member => later _ _ (published entry member))
  | waiting size slots slotSize checked started observed incomplete settled published =>
    exact .waiting size slots slotSize checked (earlier.trans started) (observed.trans later) incomplete settled
      (fun entry member => later _ _ (published entry member))
  | joined completed => exact .joined (completed.grow later)

/-- A delivered location executes its command or wakes a completed ancestor.
The immediate-parent shortcut and reconstruction redirects are kept explicit. -/
inductive StepProgress (tree : ExecutionTree) (current : Location) (node : ExecutionTree)
    (before : Backend.State) (response : StepResult) (after : Backend.State) : Prop where
  | command (progress : CommandProgress current before node response after) :
      StepProgress tree current node before response after
  | redirect (redirected : Redirect tree Location.root current response after) :
      StepProgress tree current node before response after
  | parent (parent : Location) (index : Nat) (outcome : Exit)
      (linked : current.parent? = some (parent, index))
      (completed : CompletedAt (view after) parent.key outcome)
      (work : response = .runnable #[parent]) :
      StepProgress tree current node before response after

theorem StepProgress.grow {tree current node before response after initial final}
    (progress : StepProgress tree current node before response after)
    (earlier : Grows initial before) (later : Grows after final) :
    StepProgress tree current node initial response final := by
  cases progress with
  | command progress => exact .command (progress.grow earlier later)
  | redirect redirected => exact .redirect (redirected.grow later)
  | parent parent index outcome linked completed work =>
    exact .parent parent index outcome linked (completed.grow later) work

end LeanCloud.Backend.Proofs.Journal

