import LeanCloud.Proofs.SharedProgress

/-! Eventual workflow completion from actual successful deliveries. Delivery
fairness concerns retained queue messages; structural progress is derived from
the original program and worker, not included in the fairness assumption. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter JournalDb ReplayRecovery ReplayInterpreter.Internal

/-- Observe the actual poll at the beginning of this attempt. This does not
assume that its subsequent worker step or publication succeeds. -/
def Trace.Selects {source blobs} (trace : Trace source blobs) (n : Nat) (location : Location) : Prop :=
  ∃ worker current, (queue.next ⟨(), none⟩).run (advanceState (trace.elapsed n) (trace.states n)) =
    (.ok (.item location, worker), current)

/-- Every retained location is eventually delivered unless the workflow has
already completed. For leased transport this includes eventual lease expiry
and continued fair polling; it assumes no worker progress or successful run. -/
def Trace.FairDelivery {source blobs} (trace : Trace source blobs) : Prop :=
  ∀ n location, LeasePublication.Pending (trace.states n).durable.2 location →
    (∃ later, n ≤ later ∧ (trace.states later).durable.2.completed ≠ none) ∨
      ∃ later, n ≤ later ∧ trace.Selects later location

/-- A delivered item in a successful iteration has the actual worker's
structural response and has published that response before acknowledgement. -/
theorem Trace.selected_published {source tree blobs} (trace : Trace source blobs)
    (expansion : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (n : Nat) (enough : sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states n).durable) {location completed}
    (selected : trace.Selects n location)
    (normal : trace.result n = .ok (.ok completed, (⟨(), none⟩ : Worker))) :
    ∃ node, ∃ _route : TreeRoute tree Location.root location node, ∃ response,
      StableResponse (trace.states n).durable.1 node location response (trace.states (n + 1)).durable.1 ∧
      ParentResponse (trace.states n).durable.1 location response ∧
      ResponseAvailable ((trace.states (n + 1)).durable.2.completed ≠ none)
        (LeasePublication.Pending (trace.states (n + 1)).durable.2) response := by
  obtain ⟨worker, current, polled⟩ := selected
  have checkedPoll := next_spec expansion (⟨(), none⟩ : Worker)
    (advanceState (trace.elapsed n) (trace.states n)) (valid_advance valid _)
  rw [polled] at checkedPoll
  obtain ⟨validNow, validPoll, ready⟩ := checkedPoll.2
  obtain ⟨node, route, activated, _⟩ := ready location rfl
  obtain ⟨_, receipt, message, delivered, held, _⟩ := validPoll.2
  obtain ⟨handle, delivery⟩ := worker
  cases handle
  change delivery = some (location, receipt) at delivered
  subst delivery
  have journalSame : current.durable.1 = (trace.states n).durable.1 := by
    have framed : ((queue.next ⟨(), none⟩).run (advanceState (trace.elapsed n) (trace.states n))).2.durable.1 =
        (trace.states n).durable.1 := by rw [queue_next]; rfl
    simpa only [polled] using framed
  have checked := step_complete_published expansion supported route current.durable validNow activated held
    comparable (sameExit location node route.member) blobs (trace.fuel n)
    (Nat.le_trans route.fuel_bound enough) current rfl
  have whole := trace.execution n
  rw [normal, iteration_eq, run_bind, polled] at whole
  dsimp only at whole
  rw [run_map] at whole
  generalize executed : ((do
    let response ← step workerDb blobs (trace.fuel n) (journalMap.program source) location
    queue.complete location response
    pure response : ExceptT CloudError (StateT Worker M) StepResult).run ⟨(), some (location, receipt)⟩).run current =
      observed at checked whole
  obtain ⟨result, final⟩ := observed
  cases result with
  | error crash => cases whole
  | ok value =>
    obtain ⟨response, rfl, advances, parent, published⟩ := checked.2
    have finalSame : final = trace.states (n + 1) := congrArg Prod.snd whole
    rw [finalSame, journalSame] at advances
    rw [journalSame] at parent
    rw [finalSame] at published
    exact ⟨node, route, response, advances, parent, published⟩

/-- Completed raw child slots or a completed cache always enable the parent
shortcut. A cache, if present, is bounded by the original program's outcome. -/
private theorem parent_readable {tree location node journal parent index outcome}
    (route : TreeRoute tree Location.root location node)
    (bounded : Extends journal (tree.journal Location.root))
    (linked : location.parent? = some (parent, index)) (completed : CompletedAt journal parent.key outcome) :
    ∃ recorded, JournalDb.get raw parent.key journal = (some (toJson (Result.completed recorded)), journal) := by
  obtain ⟨children, result, next, _, member, _⟩ := route.child_outcome linked
  have intended := (tree.fork_fields (by simp [Location.root]) member).2.1
  cases cached : journal (resultKey parent.key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans intended
    cases same
    exact ⟨_, get_completed _ _ _ cached⟩
  | none =>
    cases completed with
    | cached recorded => simp [cached] at recorded
    | group slots fork filled settled =>
      refine ⟨outcome, ?_⟩
      rw [get_fork journal parent.key slots cached fork (by
        intro i inside
        obtain ⟨value, same, recorded⟩ := filled i inside
        simpa only [same, Option.map_some] using recorded), settled]

/-- Full execution traces eventually record the direct program's outcome.
Finite crashes and journal stabilization are derived from the implementation;
the only delivery assumption selects retained work unless completion is already
durable. Duplicates and interrupted publication are allowed throughout. -/
theorem Trace.eventually_completed {source tree blobs} (trace : Trace source blobs)
    (expansion : Expansion source tree) (supported : PureProgram source)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable)
    (fair : trace.FairDelivery) : ∃ n, (trace.states n).durable.2.completed = some tree.exit := by
  classical
  have kept := trace.invariants expansion supported comparable sameExit enough valid covered
  apply Classical.byContradiction
  intro never
  have incomplete (n : Nat) : (trace.states n).durable.2.completed = none := by
    cases stored : (trace.states n).durable.2.completed with
    | none => rfl
    | some outcome =>
      have correct := (kept n).1.2.2.2 outcome stored
      exact False.elim (never ⟨n, stored.trans (congrArg some correct)⟩)
  obtain ⟨crashCut, normal⟩ := trace.after_last_crash expansion supported comparable sameExit enough valid covered
  obtain ⟨journalCut, stable⟩ := trace.journal_stable expansion supported comparable sameExit enough valid covered
  let cut := max crashCut journalCut
  let journal := (trace.states cut).durable.1
  let available := fun location => ∃ n, cut ≤ n ∧ trace.Selects n location
  have journalSame (n : Nat) (later : cut ≤ n) : (trace.states n).durable.1 = journal :=
    (stable n (by dsimp [cut] at later; omega)).trans (stable cut (by dsimp [cut]; omega)).symm
  have delivered (n : Nat) (later : cut ≤ n) (location : Location)
      (pending : LeasePublication.Pending (trace.states n).durable.2 location) : available location := by
    rcases fair n location pending with ⟨finished, _, done⟩ | ⟨selected, after, selectedAt⟩
    · exact False.elim (done (incomplete finished))
    · exact ⟨selected, Nat.le_trans later after, selectedAt⟩
  have responses (location : Location) (node : ExecutionTree) (member : (location, node) ∈ tree.nodes Location.root)
      (ready : available location) :
      StableAdvance journal available node location (BranchReported journal False node location) := by
    obtain ⟨n, later, selected⟩ := ready
    obtain ⟨completed, returned, _⟩ := normal n (by dsimp [cut] at later; omega)
    obtain ⟨actual, route, response, advances, _, published⟩ := trace.selected_published expansion supported
      comparable sameExit n (enough n) (kept n).1 selected returned
    have sameNode : actual = node := congrArg Prod.snd
      (tree.node_unique (by simp [Location.root]) route.member member rfl)
    subst actual
    have supplied : ResponseAvailable False available response := by
      cases response with
      | done outcome => exact published (incomplete (n + 1))
      | runnable locations =>
        exact fun next member => delivered (n + 1) (by omega) next (published next member)
    have result := advances ((journalSame (n + 1) (by omega)).trans (journalSame n later).symm) False available supplied
    simpa only [journalSame (n + 1) (by omega)] using result
  have parents (source parent : Location) (index : Nat) (outcome : Exit)
      (linked : source.parent? = some (parent, index)) (completed : CompletedAt journal parent.key outcome)
      (ready : available source) : available parent := by
    obtain ⟨n, later, selected⟩ := ready
    obtain ⟨finished, returned, _⟩ := normal n (by dsimp [cut] at later; omega)
    obtain ⟨node, route, response, _, parentResponse, published⟩ := trace.selected_published expansion supported
      comparable sameExit n (enough n) (kept n).1 selected returned
    have recorded : CompletedAt (trace.states n).durable.1 parent.key outcome := (journalSame n later) ▸ completed
    obtain ⟨value, view⟩ := parent_readable route (kept n).1.1 linked recorded
    rw [parentResponse parent index value linked view] at published
    exact delivered (n + 1) (by omega) parent (published parent (by simp))
  have represented := (kept cut).2
  change Coverage journal (LeasePublication.Pending (trace.states cut).durable.2) tree Location.root
    ((trace.states cut).durable.2.completed = some tree.exit) at represented
  have represented' := represented.mono_work (delivered cut (Nat.le_refl _))
  have unfinished : Coverage journal available tree Location.root False := by
    simpa only [incomplete cut, reduceCtorEq] using represented'
  exact unfinished.stable_complete (by simp [Location.root]) (fun _ h => h) rfl responses parents

/-- Once a final outcome is durable, polling reads it and skips dequeue.
Neither a lost read reply nor a return changes the durable backend. -/
theorem next_completed_reads (state : Durable) (worker : Worker) (outcome : Exit)
    (recorded : state.2.completed = some outcome) :
    Reads (queue.next worker) state (.completed outcome, (⟨(), none⟩ : Worker)) := by
  have component : Reads (LeasePublication.queue.next worker) state.2 (.completed outcome, (⟨(), none⟩ : Worker)) := by
    rw [LeasePublication.next_eq]
    apply (Reads.atomic (fun state : LeasePublication.Durable => state.completed) state.2).bind
    rw [recorded]
    exact Reads.pure _ _
  rw [queue_next]
  apply (component.withRight (· = state.1)).weaken
  · intro current same; subst current; exact ⟨rfl, rfl⟩
  · intro value current h
    exact ⟨h.2.1, Prod.ext h.1 h.2.2⟩
  · intro current h
    exact Prod.ext h.1 h.2

/-- The existing loop body returns a recorded outcome without reexecuting any
workflow command. Its single read may still crash and be retried. -/
theorem iteration_completed_reads (source : Cloud M Json) (blobs : BlobStorage Worker M)
    (state : Durable) (worker : Worker) (fuel : Nat) (outcome : Exit)
    (recorded : state.2.completed = some outcome) :
    Reads ((iteration workerDb blobs queue fuel source).run worker) state
      (.ok (some outcome), (⟨(), none⟩ : Worker)) := by
  rw [iteration_eq]
  exact (next_completed_reads state worker outcome recorded).bind (Reads.pure _ _)

theorem Trace.completed_persists {source blobs} (trace : Trace source blobs)
    {start : Nat} {outcome : Exit} (recorded : (trace.states start).durable.2.completed = some outcome)
    (stop : Nat) (later : start ≤ stop) : (trace.states stop).durable.2.completed = some outcome := by
  have step (n : Nat) (present : (trace.states n).durable.2.completed = some outcome) :
      (trace.states (n + 1)).durable.2.completed = some outcome := by
    have checked := iteration_completed_reads (journalMap.program source) blobs
      (advance (trace.elapsed n) (trace.states n).durable) ⟨(), none⟩ (trace.fuel n) outcome present
      (advanceState (trace.elapsed n) (trace.states n)) rfl
    rw [trace.execution n] at checked
    have same : (trace.states (n + 1)).durable = advance (trace.elapsed n) (trace.states n).durable := by
      cases observed : trace.result n with
      | error crash => rw [observed] at checked; exact checked.2.1
      | ok value => rw [observed] at checked; exact checked.2.2
    simpa only [same, advance] using present
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact recorded
  | succ offset ih => exact step (start + offset) (ih (by omega))

/-- Eventual durable completion is observable: after finitely many further
crashes an actual loop iteration returns that same outcome to its caller. -/
theorem Trace.eventually_returns {source tree blobs} (trace : Trace source blobs)
    (expansion : Expansion source tree) (supported : PureProgram source)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable)
    (fair : trace.FairDelivery) :
    ∃ n, trace.result n = .ok (.ok (some tree.exit), (⟨(), none⟩ : Worker)) := by
  obtain ⟨completedAt, recorded⟩ := trace.eventually_completed expansion supported comparable sameExit enough valid covered fair
  obtain ⟨crashCut, normal⟩ := trace.after_last_crash expansion supported comparable sameExit enough valid covered
  let n := max completedAt crashCut
  have present := trace.completed_persists recorded n (by dsimp [n]; omega)
  have checked := iteration_completed_reads (journalMap.program source) blobs
    (advance (trace.elapsed n) (trace.states n).durable) ⟨(), none⟩ (trace.fuel n) tree.exit present
    (advanceState (trace.elapsed n) (trace.states n)) rfl
  rw [trace.execution n] at checked
  obtain ⟨completed, returned, _⟩ := normal n (by dsimp [n]; omega)
  rw [returned] at checked
  exact ⟨n, returned.trans (congrArg Except.ok checked.2.1)⟩

end LeanCloud.Proofs.SharedRecovery
