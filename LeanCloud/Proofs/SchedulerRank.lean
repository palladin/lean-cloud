import LeanCloud.Proofs.Traffic
import Init.Data.List.Nat.Sum
import Init.Data.List.Perm

/-! A finite progress measure for coordination. Attempts, deadlines, and worker
identities do not contribute: a retry cannot reset useful work. A live successful
report strictly increases the measure when its fork command is within the bound.
The source program must supply that bound and a bound on the number of jobs. -/

namespace LeanCloud.Proofs.SchedulerRank
open LeanCloud.Scheduler Internal

def command (location : Location) : Nat := location[location.size - 1]!.2

def phase (job : Job) : Nat :=
  if job.joining then 2 else match job.status with | .waiting _ => 1 | _ => 0

/-- Completion is above every unfinished phase. Clipping commands makes the
measure bounded even for arbitrary scheduler states; strict progress only uses
forks whose commands are within the supplied bound. -/
def score (limit : Nat) (job : Job) : Nat :=
  if job.status == .done then 3 * limit + 3 else min (3 * command job.location + phase job) (3 * limit + 2)

def rank (limit : Nat) (jobs : Array Job) : Nat := (jobs.toList.map (score limit)).sum

private theorem phase_le (job : Job) : phase job ≤ 2 := by
  unfold phase
  split
  · omega
  · cases job.status <;> simp

theorem score_le (limit : Nat) (job : Job) : score limit job ≤ 3 * limit + 3 := by
  have bound := phase_le job
  unfold score
  split <;> omega

theorem rank_le (limit : Nat) (jobs : Array Job) : rank limit jobs ≤ jobs.size * (3 * limit + 3) := by
  have bound : ∀ items : List Job, (items.map (score limit)).sum ≤ items.length * (3 * limit + 3) := by
    intro items
    induction items with
    | nil => simp
    | cons job jobs ih =>
      have this := score_le limit job
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      omega
  simpa only [rank, Array.length_toList] using bound jobs.toList

/-- A scheduler has exactly one row per branch, regardless of redelivery. -/
def Unique (jobs : Array Job) : Prop := (jobs.toList.map Job.branch).Nodup

theorem unique_initial : Unique ({} : State).jobs := by simp [Unique]

private theorem unique_mapped {jobs : Array Job} (valid : Unique jobs) (f : Job → Job)
    (same : ∀ job, (f job).branch = job.branch) : Unique (jobs.map f) := by
  simpa only [Unique, Array.toList_map, List.map_map, Function.comp_def, same] using valid

private theorem unique_replace {jobs : Array Job} (valid : Unique jobs) (index : Nat) (value : Job)
    (inside : index < jobs.size) (same : value.branch = jobs[index]!.branch) : Unique (jobs.set! index value) := by
  have shape : (jobs.set! index value).map Job.branch = jobs.map Job.branch := by
    apply Array.ext (by simp)
    intro position first last
    have insidePos : position < jobs.size := by simpa using last
    simp only [Array.getElem_map, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds insidePos]
    split
    next selected => subst position; simpa only [getElem!_pos jobs index inside] using same
    next => rfl
  unfold Unique
  rw [← Array.toList_map, shape]
  simpa only [Array.toList_map, Unique] using valid

private theorem unique_awaken (state : State) (valid : Unique state.jobs) : Unique (Internal.awaken state).jobs := by
  apply unique_mapped valid
  intro job
  cases job.status <;> simp only
  all_goals first | rfl | (split <;> rfl)

private theorem unique_children (jobs : Array Job) (children : Array Location) (valid : Unique jobs) :
    Unique (Internal.addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => Unique current) valid
  intro index current ih
  split
  · exact ih
  next missing =>
    have absent : children[index] ∉ current.toList.map Job.branch := by
      intro present
      obtain ⟨job, member, same⟩ := List.mem_map.mp present
      apply missing
      exact Array.any_eq_true'.mpr ⟨job, by simpa using member, by simpa only [beq_iff_eq] using same⟩
    simp only [Unique, Array.toList_push, List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro branch member other singleton same
    have selected : other = children[index] := List.mem_singleton.mp singleton
    exact absent ((same.trans selected) ▸ member)

private theorem unique_acquire (state : State) (worker : WorkerId) (duration : Nat) (valid : Unique state.jobs) :
    Unique (Internal.acquire state worker duration).1.jobs := by
  simp only [Internal.acquire]
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · split
        next index found => exact unique_replace valid index _ (Array.findIdx?_eq_some_iff_getElem.mp found).1 rfl
        next => exact valid

private theorem unique_accept (state : State) (report : Report) (valid : Unique state.jobs) :
    Unique (Internal.accept state report).jobs := by
  simp only [Internal.accept, Scheduler.observe_jobs]
  split
  next index found =>
    have inside := (Array.findIdx?_eq_some_iff_getElem.mp found).1
    cases report.progress with
    | error _ => exact valid
    | ok result =>
      cases result with
      | done => exact unique_awaken _ (unique_replace valid index _ inside rfl)
      | fork location count => exact unique_awaken _ (unique_children _ _ (unique_replace valid index _ inside rfl))
  next => simpa only [Id.run, pure, Scheduler.observe_jobs] using! valid

theorem unique_handle (state : State) (duration : Nat) (message : SchedulerMessage) (valid : Unique state.jobs) :
    Unique (Scheduler.handle duration state message).1.jobs := by
  cases message with
  | ready worker => exact unique_acquire (observe state worker #[]) worker duration (by simpa only [Scheduler.observe_jobs] using valid)
  | report report => exact unique_accept state report valid
  | inspect _ => exact valid
  | tick elapsed =>
    apply unique_mapped valid
    intro job
    cases job.status <;> simp only
    all_goals first | rfl | (split <;> rfl)

theorem unique_recover (state : State) (valid : Unique state.jobs) : Unique (Recovery.recovered state).jobs := by
  apply unique_mapped valid
  intro job
  cases job.status <;> rfl

/-- Finite possible branch keys bound the number of actual scheduler rows,
because insertion and all subsequent transitions preserve branch uniqueness. -/
theorem Unique.size_le {jobs : Array Job} (unique : Unique jobs) (keys : List String)
    (covered : ∀ job ∈ jobs, ReplayStore.returnKey job.branch ∈ keys) : jobs.size ≤ keys.length := by
  have distinct : (jobs.toList.map Job.branch |>.map ReplayStore.returnKey).Nodup := by
    apply List.pairwise_map.mpr
    exact unique.imp (fun different same => different (Location.return_key_injective same))
  have bounded := distinct.length_le_of_subset (l₂ := keys) (by
    intro key member
    obtain ⟨branch, branches, rfl⟩ := List.mem_map.mp member
    obtain ⟨job, jobs, rfl⟩ := List.mem_map.mp branches
    exact covered job (by simpa using jobs))
  simpa using bounded

private theorem command_bound (keys : List String) :
    ∃ limit, ∀ location, ReplayStore.valueKey location ∈ keys → command location ≤ limit := by
  classical
  induction keys with
  | nil => exact ⟨0, by simp⟩
  | cons key keys ih =>
    obtain ⟨limit, bounded⟩ := ih
    by_cases located : ∃ location, ReplayStore.valueKey location = key
    · obtain ⟨location, same⟩ := located
      refine ⟨max limit (command location), ?_⟩
      intro other member
      rcases List.mem_cons.mp member with first | rest
      · have equal := Location.value_key_injective (first.trans same.symm)
        subst other
        exact Nat.le_max_right _ _
      · exact Nat.le_trans (bounded other rest) (Nat.le_max_left _ _)
    · refine ⟨limit, ?_⟩
      intro location member
      rcases List.mem_cons.mp member with first | rest
      · exact False.elim (located ⟨location, first⟩)
      · exact bounded location rest

/-- A finite source journal bounds every possible fork command. The bound is
chosen before scheduling, and requires no parsing of runtime location strings. -/
theorem group_bound (expected : ReplayModel.Journal) :
    ∃ limit, ∀ location count, Specification.Group expected location count → command location ≤ limit := by
  obtain ⟨limit, bounded⟩ := command_bound (expected.map Prod.fst)
  refine ⟨limit, ?_⟩
  intro location count group
  obtain ⟨α, codec, outcomes, known, _⟩ := group
  apply bounded location
  have present : (expected.lookup (ReplayStore.valueKey location)).isSome := by simp [known]
  obtain ⟨entry, member, same⟩ := List.lookup_isSome_iff.mp present
  exact List.mem_map.mpr ⟨entry, member, (beq_iff_eq.mp same).symm⟩

private theorem sum_map_le (items : List α) (f g : α → Nat)
    (bounded : ∀ item ∈ items, f item ≤ g item) : (items.map f).sum ≤ (items.map g).sum := by
  induction items with
  | nil => exact Nat.le_refl _
  | cons item items ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bounded item (by simp)) (ih (fun value member => bounded value (by simp [member])))

private theorem mapped (limit : Nat) (jobs : Array Job) (f : Job → Job)
    (increases : ∀ job ∈ jobs, score limit job ≤ score limit (f job)) :
    rank limit jobs ≤ rank limit (jobs.map f) := by
  simpa only [rank, Array.toList_map, List.map_map, Function.comp_def] using
    sum_map_le jobs.toList (score limit) (fun job => score limit (f job))
      (fun job member => increases job (by simpa using member))

private theorem sum_set (items : List α) (f : α → Nat) (index : Nat) (value : α)
    (inside : index < items.length) :
    ((items.set index value).map f).sum + f items[index] = (items.map f).sum + f value := by
  induction items generalizing index with
  | nil => simp at inside
  | cons item items ih =>
    cases index with
    | zero => simp [Nat.add_comm, Nat.add_left_comm]
    | succ index =>
      have rest := ih index (by simpa using inside)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

private theorem replaced (limit : Nat) (jobs : Array Job) (index : Nat) (value : Job)
    (inside : index < jobs.size) :
    rank limit (jobs.set! index value) + score limit jobs[index]! = rank limit jobs + score limit value := by
  simpa [rank, getElem!_pos jobs index inside] using!
    sum_set jobs.toList (score limit) index value (by simpa using inside)

private theorem addChildren (limit : Nat) (jobs : Array Job) (children : Array Location) :
    rank limit jobs ≤ rank limit (Internal.addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => rank limit jobs ≤ rank limit current) (Nat.le_refl _)
  intro index current ih
  split
  · exact ih
  · simpa only [rank, Array.toList_push, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      using Nat.le_trans ih (Nat.le_add_right (rank limit current) _)

theorem awaken (limit : Nat) (state : State) : rank limit state.jobs ≤ rank limit (Internal.awaken state).jobs := by
  apply mapped
  intro job _
  cases status : job.status <;> simp only
  all_goals first | exact Nat.le_refl _ | skip
  split
  · have bound := phase_le job
    simp only [score, status, Scheduler.done_iff, reduceCtorEq, ite_false]
    change min (3 * command job.location + phase job) (3 * limit + 2) ≤
      min (3 * command job.location + 2) (3 * limit + 2)
    omega
  · exact Nat.le_refl _

theorem acquire (limit : Nat) (state : State) (worker : WorkerId) (duration : Nat) :
    rank limit state.jobs ≤ rank limit (Internal.acquire state worker duration).1.jobs := by
  simp only [Internal.acquire]
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · split
        next index found =>
          obtain ⟨inside, selected, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
          have pending : state.jobs[index]!.status = .pending := by
            rw [getElem!_pos state.jobs index inside]
            cases status : state.jobs[index].status <;>
              simp_all [BEq.beq, instBEqStatus.beq]
          have equal := replaced limit state.jobs index
            { state.jobs[index]! with status := .running worker state.nextAttempt (state.now + max 1 duration) } inside
          simp only [score, phase, pending] at equal
          simpa only [Id.run, pure] using Nat.le_of_eq (Nat.add_right_cancel equal).symm
        next => exact Nat.le_refl _

private theorem command_le {source target : Location} (follows : Routing.Follows source target)
    (same : Location.branchStart source = Location.branchStart target) : command source ≤ command target := by
  have size : source.size = target.size := by
    simpa [Location.branchStart] using congrArg Array.size same
  simpa only [command, size] using follows.command

private theorem command_lt {source target : Location} (follows : Routing.Follows source target)
    (same : Location.branchStart source = Location.branchStart target) (different : target ≠ source) :
    command source < command target := by
  have le := command_le follows same
  by_cases smaller : command source < command target
  · exact smaller
  have equal : command source = command target := by omega
  have size : source.size = target.size := by simpa [Location.branchStart] using congrArg Array.size same
  apply False.elim
  apply different
  apply Routing.Follows.antisymm (b := follows)
  refine ⟨by have := follows.nonempty; omega, Nat.le_of_eq size.symm, ?_, ?_, ?_⟩
  · intro index inside
    exact (follows.ancestry index (by omega)).symm
  · simpa only [size] using follows.branch.symm
  · simpa only [command, size] using Nat.le_of_eq equal.symm

private theorem fork_increases (limit : Nat) (job : Job) (worker : WorkerId) (attempt deadline : Nat)
    (location : Location) (children : Array Location)
    (running : job.status = .running worker attempt deadline)
    (branch : Location.branchStart job.location = Location.branchStart location)
    (forward : Routing.Follows job.location location)
    (joining : job.joining = true → location ≠ job.location) (bounded : command location ≤ limit) :
    score limit job < score limit { job with location, joining := false, status := .waiting children } := by
  have le := command_le forward branch
  have old : command job.location ≤ limit := Nat.le_trans le bounded
  cases joined : job.joining with
  | false => simp [score, phase, running, joined, Scheduler.done_iff]; omega
  | true =>
    have strict := command_lt forward branch (joining joined)
    simp [score, phase, running, joined, Scheduler.done_iff]
    omega

private theorem fork_nondecreasing (limit : Nat) (job : Job) (worker : WorkerId) (attempt deadline : Nat)
    (location : Location) (children : Array Location)
    (running : job.status = .running worker attempt deadline)
    (branch : Location.branchStart job.location = Location.branchStart location)
    (forward : Routing.Follows job.location location)
    (joining : job.joining = true → location ≠ job.location) :
    score limit job ≤ score limit { job with location, joining := false, status := .waiting children } := by
  have le := command_le forward branch
  cases joined : job.joining with
  | false => simp [score, phase, running, joined, Scheduler.done_iff]; omega
  | true =>
    have strict := command_lt forward branch (joining joined)
    simp [score, phase, running, joined, Scheduler.done_iff]
    omega

/-- Correct reports never undo progress. Errors and stale reports leave jobs
alone; successful reports advance the selected job and may awaken its parent. -/
theorem accept {m : Type → Type u} (limit : Nat) (state : State) (report : Report)
    (expected journal : ReplayModel.Journal) (encode : α → Lean.Json) (program : Cloud m α)
    (groups : SchedulerGroups.Valid expected journal state.jobs)
    (valid : Traffic.ToScheduler encode program expected state journal (.report report)) :
    rank limit state.jobs ≤ rank limit (Internal.accept state report).jobs := by
  simp only [Internal.accept, Scheduler.observe_jobs]
  split
  next index found =>
    obtain ⟨member, deadline, running⟩ := Scheduler.report_job state report index found
    have inside := (Array.findIdx?_eq_some_iff_getElem.mp found).1
    cases progress : report.progress with
    | error _ => exact Nat.le_refl _
    | ok result =>
      cases result with
      | done =>
        dsimp only [Id.run, pure]
        apply Nat.le_trans (m := rank limit (state.jobs.set! index { state.jobs[index]! with status := .done }))
        · have changed := replaced limit state.jobs index { state.jobs[index]! with status := .done } inside
          have bounded := score_le limit state.jobs[index]!
          have completed : score limit { state.jobs[index]! with status := .done } = 3 * limit + 3 := by
            simp [score, Scheduler.done_iff]
          rw [completed] at changed
          omega
        · exact awaken limit { observe state report.worker report.recorded with
            jobs := state.jobs.set! index { state.jobs[index]! with status := .done } }
      | fork location count =>
        have branch := (valid.2.2.1 _ member deadline location count running progress).1
        obtain ⟨forward, joining⟩ := valid.2.2.2.2 _ member deadline location count running progress
        let children := (Array.range count).map location.child
        let updated := { state.jobs[index]! with location, joining := false, status := .waiting children }
        dsimp only [Id.run, pure]
        apply Nat.le_trans (m := rank limit (Internal.addChildren (state.jobs.set! index updated) children))
        · apply Nat.le_trans (m := rank limit (state.jobs.set! index updated))
          · have changed := replaced limit state.jobs index updated inside
            have advances := fork_nondecreasing limit state.jobs[index]! report.worker report.attempt deadline location
              children running ((groups _ member).branch.symm.trans branch) forward joining
            change score limit state.jobs[index]! ≤ score limit updated at advances
            omega
          · exact addChildren limit _ _
        · exact awaken limit { observe state report.worker report.recorded with
            jobs := Internal.addChildren (state.jobs.set! index updated) children }
  next => simpa only [Id.run, pure, Scheduler.observe_jobs] using! Nat.le_refl (rank limit state.jobs)

theorem handle {m : Type → Type u} (limit : Nat) (state : State) (duration : Nat) (message : SchedulerMessage)
    (expected journal : ReplayModel.Journal) (encode : α → Lean.Json) (program : Cloud m α)
    (groups : SchedulerGroups.Valid expected journal state.jobs)
    (valid : Traffic.ToScheduler encode program expected state journal message) :
    rank limit state.jobs ≤ rank limit (Scheduler.handle duration state message).1.jobs := by
  cases message with
  | ready worker => simpa only [Scheduler.observe_jobs] using! acquire limit (observe state worker #[]) worker duration
  | report report => exact accept limit state report expected journal encode program groups valid
  | inspect _ => exact Nat.le_refl _
  | tick elapsed =>
    apply mapped
    intro job _
    cases status : job.status <;> simp only
    all_goals first | exact Nat.le_refl _ | skip
    split
    · simp [score, phase, status, Scheduler.done_iff]
    · exact Nat.le_refl _

theorem recover (limit : Nat) (state : State) :
    rank limit state.jobs ≤ rank limit (Recovery.recovered state).jobs := by
  apply mapped
  intro job _
  cases status : job.status <;> simp [score, phase, status, Scheduler.done_iff]

/-- Every accepted successful report makes strict durable coordination progress.
The fork facts are proved for worker execution and retained by durable transport.
No bound on retries or failed deliveries is assumed by this local theorem. -/
theorem accept_increases (limit : Nat) (state : State) (report : Report) (job : Job) (deadline : Nat)
    (valid : SchedulerAssignments.Valid state) (member : job ∈ state.jobs)
    (running : job.status = .running report.worker report.attempt deadline)
    (success : report.progress.isOk = true)
    (branch : job.branch = Location.branchStart job.location)
    (forked : ∀ location count, report.progress = .ok (.fork location count) →
      job.branch = Location.branchStart location ∧ Routing.Follows job.location location ∧
        (job.joining = true → location ≠ job.location) ∧ command location ≤ limit) :
    rank limit state.jobs < rank limit (Internal.accept state report).jobs := by
  obtain ⟨index, found, selected⟩ := SchedulerAssignments.live_report_selects state report job deadline valid member running
  have inside := (Array.findIdx?_eq_some_iff_getElem.mp found).1
  simp only [Internal.accept, Scheduler.observe_jobs]
  erw [found]
  cases progress : report.progress with
  | error error => rw [progress] at success; cases success
  | ok result =>
    cases result with
    | done =>
      dsimp only [Id.run, pure]
      simp only [selected]
      apply Nat.lt_of_lt_of_le (m := rank limit (state.jobs.set! index { job with status := .done }))
      · have changed := replaced limit state.jobs index { job with status := .done } inside
        have less : score limit job < 3 * limit + 3 := by
          have phaseBound := phase_le job
          simp only [score, running] 
          simp only [BEq.beq, instBEqStatus.beq, Bool.false_eq_true, ite_false]
          omega
        have completed : score limit { job with status := .done } = 3 * limit + 3 := by
          simp [score, Scheduler.done_iff]
        rw [selected, completed] at changed
        omega
      · exact awaken limit { observe state report.worker report.recorded with jobs := state.jobs.set! index { job with status := .done } }
    | fork location count =>
      obtain ⟨sameBranch, forward, joining, bounded⟩ := forked location count progress
      dsimp only [Id.run, pure]
      simp only [selected]
      let children := (Array.range count).map location.child
      let updated := { job with location, joining := false, status := .waiting children }
      apply Nat.lt_of_lt_of_le (m := rank limit (Internal.addChildren (state.jobs.set! index updated) children))
      · apply Nat.lt_of_lt_of_le (m := rank limit (state.jobs.set! index updated))
        · have changed := replaced limit state.jobs index
            { state.jobs[index]! with location, joining := false, status := .waiting ((Array.range count).map location.child) } inside
          have strict := fork_increases limit job report.worker report.attempt deadline location
            ((Array.range count).map location.child) running (branch.symm.trans sameBranch) forward joining bounded
          simp only [selected] at changed
          change rank limit state.jobs < rank limit (state.jobs.set! index
            { job with location, joining := false, status := .waiting ((Array.range count).map location.child) })
          omega
        · exact addChildren limit _ _
      · exact awaken limit { observe state report.worker report.recorded with jobs := Internal.addChildren (state.jobs.set! index updated) children }

end LeanCloud.Proofs.SchedulerRank
