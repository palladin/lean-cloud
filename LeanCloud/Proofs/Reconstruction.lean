import LeanCloud.Proofs.ReplayModel
import LeanCloud.Proofs.Routing

namespace LeanCloud.Proofs.Reconstruction
open Lean LeanEff ReplayModel ReplayInterpreter Routing

variable {info : Option SourceSiteId}

/-- At the assigned location, the next worker instruction is active. -/
theorem walk_at_assignment [Monad m] (store : ReplayStore m) (blobs : BlobStorage m)
    (assignment : Assignment) (fuel : Nat) (encode : α → Json) (program : Cloud m α) :
    walk store blobs assignment fuel encode program assignment.location false =
      walk store blobs assignment fuel encode program assignment.location true := by
  cases fuel <;> simp only [walk, Bool.false_or, Bool.true_or, beq_self_eq_true]

/-- A recorded prefix leads to the assigned typed continuation. Descending into
an array child selects its codec; ordinary continuation steps retain the current
encoder. No encoding computation is appended to the Cloud program. -/
inductive Prefix {m : Type → Type u} (journal : Journal) (target : Location) :
    {α β : Type} → (α → Json) → Cloud m α → Location → Nat → (β → Json) → Cloud m β → Prop where
  | here (encode : α → Json) (program : Cloud m α) :
      Prefix journal target encode program target 0 encode program
  | delay {info : Option SourceSiteId} {encode : α → Json} {remainingEncode : β → Json} {remaining : Cloud m β} {current steps}
      (next : ArrsF (Control m) SourceSiteId Unit α) (before : current ≠ target)
      (rest : Prefix journal target encode (next.apply ()) current steps remainingEncode remaining) :
      Prefix journal target encode (.impure info .delay next) current (steps + 1) remainingEncode remaining
  | command {info : Option SourceSiteId} {encode : β → Json} {remainingEncode : γ → Json} {remaining : Cloud m γ} {current steps}
      (codec : Codec α) (operation : Operation m α) (next : ArrsF (Control m) SourceSiteId α β)
      (record : ReplayRecord) (wire : Json) (value : α)
      (before : current ≠ target)
      (present : journal.lookup (ReplayStore.valueKey current) = some record)
      (checked : (record.request == Internal.request codec operation) = true)
      (success : record.outcome = .success wire) (decoded : codec.decode wire = .ok value)
      (rest : Prefix journal target encode (next.apply value) current.next steps remainingEncode remaining) :
      Prefix journal target encode (.impure info (.command codec operation) next) current (steps + 1)
        remainingEncode remaining
  | joined {info : Option SourceSiteId} {encode : β → Json} {remainingEncode : γ → Json} {remaining : Cloud m γ} {current steps}
      (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) SourceSiteId (Array α) β) (record : ReplayRecord) (wire : Json) (values : Array α)
      (before : current ≠ target) (skip : current.entersChild target = false)
      (present : journal.lookup (ReplayStore.valueKey current) = some record)
      (checked : (record.request == ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩) = true)
      (success : record.outcome = .success wire)
      (decoded : (@instCodecArray α codec).decode wire = .ok values) (size : values.size = count)
      (rest : Prefix journal target encode (next.apply values) current.next steps remainingEncode remaining) :
      Prefix journal target encode (.impure info (.parallel codec count branches) next) current (steps + 1)
        remainingEncode remaining
  | child {info : Option SourceSiteId} {encode : β → Json} {remainingEncode : γ → Json} {remaining : Cloud m γ} {current steps}
      (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) SourceSiteId (Array α) β) (index : Fin count) (before : current ≠ target)
      (enters : current.entersChild target = true) (selected : target[current.size]!.1 = index.val)
      (rest : Prefix journal target codec.encode (branches index) (current.child index) steps remainingEncode remaining) :
      Prefix journal target encode (.impure info (.parallel codec count branches) next) current (steps + 1)
        remainingEncode remaining

/-- Other workers may add records without changing this reconstruction path. -/
theorem Prefix.extend {m : Type → Type u} {before after : Journal}
    {target current steps} {encode : α → Json} {program : Cloud m α}
    {remainingEncode : β → Json} {remaining : Cloud m β}
    (witness : Prefix before target encode program current steps remainingEncode remaining)
    (extension : Extends before after) : Prefix after target encode program current steps remainingEncode remaining := by
  induction witness with
  | here encode program => exact .here encode program
  | delay next earlier rest ih => exact .delay next earlier ih
  | command codec operation next record wire value earlier present checked success decoded rest ih =>
    exact .command codec operation next record wire value earlier (extension _ _ present)
      checked success decoded ih
  | joined codec count branches next record wire values earlier skip present checked success decoded size rest ih =>
    exact .joined codec count branches next record wire values earlier skip (extension _ _ present)
      checked success decoded size ih
  | child codec count branches next index earlier enters selected rest ih =>
    exact .child codec count branches next index earlier enters selected ih

/-- Reconstruction retains the source's ancestry and cannot move backwards
within a branch. The proof applies to the existing array-based locations. -/
theorem Prefix.follows {m : Type → Type u} {journal : Journal}
    {target current steps} {encode : α → Json} {program : Cloud m α}
    {remainingEncode : β → Json} {remaining : Cloud m β}
    (witness : Prefix journal target encode program current steps remainingEncode remaining)
    (nonempty : 0 < current.size) : Follows current target := by
  induction witness with
  | here encode program => exact .refl _ nonempty
  | delay next before rest ih => exact ih nonempty
  | command codec operation next record wire value before present checked success decoded rest ih =>
    exact (next_follows _ nonempty).trans (ih (by simpa [LeanCloud.Location.next] using nonempty))
  | joined codec count branches next record wire values before skip present checked success decoded size rest ih =>
    exact (next_follows _ nonempty).trans (ih (by simpa [LeanCloud.Location.next] using nonempty))
  | child codec count branches next index before enters selected rest ih =>
    exact (child_follows _ nonempty index).trans (ih (by simp [LeanCloud.Location.child]))

/-- Continuing a recorded path to a later command or nested child preserves all
earlier routing decisions. The combined path reconstructs from the same source. -/
theorem Prefix.append {m : Type → Type u} {journal : Journal}
    {target destination current steps tailSteps} {encode : α → Json} {program : Cloud m α}
    {remainingEncode : β → Json} {remaining : Cloud m β}
    {finalEncode : γ → Json} {final : Cloud m γ}
    (witness : Prefix journal target encode program current steps remainingEncode remaining)
    (suffix : Prefix journal destination remainingEncode remaining target tailSteps finalEncode final)
    (nonempty : 0 < current.size) :
    Prefix journal destination encode program current (steps + tailSteps) finalEncode final := by
  induction witness with
  | here encode program => simpa using suffix
  | delay next before rest ih =>
    have earlier := rest.follows nonempty
    have later := suffix.follows (Nat.lt_of_lt_of_le nonempty earlier.depth)
    simpa only [Nat.add_right_comm _ 1 tailSteps] using
      Prefix.delay next (different_follows earlier later before) (ih suffix nonempty)
  | command codec operation next record wire value before present checked success decoded rest ih =>
    have edge := next_follows _ nonempty
    have nonemptyNext := Nat.lt_of_lt_of_le nonempty edge.depth
    have earlier := edge.trans (rest.follows nonemptyNext)
    have later := suffix.follows (Nat.lt_of_lt_of_le nonempty earlier.depth)
    simpa only [Nat.add_right_comm _ 1 tailSteps] using
      Prefix.command codec operation next record wire value (different_follows earlier later before)
        present checked success decoded (ih suffix nonemptyNext)
  | joined codec count branches next record wire values before skip present checked success decoded size rest ih =>
    have edge := next_follows _ nonempty
    have nonemptyNext := Nat.lt_of_lt_of_le nonempty edge.depth
    have earlier := edge.trans (rest.follows nonemptyNext)
    have later := suffix.follows (Nat.lt_of_lt_of_le nonempty earlier.depth)
    simpa only [Nat.add_right_comm _ 1 tailSteps] using
      Prefix.joined codec count branches next record wire values (different_follows earlier later before)
        (skip_follows earlier later before skip) present checked success decoded size (ih suffix nonemptyNext)
  | child codec count branches next index before enters selected rest ih =>
    have edge := child_follows _ nonempty index
    have nonemptyChild := Nat.lt_of_lt_of_le nonempty edge.depth
    have earlier := edge.trans (rest.follows nonemptyChild)
    have later := suffix.follows (Nat.lt_of_lt_of_le nonempty earlier.depth)
    simpa only [Nat.add_right_comm _ 1 tailSteps] using
      Prefix.child codec count branches next index (different_follows earlier later before)
        (enters_follows enters later)
        ((later.branch_at _ ((entersChild_iff _ _).mp enters).1).symm.trans selected)
        (ih suffix nonemptyChild)

/-- Replaying the prefix reaches exactly the assigned continuation, with the same
journal and remaining fuel. No recorded prefix action needs to execute again. -/
theorem replay_reaches_continuation (journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) {α β : Type} {encode : α → Json} {program : Cloud M α}
    {current steps} {remainingEncode : β → Json} {remaining : Cloud M β}
    (witness : Prefix journal assignment.location encode program current steps remainingEncode remaining) (fuel : Nat) :
    (walk store blobs assignment (steps + fuel) encode program current).run journal =
      (walk store blobs assignment fuel remainingEncode remaining assignment.location).run journal := by
  induction witness with
  | here encode program => simp
  | delay next before rest ih =>
    rw [Nat.add_right_comm _ 1 fuel, walk]
    simpa [beq_eq_false_iff_ne.mpr before] using ih
  | command codec operation next record wire value before present checked success decoded rest ih =>
    rw [Nat.add_right_comm _ 1 fuel, walk]
    simp [beq_eq_false_iff_ne.mpr before]
    erw [read_then]
    simp [present, Internal.check, checked, success, Internal.decode, decoded]
    exact ih
  | joined codec count branches next record wire values before skip present checked success decoded size rest ih =>
    rw [Nat.add_right_comm _ 1 fuel, walk]
    simp [beq_eq_false_iff_ne.mpr before, skip]
    erw [read_then]
    simp [present, Internal.check, checked, success, Internal.decodeGroup, Internal.decode, decoded, size]
    exact ih
  | child codec count branches next index before enters selected rest ih =>
    rw [Nat.add_right_comm _ 1 fuel, walk]
    simp [beq_eq_false_iff_ne.mpr before, enters, selected, index.isLt]
    exact ih

/-- The worker entry point resumes the continuation certified by the recorded
prefix. An already completed branch instead takes `step`'s warm-replay shortcut. -/
theorem step_resumes_at_location [Codec α] (journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (program : ι → Cloud M α) (input : ι)
    {β : Type} {steps} {remainingEncode : β → Json} {remaining : Cloud M β} (fuel : Nat)
    (valid : (!assignment.location.isEmpty && assignment.location[0]!.1 == 0) = true)
    (unfinished : journal.lookup (ReplayStore.returnKey assignment.branch) = none)
    (witness : Prefix journal assignment.location Codec.encode (program input)
      Location.root steps remainingEncode remaining) :
    (step store blobs (steps + fuel) program input assignment).run journal =
      (walk store blobs assignment fuel remainingEncode remaining assignment.location).run journal := by
  simp [step, valid, ReplayStore.outcome]
  erw [read_then]
  simp [unfinished]
  exact replay_reaches_continuation journal blobs assignment witness fuel

/-- A completed branch reuses its durable return record without running its
program or changing the journal, even if the interpreter has no fuel left. -/
theorem completed_step_reuses_record [Codec α] (journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (program : ι → Cloud M α) (input : ι) (fuel : Nat)
    (record : ReplayRecord)
    (valid : (!assignment.location.isEmpty && assignment.location[0]!.1 == 0) = true)
    (completed : journal.lookup (ReplayStore.returnKey assignment.branch) = some record)
    (checked : (record.request == ReplayStore.returnRequest) = true) :
    (step store blobs fuel program input assignment).run journal = (.ok .done, journal) := by
  simp [step, valid, ReplayStore.outcome]
  erw [read_then]
  simp [completed, checked]

end LeanCloud.Proofs.Reconstruction
