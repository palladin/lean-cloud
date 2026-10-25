import LeanCloud.Proofs.ReplayCursor

namespace LeanCloud.Proofs.ProgramCursor

variable {label : ParallelLabel}
open Lean LeanEff ReplayModel ReplayInterpreter Routing

variable {info : Option SourceSiteId}

variable [rootCodec : Codec α] (context : ExecContext M) (source : Cloud M α)

/-- A proof-only cursor into the source. It can pass transparent delays without
advancing the location. It carries no runtime continuation. -/
structure Cursor (journal : Journal) (current : Location) (encode : β → Json)
    (remaining : Cloud M β) : Prop where
  follows : Follows Location.root current
  replay : ∃ cost, ∀ after, Extends journal after → ∀ assignment,
    assignment.branchStart = Location.branchStart assignment.location →
    Follows current assignment.location → ∀ fuel,
      (ReplayCursor.atPoint store context assignment (cost + fuel) rootCodec.encode source Location.root).run after =
        (ReplayCursor.atPoint store context assignment fuel encode remaining current).run after

theorem Cursor.root (journal : Journal) : Cursor context source journal Location.root rootCodec.encode source :=
  ⟨.refl _ (by decide), 0, by intros; simp⟩

theorem Cursor.extend {journal after current} {encode : β → Json} {remaining : Cloud M β}
    (cursor : Cursor context source journal current encode remaining) (grows : Extends journal after) :
    Cursor context source after current encode remaining := by
  obtain ⟨route, cost, replay⟩ := cursor
  exact ⟨route, cost, fun later extension => replay later (grows.trans extension)⟩

theorem Cursor.delay {journal current encode} (next : ArrsF (Control M) SourceSiteId Unit β)
    (cursor : Cursor context source journal current encode (.impure info .delay next)) :
    Cursor context source journal current encode (next.apply ()) := by
  obtain ⟨route, cost, replay⟩ := cursor
  refine ⟨route, cost + 1, ?_⟩
  intro after extension assignment branch follows fuel
  rw [Nat.add_assoc, replay after extension assignment branch follows, Nat.add_comm 1,
    ReplayCursor.delay _ _ _ branch]

theorem Cursor.exec {journal current encode} (codec : Codec β) (label : String) (body : Unit → β)
    (next : ArrsF (Control M) SourceSiteId β γ)
    (cursor : Cursor context source journal current encode (.impure info (.command codec label (fun _ => pure (body ()))) next))
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec label, .success (codec.encode (body ()))⟩)
    (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ())) :
    Cursor context source journal current.next encode (next.apply (body ())) := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have edge := next_follows current nonempty
  refine ⟨route.trans edge, cost + 1, ?_⟩
  intro after extension assignment branch follows fuel
  rw [Nat.add_assoc, replay after extension assignment branch (edge.trans follows), Nat.add_comm 1]
  exact ReplayCursor.command after context assignment branch current fuel encode codec label _ next _ _ _ _
    (extension _ _ present) (by simp) rfl roundtrip

theorem Cursor.joined {journal current encode} (codec : Codec β) (count : Nat)
    (branches : Fin count → Cloud M β) (next : ArrsF (Control M) SourceSiteId (Array β) γ) (values : Array β)
    (cursor : Cursor context source journal current encode (.impure info (.parallel codec count branches label) next))
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩)
    (decoded : (@instCodecArray β codec).decode (Json.arr (values.map codec.encode)) = .ok values)
    (size : values.size = count) :
    Cursor context source journal current.next encode (next.apply values) := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have edge := next_follows current nonempty
  refine ⟨route.trans edge, cost + 1, ?_⟩
  intro after extension assignment branch follows fuel
  have skip := skip_follows edge follows (next_ne current nonempty) (skip_next current)
  rw [Nat.add_assoc, replay after extension assignment branch (edge.trans follows), Nat.add_comm 1]
  exact ReplayCursor.joined after context assignment branch current fuel encode codec count branches next _ _ _ values
    (edge.trans follows) skip (extension _ _ present) (by simp) rfl decoded size

theorem Cursor.child {journal current encode} (codec : Codec β) (count : Nat)
    (branches : Fin count → Cloud M β) (next : ArrsF (Control M) SourceSiteId (Array β) γ)
    (cursor : Cursor context source journal current encode (.impure info (.parallel codec count branches label) next)) (index : Fin count) :
    Cursor context source journal (current.child index) codec.encode (branches index) := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have edge := child_follows current nonempty index
  refine ⟨route.trans edge, cost + 1, ?_⟩
  intro after extension assignment branch follows fuel
  have enters := enters_follows (enters_child current index) follows
  have selected : assignment.location[current.size]!.1 = index.val := by
    simpa [LeanCloud.Location.child] using (follows.branch_at current.size (by simp [LeanCloud.Location.child])).symm
  rw [Nat.add_assoc, replay after extension assignment branch (edge.trans follows), Nat.add_comm 1,
    ReplayCursor.child _ _ _ branch _ _ codec count branches next _ _ index enters selected follows]

/-- The replay entry point reconstructs this cursor from the root. -/
theorem Cursor.step {journal current} {encode : β → Json} {remaining : Cloud M β}
    (cursor : Cursor context source journal current encode remaining) (assignment : ReplayTarget)
    (branch : assignment.branchStart = Location.branchStart assignment.location)
    (atLocation : assignment.location = current)
    (unfinished : journal.lookup (ReplayStore.returnKey assignment.branchStart) = none) :
    ∃ cost, ∀ fuel,
      (step store context (cost + fuel) (fun _ : Unit => source) () assignment).run journal =
        (ReplayInterpreter.replay store context assignment.branchStart fuel encode remaining current).run journal := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have first : current[0]!.1 = 0 := by simpa [LeanCloud.Location.root] using (route.branch_at 0 (by decide)).symm
  have valid : (!assignment.branchStart.isEmpty && assignment.branchStart[0]!.1 == 0) = true := by
    simp [branch, atLocation, Array.isEmpty, Nat.ne_of_gt nonempty, Location.branchStart_index _ 0 nonempty, first]
  refine ⟨cost, fun fuel => ?_⟩
  simp [ReplayInterpreter.step, ReplayTarget.work, valid, ReplayStore.outcome]
  erw [read_then]
  simp only [unfinished, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have follows : Follows current assignment.location := by simpa only [atLocation] using Follows.refl current nonempty
  rw [← ReplayCursor.boundary store context assignment branch _ _ _ Location.root (route.trans follows) (by simp)]
  rw [replay journal (.refl _) assignment branch follows]
  simpa only [atLocation] using congrArg (fun action => action.run journal)
    (ReplayCursor.at_target store context assignment fuel encode remaining)

/-- A completed branch reuses its durable return record without running its
program or changing the journal, even if the interpreter has no fuel left. -/
theorem completed_step_reuses_record (journal : Journal) (context : ExecContext M)
    (assignment : ReplayTarget) (program : ι → Cloud M α) (input : ι) (fuel : Nat)
    (record : ReplayRecord)
    (valid : (!assignment.branchStart.isEmpty && assignment.branchStart[0]!.1 == 0) = true)
    (completed : journal.lookup (ReplayStore.returnKey assignment.branchStart) = some record)
    (checked : (record.request == ReplayStore.returnRequest) = true) :
    (step store context fuel program input assignment).run journal = (.ok .done, journal) := by
  simp [step, ReplayTarget.work, valid, ReplayStore.outcome]
  erw [read_then]
  simp [completed, checked]

end LeanCloud.Proofs.ProgramCursor
