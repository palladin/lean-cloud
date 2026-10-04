import LeanCloud.Proofs.Reconstruction

namespace LeanCloud.Proofs.SequentialCursor
open Lean LeanEff ReplayModel ReplayInterpreter Reconstruction Routing

variable {info : Option SourceSiteId}

variable [rootCodec : Codec α] (blobs : BlobStorage M) (source : Cloud M α)

/-- A proof-only cursor into the source. Unlike an assigned location it can also
pass transparent delays at that location. It carries no runtime continuation. -/
structure Cursor (journal : Journal) (current : Location) (encode : β → Json)
    (remaining : Cloud M β) : Prop where
  follows : Follows Location.root current
  replay : ∃ cost, ∀ after, Extends journal after → ∀ assignment,
    Follows current assignment.location → ∀ fuel,
      (walk store blobs assignment (cost + fuel) rootCodec.encode source Location.root).run after =
        (walk store blobs assignment fuel encode remaining current).run after

theorem Cursor.root (journal : Journal) : Cursor blobs source journal Location.root rootCodec.encode source :=
  ⟨.refl _ (by decide), 0, by intros; simp⟩

theorem Cursor.extend {journal after current} {encode : β → Json} {remaining : Cloud M β}
    (cursor : Cursor blobs source journal current encode remaining) (grows : Extends journal after) :
    Cursor blobs source after current encode remaining := by
  obtain ⟨route, cost, replay⟩ := cursor
  exact ⟨route, cost, fun later extension => replay later (grows.trans extension)⟩

theorem Cursor.delay {journal current encode} (next : ArrsF (Control M) SourceSiteId Unit β)
    (cursor : Cursor blobs source journal current encode (.impure info .delay next)) :
    Cursor blobs source journal current encode (next.apply ()) := by
  obtain ⟨route, cost, replay⟩ := cursor
  refine ⟨route, cost + 1, ?_⟩
  intro after extension assignment follows fuel
  rw [Nat.add_assoc, replay after extension assignment follows, Nat.add_comm 1, walk]
  by_cases same : current = assignment.location
  · subst current
    simpa using congrArg (fun action => action.run after) (walk_at_assignment store blobs assignment fuel encode (next.apply ())).symm
  · simp [beq_eq_false_iff_ne.mpr same]

theorem Cursor.exec {journal current encode} (codec : Codec β) (label : String) (body : Unit → β)
    (next : ArrsF (Control M) SourceSiteId β γ)
    (cursor : Cursor blobs source journal current encode (.impure info (.command codec (.exec label (fun _ => pure (body ())))) next))
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → M β)), .success (codec.encode (body ()))⟩)
    (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ())) :
    Cursor blobs source journal current.next encode (next.apply (body ())) := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have edge := next_follows current nonempty
  refine ⟨route.trans edge, cost + 1, ?_⟩
  intro after extension assignment follows fuel
  have before := different_follows edge follows (next_ne current nonempty)
  rw [Nat.add_assoc, replay after extension assignment (edge.trans follows), Nat.add_comm 1, walk]
  simp only [beq_eq_false_iff_ne.mpr before, Bool.false_or]
  erw [read_then]
  simp [extension _ _ present, Internal.check, Internal.decode, roundtrip]

theorem Cursor.joined {journal current encode} (codec : Codec β) (count : Nat)
    (branches : Fin count → Cloud M β) (next : ArrsF (Control M) SourceSiteId (Array β) γ) (values : Array β)
    (cursor : Cursor blobs source journal current encode (.impure info (.parallel codec count branches) next))
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩)
    (decoded : (@instCodecArray β codec).decode (Json.arr (values.map codec.encode)) = .ok values)
    (size : values.size = count) :
    Cursor blobs source journal current.next encode (next.apply values) := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have edge := next_follows current nonempty
  refine ⟨route.trans edge, cost + 1, ?_⟩
  intro after extension assignment follows fuel
  have before := different_follows edge follows (next_ne current nonempty)
  have skip := skip_follows edge follows (next_ne current nonempty) (skip_next current)
  rw [Nat.add_assoc, replay after extension assignment (edge.trans follows), Nat.add_comm 1, walk]
  simp only [beq_eq_false_iff_ne.mpr before, Bool.false_or, Bool.not_false,
    Bool.true_and, skip, Bool.false_eq_true, ite_false]
  erw [read_then]
  simp [extension _ _ present, Internal.check, Internal.decodeGroup, Internal.decode, decoded, size]

theorem Cursor.child {journal current encode} (codec : Codec β) (count : Nat)
    (branches : Fin count → Cloud M β) (next : ArrsF (Control M) SourceSiteId (Array β) γ)
    (cursor : Cursor blobs source journal current encode (.impure info (.parallel codec count branches) next)) (index : Fin count) :
    Cursor blobs source journal (current.child index) codec.encode (branches index) := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have edge := child_follows current nonempty index
  refine ⟨route.trans edge, cost + 1, ?_⟩
  intro after extension assignment follows fuel
  have different : current ≠ current.child index := by intro same; have := congrArg Array.size same; simp [LeanCloud.Location.child] at this
  have before := different_follows edge follows different
  have enters := enters_follows (enters_child current index) follows
  have selected : assignment.location[current.size]!.1 = index.val := by
    simpa [LeanCloud.Location.child] using (follows.branch_at current.size (by simp [LeanCloud.Location.child])).symm
  rw [Nat.add_assoc, replay after extension assignment (edge.trans follows), Nat.add_comm 1, walk]
  simp [beq_eq_false_iff_ne.mpr before, enters, selected, index.isLt]

/-- The ordinary worker entry point reconstructs this cursor from the root. -/
theorem Cursor.step {journal current} {encode : β → Json} {remaining : Cloud M β}
    (cursor : Cursor blobs source journal current encode remaining) (assignment : Assignment)
    (atLocation : assignment.location = current)
    (unfinished : journal.lookup (ReplayStore.returnKey assignment.branch) = none) :
    ∃ cost, ∀ fuel,
      (step store blobs (cost + fuel) (fun _ : Unit => source) () assignment).run journal =
        (walk store blobs assignment fuel encode remaining current true).run journal := by
  obtain ⟨route, cost, replay⟩ := cursor
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have first : current[0]!.1 = 0 := by simpa [LeanCloud.Location.root] using (route.branch_at 0 (by decide)).symm
  have valid : (!assignment.location.isEmpty && assignment.location[0]!.1 == 0) = true := by
    simp [atLocation, Array.isEmpty, Nat.ne_of_gt nonempty, first]
  refine ⟨cost, fun fuel => ?_⟩
  simp [ReplayInterpreter.step, valid, ReplayStore.outcome]
  erw [read_then]
  simp only [unfinished, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rw [replay journal (.refl _) assignment (by simpa only [atLocation] using Follows.refl current nonempty)]
  simpa only [atLocation] using congrArg (fun action => action.run journal)
    (walk_at_assignment store blobs assignment fuel encode remaining)

end LeanCloud.Proofs.SequentialCursor
