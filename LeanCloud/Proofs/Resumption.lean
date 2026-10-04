import LeanCloud.Proofs.Reconstruction

namespace LeanCloud.Proofs.Reconstruction
open Lean LeanEff ReplayModel ReplayInterpreter Routing

/-- A location can be reconstructed from the source program. The continuation,
its result type, encoder, and prefix budget are proof witnesses, not runtime data. -/
def Resumable {m : Type → Type u} (journal : Journal) (encode : α → Json) (program : Cloud m α)
    (current target : Location) : Prop :=
  ∃ (β : Type) (remainingEncode : β → Json) (remaining : Cloud m β) (steps : Nat),
    Prefix journal target encode program current steps remainingEncode remaining

theorem Resumable.here {m : Type → Type u} (journal : Journal) (encode : α → Json)
    (program : Cloud m α) (current : Location) : Resumable journal encode program current current :=
  ⟨α, encode, program, 0, .here encode program⟩

theorem Resumable.extend {m : Type → Type u} {before after current target} {encode : α → Json} {program : Cloud m α}
    (resumable : Resumable before encode program current target) (extension : Extends before after) :
    Resumable after encode program current target := by
  obtain ⟨β, remainingEncode, remaining, steps, witness⟩ := resumable
  exact ⟨β, remainingEncode, remaining, steps, witness.extend extension⟩

private theorem Resumable.continuation {m : Type → Type u} {journal current target}
    {encode : α → Json} {program : Cloud m α}
    (available : Resumable journal encode program current target) (before : current ≠ target) :
    match program with
    | EffF.pure _ => False
    | .impure control next =>
      match control with
      | .delay => Resumable journal encode (next.apply ()) current target
      | .command codec operation =>
        ∃ record wire value,
          journal.lookup (ReplayStore.valueKey current) = some record ∧
          (record.request == Internal.request codec operation) = true ∧
          record.outcome = .success wire ∧ codec.decode wire = .ok value ∧
          Resumable journal encode (next.apply value) current.next target
      | .parallel codec count branches =>
        (∃ index : Fin count, current.entersChild target = true ∧ target[current.size]!.1 = index.val ∧
          Resumable journal codec.encode (branches index) (current.child index) target) ∨
        (current.entersChild target = false ∧ ∃ record wire values,
          journal.lookup (ReplayStore.valueKey current) = some record ∧
          (record.request == ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩) = true ∧
          record.outcome = .success wire ∧ (@instCodecArray _ codec).decode wire = .ok values ∧
          values.size = count ∧ Resumable journal encode (next.apply values) current.next target)
      | _ => False := by
  obtain ⟨β, remainingEncode, remaining, steps, witness⟩ := available
  cases witness with
  | here => exact False.elim (before rfl)
  | delay _ _ rest => exact ⟨_, _, _, _, rest⟩
  | command _ _ _ record wire value _ present checked success decoded rest =>
    exact ⟨record, wire, value, present, checked, success, decoded, _, _, _, _, rest⟩
  | joined _ _ _ _ record wire values _ skip present checked success decoded size rest =>
    exact Or.inr ⟨skip, record, wire, values, present, checked, success, decoded, size, _, _, _, _, rest⟩
  | child _ _ _ _ index _ enters selected rest =>
    exact Or.inl ⟨index, enters, selected, _, _, _, _, rest⟩

/-- A reconstructible location has the same typed continuation and prefix
length in every compatible snapshot. A complete specification can therefore
choose the fuel budget once; workers need only the records on their own path. -/
theorem Prefix.in_snapshot {m : Type → Type u} {expected journal : Journal}
    {target current steps} {encode : α → Json} {program : Cloud m α}
    {remainingEncode : β → Json} {remaining : Cloud m β}
    (witness : Prefix expected target encode program current steps remainingEncode remaining)
    (consistent : Extends journal expected)
    (available : Resumable journal encode program current target) :
    Prefix journal target encode program current steps remainingEncode remaining := by
  induction witness with
  | here encode program => exact .here encode program
  | delay next before rest ih =>
    exact .delay next before (ih (available.continuation before))
  | command codec operation next record wire value before present checked success decoded rest ih =>
    obtain ⟨actual, actualWire, actualValue, found, _, succeeded, decodedActual, path⟩ := available.continuation before
    have same := Option.some.inj ((consistent _ _ found).symm.trans present)
    subst actual
    have sameWire := Exit.success.inj (succeeded.symm.trans success)
    subst actualWire
    have sameValue := Except.ok.inj (decodedActual.symm.trans decoded)
    subst actualValue
    exact .command codec operation next record wire value before found checked success decoded (ih path)
  | joined codec count branches next record wire values before skip present checked success decoded size rest ih =>
    rcases available.continuation before with ⟨_, enters, _, _⟩ | ⟨_, actual, actualWire, actualValues, found, _, succeeded, decodedActual, _, path⟩
    · simp [skip] at enters
    ·
      have same := Option.some.inj ((consistent _ _ found).symm.trans present)
      subst actual
      have sameWire := Exit.success.inj (succeeded.symm.trans success)
      subst actualWire
      have sameValues := Except.ok.inj (decodedActual.symm.trans decoded)
      subst actualValues
      exact .joined codec count branches next record wire values before skip found checked success decoded size
        (ih path)
  | child codec count branches next index before enters selected rest ih =>
    rcases available.continuation before with ⟨actual, _, actualSelected, path⟩ | ⟨skip, _⟩
    ·
      have same : actual = index := Fin.ext (actualSelected.symm.trans selected)
      subst actual
      exact .child codec count branches next index before enters selected (ih path)
    · simp [enters] at skip

theorem Resumable.follows {m : Type → Type u} {journal current target} {encode : α → Json} {program : Cloud m α}
    (resumable : Resumable journal encode program current target) (nonempty : 0 < current.size) :
    Follows current target := by
  obtain ⟨_, _, _, _, witness⟩ := resumable
  exact witness.follows nonempty

/-- Reconstructing from the root automatically satisfies the worker's location
validation. No separate well-formedness assumption is needed. -/
theorem Resumable.valid_root {m : Type → Type u} {journal target} {encode : α → Json} {program : Cloud m α}
    (resumable : Resumable journal encode program Location.root target) :
    (!target.isEmpty && target[0]!.1 == 0) = true := by
  have route := resumable.follows (by decide)
  have nonempty : 0 < target.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have first : target[0]!.1 = 0 := by simpa [LeanCloud.Location.root] using (route.branch_at 0 (by decide)).symm
  simp [Array.isEmpty, Nat.ne_of_gt nonempty, first]

theorem Resumable.prepend {m : Type → Type u} {journal current middle target steps}
    {encode : α → Json} {program : Cloud m α} {remainingEncode : β → Json} {remaining : Cloud m β}
    (resumable : Resumable journal remainingEncode remaining middle target)
    (witness : Prefix journal middle encode program current steps remainingEncode remaining)
    (nonempty : 0 < current.size) : Resumable journal encode program current target := by
  obtain ⟨γ, finalEncode, final, tailSteps, suffix⟩ := resumable
  exact ⟨γ, finalEncode, final, steps + tailSteps, witness.append suffix nonempty⟩

theorem Resumable.delay {m : Type → Type u} {journal current target} {encode : α → Json}
    (next : ArrsF (Control m) Unit α) (rest : Resumable journal encode (next.apply ()) current target) :
    Resumable journal encode (.impure .delay next) current target := by
  by_cases same : current = target
  · subst target; exact .here ..
  · obtain ⟨β, remainingEncode, remaining, steps, witness⟩ := rest
    exact ⟨β, remainingEncode, remaining, steps + 1, .delay next same witness⟩

theorem Resumable.command {m : Type → Type u} {journal current target} {encode : β → Json}
    (codec : Codec α) (operation : Operation m α) (next : ArrsF (Control m) α β)
    (record : ReplayRecord) (wire : Json) (value : α) (nonempty : 0 < current.size)
    (present : journal.lookup (ReplayStore.valueKey current) = some record)
    (checked : (record.request == Internal.request codec operation) = true)
    (success : record.outcome = .success wire) (decoded : codec.decode wire = .ok value)
    (rest : Resumable journal encode (next.apply value) current.next target) :
    Resumable journal encode (.impure (.command codec operation) next) current target := by
  obtain ⟨γ, remainingEncode, remaining, steps, witness⟩ := rest
  have edge := next_follows current nonempty
  have later := witness.follows (Nat.lt_of_lt_of_le nonempty edge.depth)
  exact ⟨γ, remainingEncode, remaining, steps + 1,
    .command codec operation next record wire value (different_follows edge later (next_ne current nonempty))
      present checked success decoded witness⟩

theorem Resumable.joined {m : Type → Type u} {journal current target} {encode : β → Json}
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α) (next : ArrsF (Control m) (Array α) β)
    (record : ReplayRecord) (wire : Json) (values : Array α) (nonempty : 0 < current.size)
    (present : journal.lookup (ReplayStore.valueKey current) = some record)
    (checked : (record.request == ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩) = true)
    (success : record.outcome = .success wire) (decoded : (@instCodecArray α codec).decode wire = .ok values)
    (size : values.size = count) (rest : Resumable journal encode (next.apply values) current.next target) :
    Resumable journal encode (.impure (.parallel codec count branches) next) current target := by
  obtain ⟨γ, remainingEncode, remaining, steps, witness⟩ := rest
  have edge := next_follows current nonempty
  have later := witness.follows (Nat.lt_of_lt_of_le nonempty edge.depth)
  exact ⟨γ, remainingEncode, remaining, steps + 1,
    .joined codec count branches next record wire values (different_follows edge later (next_ne current nonempty))
      (skip_follows edge later (next_ne current nonempty) (skip_next current))
      present checked success decoded size witness⟩

theorem Resumable.child {m : Type → Type u} (journal : Journal) (encode : β → Json) (current : Location)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α) (next : ArrsF (Control m) (Array α) β)
    (index : Fin count) :
    Resumable journal encode (.impure (.parallel codec count branches) next) current (current.child index) := by
  refine ⟨α, codec.encode, branches index, 1, .child codec count branches next index ?_
    (enters_child current index) (by simp [LeanCloud.Location.child]) (.here _ _)⟩
  intro same
  have sizes := congrArg Array.size same
  simp [LeanCloud.Location.child] at sizes

end LeanCloud.Proofs.Reconstruction
