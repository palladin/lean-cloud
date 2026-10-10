import LeanCloud.Proofs.RecoveryReads

namespace LeanCloud.Proofs.RecoveryStep
open Lean LeanEff ReplayFaults ReplayModel ReplayInterpreter JournalMerge JournalRegion WorkerRecovery
open RecoveryMeaning RecoveryCursor

variable {info : Option SourceSiteId}

private theorem catch_pure (value : β) (handle : CloudError → ExceptT CloudError WorkerM β) :
    (tryCatch (pure value) handle : ExceptT CloudError WorkerM β) = pure value := rfl

private theorem command (expected base : Journal) (branch current : Location) (codec : Codec β)
    (label : String) (body : Unit → β) (property : Journal → Prop)
    (monotone : ∀ before after, property before → Extends before after → property after)
    (owned : Owns branch (ReplayStore.valueKey current))
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → WorkerM β)),
        .success (codec.encode (body ()))⟩) :
    Ensures (Valid expected base branch) (fun j => Valid expected base branch j ∧ property j)
      (Internal.command ReplayFaults.store ReplayFaults.noBlobs current codec (.exec label (fun _ => pure (body ()))))
      (fun value j => property j ∧ value = .success (codec.encode (body ())) ∧
        j.lookup (ReplayStore.valueKey current) =
          some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → WorkerM β)),
            .success (codec.encode (body ()))⟩) := by
  unfold Internal.command
  apply Ensures.read_bind _ _ (fun j h => h.1)
  intro found
  cases found with
  | some record =>
    intro saved ⟨⟨valid, holds⟩, got⟩
    have same := Option.some.inj ((valid.2 _ _ got.symm).symm.trans known)
    subst record
    simp only [Internal.check, beq_self_eq_true, ↓reduceIte]
    exact
      (show Valid expected base branch saved.durable ∧
        saved.faults.remaining.length ≤ saved.faults.remaining.length ∧
        property saved.durable ∧ (Exit.success (codec.encode (body ()))) = .success (codec.encode (body ())) ∧
        saved.durable.lookup (ReplayStore.valueKey current) = _ from ⟨valid, Nat.le_refl _, holds, rfl, got.symm⟩)
  | none =>
    simp only [Internal.execute, BlobStorage.execute, liftM_pure, pure_bind]
    simp only [catch_pure, pure_bind]
    apply ((create_preserving property monotone owned known).consequence
      (fun j h => h.1) (fun _ _ h => h)).bind
    intro record saved ⟨valid, holds, same, got⟩
    subst record
    simp only [Internal.check, beq_self_eq_true, ↓reduceIte]
    exact
      (show Valid expected base branch saved.durable ∧
        saved.faults.remaining.length ≤ saved.faults.remaining.length ∧
        property saved.durable ∧ (Exit.success (codec.encode (body ()))) = .success (codec.encode (body ())) ∧
        saved.durable.lookup (ReplayStore.valueKey current) = _ from ⟨valid, Nat.le_refl _, holds, rfl, got⟩)

private theorem group (expected base : Journal) (branch current : Location) (codec : Codec β)
    (count : Nat) (outcomes : Fin count → Except CloudError β) (property : Journal → Prop)
    (monotone : ∀ before after, property before → Extends before after → property after)
    (owned : Owns branch (ReplayStore.valueKey current))
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
        Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩)
    (returned : ∀ index : Fin count, expected.lookup (ReplayStore.returnKey (current.child index)) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
    (continueWith : Exit → ExceptT CloudError WorkerM Progress)
    (resumes : Ensures (Valid expected base branch)
      (fun journal => Valid expected base branch journal ∧ property journal ∧ journal.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
          Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩)
      (continueWith (Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id))) post)
    (suspended : ∀ journal, Valid expected base branch journal → property journal →
      (∃ index : Fin count, journal.lookup (ReplayStore.returnKey (current.child index)) = none) → post (.fork current count) journal) :
    Ensures (Valid expected base branch) (fun j => Valid expected base branch j ∧ property j)
      (do
        let expected : Request := ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩
        match ← ReplayFaults.store.read (ReplayStore.valueKey current) with
        | some record => continueWith (← Internal.check expected record)
        | none =>
            match ← Internal.tryJoin ReplayFaults.store current count with
            | none => return .fork current count
            | some outcome =>
                let record ← ReplayFaults.store.create (ReplayStore.valueKey current) ⟨expected, outcome⟩
                continueWith (← Internal.check expected record)) post := by
  have publish : Ensures (Valid expected base branch) (fun j => Valid expected base branch j ∧ property j)
      (do
        let record ← ReplayFaults.store.create (ReplayStore.valueKey current)
          ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
            Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩
        continueWith (← Internal.check ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩ record)) post := by
    apply (create_preserving property monotone owned known).bind
    intro record saved ⟨valid, holds, same, present⟩
    subst record
    simpa [Internal.check] using resumes saved ⟨valid, holds, present⟩
  apply Ensures.read_bind _ _ (fun j h => h.1)
  intro found
  cases found with
  | some record =>
    intro saved ⟨⟨valid, holds⟩, got⟩
    have same := Option.some.inj ((valid.2 _ _ got.symm).symm.trans known)
    subst record
    simpa [Internal.check] using resumes saved ⟨valid, holds, got.symm⟩
  | none =>
    apply ((RecoveryReads.join expected current codec count outcomes returned
      (fun j (h : Valid expected base branch j ∧ property j) => ⟨h.1, h.1.2⟩)).consequence
      (fun j h => h.1) (fun _ _ h => h)).bind
    intro result
    cases result with
    | none =>
      apply Ensures.pure (Progress.fork current count)
      intro journal ⟨valid, ⟨_, holds⟩, missing⟩
      exact ⟨valid, suspended journal valid holds missing⟩
    | some value =>
      intro saved ⟨valid, ⟨_, holds⟩, same⟩
      subst value
      exact publish saved ⟨valid, holds⟩

/-- A sufficiently funded replay segment either completes correctly or suspends
at a genuine incomplete group. Every interrupted prefix preserves its records. -/
theorem replay_safe [rootCodec : Codec α] (source : Cloud WorkerM α)
    {expected current} {program : Cloud WorkerM β} {outcome budget}
    (meaning : Meaning expected current program outcome budget) :
    ∀ (encode : β → Json) (base : Journal) (branch : Location) (cost limit fuel : Nat),
      branch = Proofs.Location.branchStart current → cost + budget ≤ limit → budget ≤ fuel →
      expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩ →
      Ensures (Valid expected base branch)
        (fun journal => Valid expected base branch journal ∧ Cursor source journal current encode program cost)
        (replay ReplayFaults.store ReplayFaults.noBlobs branch fuel encode program current)
        (ProgressValid source expected limit branch) := by
  induction meaning with
  | pure value =>
    intro encode base branch cost limit fuel same bounded enough known
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    rw [replay]
    exact (finish known).consequence (fun _ h => h.1) (fun _ _ h => h)
  | fail error next =>
    intro encode base branch cost limit fuel same bounded enough known
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    rw [replay]
    exact (finish known).consequence (fun _ h => h.1) (fun _ _ h => h)
  | delay next rest ih =>
    intro encode base branch cost limit fuel same bounded enough known
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    rw [replay]
    exact (ih encode base branch (cost + 1) limit n same (by omega) (by omega) known).consequence
      (fun _ h => ⟨h.1, .delay h.2⟩) (fun _ _ h => h)
  | exec codec label body next roundtrip present rest ih =>
    intro encode base branch cost limit fuel same bounded enough known
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    rw [replay]
    apply (command expected base branch _ codec label body
      (fun journal => Cursor source journal _ encode (.impure _ (.command codec (.exec label (fun _ => pure (body ())))) next) cost)
      (fun _ _ cursor extension => cursor.extend source extension) (Owns.value same) present).bind
    intro result saved ⟨valid, cursor, correct, recorded⟩
    subst result
    simp only [Internal.resume, Internal.decode, roundtrip, pure_bind]
    exact ih encode base branch (cost + 1) limit n (by simpa using same) (by omega) (by omega) known saved
      ⟨valid, .exec codec label body next cursor recorded roundtrip⟩
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    intro encode base branch cost limit fuel same bounded enough known
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    rw [replay]
    apply group expected base branch _ codec count outcomes
      (fun journal => Cursor source journal _ encode (.impure _ (.parallel codec count branches) next) cost)
      (fun _ _ cursor extension => cursor.extend source extension) (Owns.value same)
      (by simpa [collected, Parallel.recorded] using present) returned
    · simp only [collected, Parallel.recorded, Internal.resume]
      have size := Parallel.sequence_size _ _ collected
      simp only [Array.size_ofFn] at size
      have decoded := roundtrip.array codec
      change ∀ values, (@instCodecArray _ codec).decode (Json.arr (values.map codec.encode)) = .ok values at decoded
      simp only [Internal.decodeGroup, Internal.decode, decoded, size, beq_self_eq_true, ↓reduceIte, pure_bind]
      apply (ih encode base branch (cost + 1) limit n (by simpa using same) (by omega) (by omega) known).consequence
      · intro journal ⟨valid, cursor, recorded⟩
        exact ⟨valid, .joined codec count branches next _ cursor recorded (decoded _) size⟩
      · exact fun _ _ h => h
    · intro journal valid cursor missing
      refine ⟨same, ?_, missing⟩
      intro index
      exact ⟨_, codec.encode, branches index, outcomes index, _, cost + 1, _,
        (Proofs.Location.branchStart_child _ _).symm, by omega,
        .child codec count branches next cursor index, children index, returned index⟩
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    intro encode base branch cost limit fuel same bounded enough known
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    rw [replay]
    apply group expected base branch _ codec count outcomes
      (fun journal => Cursor source journal _ encode (.impure _ (.parallel codec count branches) next) cost)
      (fun _ _ cursor extension => cursor.extend source extension) (Owns.value same)
      (by simpa [collected, Parallel.recorded] using present) returned
    · simp only [collected, Parallel.recorded, Internal.resume]
      exact (finish known).consequence (fun _ h => h.1) (fun _ _ h => h)
    · intro journal valid cursor missing
      refine ⟨same, ?_, missing⟩
      intro index
      exact ⟨_, codec.encode, branches index, outcomes index, _, cost + 1, _,
        (Proofs.Location.branchStart_child _ _).symm, by omega,
        .child codec count branches next cursor index, children index, returned index⟩
  | weaken meaning larger ih =>
    intro encode base branch cost limit fuel same bounded enough known
    exact ih encode base branch cost limit fuel same (by omega) (by omega) known

end LeanCloud.Proofs.RecoveryStep


