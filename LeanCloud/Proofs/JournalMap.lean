import LeanCloud.Proofs.BackendMap
import LeanCloud.Proofs.JournalAdapter

/-! The physical journal adapter commutes with a backend map. In particular,
embedding its raw operations in a shared crash state preserves its whole loop. -/

namespace LeanCloud.Proofs.BackendMap
open Lean JournalDb JournalAdapter
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

omit [LawfulMonad m] [LawfulMonad n] in
theorem putSame_map (f : BackendMap m n) (backend : Db σ m) (key : String) (value : Json) :
    (f.state σ).map (putSame backend key value) = putSame (f.db backend) key value := by
  unfold putSame
  rw [(f.state σ).map_bind]
  congr 1
  funext previous
  cases previous with
  | none => rfl
  | some _ => exact (f.state σ).map_pure _

theorem put_map (f : BackendMap m n) (backend : Db σ m) (key : String) (value : Json) :
    (f.state σ).map (JournalDb.put backend key value) = JournalDb.put (f.db backend) key value := by
  unfold JournalDb.put
  cases fromJson? (α := Result) value with
  | error error => simp only []; exact (f.state σ).map_pure _
  | ok record =>
    simp only [pure_bind]
    cases record with
    | completed outcome => exact putSame_map f backend _ _
    | suspended children =>
      rw [(f.state σ).map_bind, putSame_map]
      congr 1
      funext accepted
      cases accepted with
      | false => exact (f.state σ).map_pure _
      | true =>
        simp only [↓reduceIte, (f.state σ).map_bind]
        congr 1
        · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
          rw [(f.state σ).map_forIn]
          congr 1
          funext index acc
          cases children[index]! with
          | none => exact (f.state σ).map_pure _
          | some outcome =>
            simp only [(f.state σ).map_bind, putSame_map]
            congr 1
            funext accepted
            cases accepted <;> exact (f.state σ).map_pure _
        · funext result
          cases result.1 <;> exact (f.state σ).map_pure _

theorem get_map (f : BackendMap m n) (backend : Db σ m) (key : String) :
    (f.state σ).map (JournalDb.get backend key) = JournalDb.get (f.db backend) key := by
  unfold JournalDb.get
  rw [(f.state σ).map_bind]
  congr 1
  funext cached
  cases cached with
  | some value =>
    simp only []
    cases fromJson? (α := Exit) value <;> simp only [] <;> exact (f.state σ).map_pure _
  | none =>
    rw [(f.state σ).map_bind]
    congr 1
    funext descriptor
    cases descriptor with
    | none => exact (f.state σ).map_pure _
    | some descriptor =>
      simp only []
      cases fromJson? (α := Nat) descriptor with
      | error error => simp only []; exact (f.state σ).map_pure _
      | ok count =>
        simp only [pure_bind, (f.state σ).map_bind]
        congr 1
        · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
          rw [(f.state σ).map_forIn]
          congr 1
          funext index acc
          rw [(f.state σ).map_bind]
          congr 1
          funext child
          cases child with
          | none => exact (f.state σ).map_pure _
          | some value =>
            simp only []
            cases fromJson? (α := Exit) value <;> simp only [] <;> exact (f.state σ).map_pure _
        · funext result
          cases result.1 <;> exact (f.state σ).map_pure _

theorem journal_map (f : BackendMap m n) (backend : Db σ m) :
    f.db (JournalDb.ofDb backend) = JournalDb.ofDb (f.db backend) := by
  change Db.mk _ _ = Db.mk _ _
  congr 1
  · funext key; exact get_map f backend key
  · funext key value; exact put_map f backend key value

end LeanCloud.Proofs.BackendMap
