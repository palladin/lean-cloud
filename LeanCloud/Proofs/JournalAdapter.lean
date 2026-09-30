import LeanCloud.Proofs.JournalDb
import LeanCloud.Proofs.ParallelSlots
import Init.Data.Range.Lemmas

/-! Specifications of the actual journal adapter. The list of records below is
a proof description of its existing loop, not an alternative implementation. -/

namespace LeanCloud.Proofs.JournalAdapter
open Lean JournalDb

abbrev Record := String × Json

def childRecord (key : String) (children : Array (Option Exit)) (index : Nat) : Option Record :=
  children[index]!.map fun outcome => (childKey key index, toJson outcome)

def records (key : String) : Result → List Record
  | .completed outcome => [(resultKey key, toJson outcome)]
  | .suspended children => (forkKey key, toJson children.size) ::
      (List.range children.size).filterMap (childRecord key children)

def publish [Monad m] (db : Db σ m) : List Record → StateT σ m Bool
  | [] => pure true
  | (key, value) :: rest => do
    if ← putSame db key value then publish db rest else pure false

private theorem publish_loop [Monad m] [LawfulMonad m] (db : Db σ m)
    (key : String) (children : Array (Option Exit)) (indices : List Nat) :
    (do
      let result ← forIn indices (none, ()) fun index (_ : Option Bool × Unit) =>
        match children[index]! with
        | some outcome => do
          if ← putSame db (childKey key index) (toJson outcome) then
            pure (ForInStep.yield (none, ()))
          else pure (ForInStep.done (some false, ()))
        | _ => pure (ForInStep.yield (none, ()))
      match result.1 with
      | some value => pure value
      | none => pure true) =
      publish db (indices.filterMap (childRecord key children)) := by
  induction indices with
  | nil => simp [publish]
  | cons index rest ih =>
    simp only [List.forIn_cons, List.filterMap_cons, childRecord]
    cases slot : children[index]! with
    | none => simpa [slot] using ih
    | some outcome =>
      simp only [Option.map_some, publish, bind_assoc]
      congr 1
      funext accepted
      cases accepted
      · simp
      · simpa only [↓reduceIte, pure_bind] using ih

/-- The actual adapter publishes exactly this finite sequence of records. -/
theorem put_eq_publish [Monad m] [LawfulMonad m] (db : Db σ m)
    (key : String) (result : Result) :
    JournalDb.put db key (toJson result) = publish db (records key result) := by
  unfold JournalDb.put
  rw [result_roundtrip]
  simp only [pure_bind]
  cases result with
  | completed outcome =>
    have identity : ∀ b : Bool,
        (if b = true then (pure true : StateT σ m Bool) else pure false) = pure b := by
      intro b; cases b <;> rfl
    simp only [records, publish, identity, bind_pure]
  | suspended children =>
    simp only [records, publish]
    congr 1
    funext accepted
    cases accepted
    · simp
    · simp only [↓reduceIte]
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      rw [← List.range_eq_range']
      rw [← publish_loop db key children (List.range children.size)]
      congr 1
      funext state
      cases state.1 <;> rfl

/-- Atomic exact-map backend for read reconstruction. -/
def raw : Db Journal Id where
  get key journal := (journal key, journal)
  put key value journal := (true, journal.write key value)

private theorem read_loop
    (body : Nat → Option (Option Json) × Array (Option Exit) →
      StateT Journal Id (ForInStep (Option (Option Json) × Array (Option Exit))))
    (indices : List Nat) (slots : Nat → Option Exit) (journal : Journal) (acc : Array (Option Exit))
    (step : ∀ index ∈ indices, ∀ acc,
      body index (none, acc) journal = (.yield (none, acc.push (slots index)), journal)) :
    (forIn indices (none, acc) body) journal =
      ((none, acc ++ (indices.map slots).toArray), journal) := by
  induction indices generalizing acc with
  | nil => simp [StateT.pure, pure, List.forIn_nil]
  | cons index rest ih =>
    rw [List.forIn_cons]
    simp only [bind, StateT.bind]
    rw [step index (by simp)]
    simp only []
    rw [ih (step := fun i member => step i (by simp [member]))]
    simp [Array.push_eq_append, Array.append_assoc, -Array.append_singleton]

/-- Reading a completed record returns its outcome without changing storage. -/
theorem get_completed (journal : Journal) (key : String) (outcome : Exit)
    (recorded : journal (resultKey key) = some (toJson outcome)) :
    JournalDb.get raw key journal = (some (toJson (Result.completed outcome)), journal) := by
  simp [JournalDb.get, raw, StateT.bind, StateT.pure, pure, bind, recorded, exit_roundtrip]

/-- Reading a fork assembles exactly its indexed child slots, then applies the
interpreter's existing array-order result selection. -/
theorem get_fork (journal : Journal) (key : String) (children : Array (Option Exit))
    (uncached : journal (resultKey key) = none)
    (fork : journal (forkKey key) = some (toJson children.size))
    (slots : ∀ i, i < children.size →
      journal (childKey key i) = children[i]!.map toJson) :
    JournalDb.get raw key journal = (some (toJson (Result.settle children)), journal) := by
  have array : ((List.range children.size).map (fun i => children[i]!)).toArray = children := by
    apply Array.ext
    · simp
    · intro i hi hj
      simp [getElem!_pos, hj]
  simp only [JournalDb.get, StateT.bind, raw, bind, pure, uncached, fork]
  rw [show fromJson? (toJson children.size) = Except.ok children.size from rfl]
  simp only [StateT.bind, StateT.pure, bind, pure]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [read_loop (slots := fun i => children[i]!)]
  · simp [array, StateT.pure, pure]
  · intro i member acc
    have stored := slots i (List.mem_range.mp member)
    cases value : children[i]! with
    | none => simp [value] at stored; simp [StateT.bind, StateT.pure, bind, pure, stored]
    | some outcome =>
      simp only [value, Option.map_some] at stored
      simp [StateT.bind, StateT.pure, bind, pure, stored, exit_roundtrip]

end LeanCloud.Proofs.JournalAdapter
