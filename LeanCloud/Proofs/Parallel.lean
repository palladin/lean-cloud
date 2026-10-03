import LeanCloud.ReplayInterpreter
import LeanCloud.DirectInterpreter

namespace LeanCloud.Proofs.Parallel
open Lean

/-- Representation of a direct result in the immutable replay journal. -/
def recorded (encode : α → Json) : Except CloudError α → Exit
  | .ok value => .success (encode value)
  | .error error => .failure error

private theorem sequence_map (values : List (Except ε α)) (encode : α → β) (error : ε → ε') :
    values.mapM (fun value => (value.map encode).mapError error) =
      ((values.mapM id).map (List.map encode)).mapError error := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.mapM_cons]
    rw [ih]
    cases first <;> cases rest.mapM id <;> rfl

private theorem sequence_length (outcomes : List (Except ε α)) (values : List α)
    (collected : outcomes.mapM id = .ok values) : values.length = outcomes.length := by
  induction outcomes generalizing values with
  | nil =>
    change Except.ok [] = Except.ok values at collected
    cases collected
    rfl
  | cons first rest ih =>
    rw [List.mapM_cons] at collected
    cases first with
    | error error => contradiction
    | ok value =>
      cases tail : rest.mapM id with
      | error error =>
        rw [tail] at collected
        contradiction
      | ok remaining =>
        rw [tail] at collected
        change Except.ok (value :: remaining) = Except.ok values at collected
        cases collected
        simp [ih remaining tail]

/-- Collecting successful children preserves the number of branches. -/
theorem sequence_size (outcomes : Array (Except ε α)) (values : Array α)
    (collected : outcomes.mapM id = .ok values) : values.size = outcomes.size := by
  rw [Array.mapM_eq_mapM_toList] at collected
  cases gathered : outcomes.toList.mapM id with
  | error error =>
    rw [gathered] at collected
    contradiction
  | ok remaining =>
    rw [gathered] at collected
    change Except.ok remaining.toArray = Except.ok values at collected
    cases collected
    simpa using sequence_length outcomes.toList remaining gathered

/-- Replay joins exactly the results that direct sequential parallel evaluation
would produce: values stay in source order and the first error in that order wins.
The statement holds for any encoding and any number of children. -/
theorem collect_matches_direct (outcomes : Array (Except CloudError α)) (encode : α → Json) :
    ReplayInterpreter.collect (outcomes.map (recorded encode)) =
      recorded (fun values => Json.arr (values.map encode)) (outcomes.mapM id) := by
  have decode_recorded :
      (fun outcome : Except CloudError α => match recorded encode outcome with
        | .success value => Except.ok value
        | other => Except.error other) =
        (fun outcome => (outcome.map encode).mapError Exit.failure) := by
    funext outcome
    cases outcome <;> rfl
  simp only [ReplayInterpreter.collect, Array.mapM_map, Function.comp_def]
  erw [decode_recorded]
  rw [Array.mapM_eq_mapM_toList, sequence_map, Array.mapM_eq_mapM_toList]
  cases outcomes.toList.mapM id with
  | error error => rfl
  | ok values => simp [recorded, Functor.map, Except.map, Except.mapError]

/-- The ordered reduction above is the one used by the actual direct interpreter.
Once child outcomes are available, replay's join has the same encoded result. -/
theorem parallel_join_matches_direct (blobs : BlobStorage Id) (codec : Codec α)
    (count : Nat) (branches : Fin count → Cloud Id α) :
    let outcomes := (Array.ofFnM fun index =>
      (DirectInterpreter.Internal.eval blobs (branches index)).run : Id _)
    ReplayInterpreter.collect (outcomes.map (recorded codec.encode)) =
      recorded (fun values => Json.arr (values.map codec.encode))
        (DirectInterpreter.Internal.evalControl blobs (.parallel codec count branches)).run := by
  let outcomes := (Array.ofFnM fun index =>
    (DirectInterpreter.Internal.eval blobs (branches index)).run : Id _)
  have direct :
      (DirectInterpreter.Internal.evalControl blobs (.parallel codec count branches)).run =
        outcomes.mapM id := by
    change (match outcomes.mapM id with
      | .ok values => Except.ok values
      | .error error => Except.error error) = outcomes.mapM id
    cases outcomes.mapM id <;> rfl
  dsimp only
  rw [direct]
  exact collect_matches_direct outcomes codec.encode

end LeanCloud.Proofs.Parallel
