import LeanCloud.Proofs.TreeLocations
import LeanCloud.Proofs.ParallelSlots
import LeanCloud.JournalDb
import LeanCloud.Location

/-! Expected physical records extracted from the pure control tree. This finite
list describes admitted values; it does not prepopulate storage or run replay. -/

namespace LeanCloud.Proofs
open Lean JournalDb

def ExecutionTree.exit (tree : ExecutionTree) : Exit :=
  encodeOutcome (inferInstance : Codec Json) tree.outcome

def ExecutionTree.slots (children : List ExecutionTree) : Array (Option Exit) :=
  (children.map fun tree => some tree.exit).toArray

/-- The immutable fields owned by a single command location. -/
def ExecutionTree.ownRecords (tree : ExecutionTree) (location : Location) : List (String × Json) :=
  match tree with
  | .terminal result => [(resultKey location.key, toJson (encodeOutcome (inferInstance : Codec Json) result))]
  | .delay _ => []
  | .fork children result _ =>
    (forkKey location.key, toJson children.length) ::
    (resultKey location.key, toJson (encodeOutcome (inferInstance : Codec Json) result)) ::
    List.ofFn (fun index : Fin children.length =>
      (childKey location.key index.val, toJson children[index.val].exit))

def ExecutionTree.records (tree : ExecutionTree) (location : Location) : List (String × Json) :=
  (tree.nodes location).flatMap fun (address, node) => node.ownRecords address

variable {m : Type → Type}

theorem ChildrenExpansion.slots {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α}
    {trees outcomes} (expansion : ChildrenExpansion codec branches trees)
    (evaluated : ChildrenEvaluation branches outcomes) :
    ExecutionTree.slots trees = (outcomes.map (encodeOutcome codec)).map some := by
  have encode (outcome : Except CloudError α) :
      encodeOutcome (inferInstance : Codec Json) (outcome.map codec.encode) = encodeOutcome codec outcome := by
    cases outcome <;> rfl
  have same := congrArg (List.map (fun outcome => some (encodeOutcome (inferInstance : Codec Json) outcome)))
    (expansion.outcomes evaluated)
  apply Array.toList_inj.mp
  simpa only [ExecutionTree.slots, ExecutionTree.exit, List.toList_toArray, Array.toList_map,
    List.map_map, Function.comp_def, encode] using same

/-- Each fork's expected result is obtained by the runtime's actual `settle`
function from its indexed child records. It preserves array-order errors. -/
theorem Expansion.fork_result {program : Cloud m Json} {children result next}
    (expansion : Expansion program (.fork children result next)) :
    Result.settle (ExecutionTree.slots children) =
      .completed (encodeOutcome (inferInstance : Codec Json) result) := by
  cases expansion with
  | success evaluated collected children rest
  | failure _ evaluated collected children =>
    rw [children.slots evaluated, settle_encoded, collected]
    rfl

mutual
  /-- Every stored command is itself justified by an original pure subprogram. -/
  theorem Expansion.node {program : Cloud m Json} {tree : ExecutionTree}
      (expansion : Expansion program tree) {start location : Location} {node}
      (member : (location, node) ∈ tree.nodes start) :
      ∃ subprogram : Cloud m Json, Expansion subprogram node := by
    match expansion with
    | .pure value =>
      simp only [ExecutionTree.nodes, List.mem_singleton] at member
      cases member
      exact ⟨_, .pure value⟩
    | .fail error continuation =>
      simp only [ExecutionTree.nodes, List.mem_singleton] at member
      cases member
      exact ⟨_, .fail error continuation⟩
    | .delay rest =>
      rw [ExecutionTree.nodes] at member
      exact rest.node member
    | .success evaluated collected children rest =>
      simp only [ExecutionTree.nodes, List.mem_cons, List.mem_append] at member
      rcases member with same | child | later
      · cases same; exact ⟨_, .success evaluated collected children rest⟩
      · exact children.node child
      · exact rest.node later
    | .failure continuation evaluated collected children =>
      simp only [ExecutionTree.nodes, List.append_nil, List.mem_cons] at member
      rcases member with same | child
      · cases same; exact ⟨_, .failure continuation evaluated collected children⟩
      · exact children.node child
  termination_by structural expansion

  theorem ChildrenExpansion.node {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α}
      {trees} (expansion : ChildrenExpansion codec branches trees) {parent location : Location} {offset node}
      (member : (location, node) ∈ ExecutionTree.childrenNodes trees parent offset) :
      ∃ subprogram : Cloud m Json, Expansion subprogram node := by
    match expansion with
    | .empty .. => simp [ExecutionTree.childrenNodes] at member
    | .cons head tail =>
      rw [ExecutionTree.childrenNodes] at member
      rcases List.mem_append.mp member with first | later
      · exact head.node first
      · exact tail.node later
  termination_by structural expansion
end

end LeanCloud.Proofs
