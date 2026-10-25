import CubeAndConquer.Files

namespace CubeAndConquer
open Lean LeanCloud

abbrev Cube := List Int

structure CNF where
  variables : Nat
  clauses : Array (Array Int)
  deriving Repr, BEq, Inhabited

def words (line : String) : Array String :=
  (((line.split Char.isWhitespace).filter (fun token => !token.isEmpty)).map
    (fun token => token.toString)).toArray

/-- Pure DIMACS parser used by the small-formula differential tests. -/
def parseCNF (text : String) : Except String CNF := do
  let mut header : Option (Nat × Nat) := none
  let mut clauses := #[]
  let mut clause := #[]
  for line in text.splitOn "\n" do
    let tokens := words line
    if tokens.isEmpty || tokens[0]! == "c" then continue
    if tokens[0]! == "p" then
      unless header.isNone && tokens.size == 4 && tokens[1]! == "cnf" do
        throw "Expected one 'p cnf VARIABLES CLAUSES' header"
      let some variables := tokens[2]!.toNat? | throw "Invalid variable count"
      let some count := tokens[3]!.toNat? | throw "Invalid clause count"
      header := some (variables, count)
    else
      let some (variables, count) := header | throw "Clause before DIMACS header"
      for token in tokens do
        let some literal := token.toInt? | throw s!"Invalid DIMACS literal: {token}"
        if literal == 0 then
          clauses := clauses.push clause
          clause := #[]
          unless clauses.size ≤ count do throw "More clauses than declared"
        else
          unless literal.natAbs ≤ variables do throw "Literal outside declared variable range"
          clause := clause.push literal
  let some (variables, count) := header | throw "Missing DIMACS header"
  unless clause.isEmpty do throw "Missing final clause terminator"
  unless clauses.size == count do throw "Clause count does not match DIMACS header"
  return ⟨variables, clauses⟩

def CNF.dimacs (cnf : CNF) (cube : Cube := []) : String :=
  s!"p cnf {cnf.variables} {cnf.clauses.size + cube.length}\n" ++
    String.join (cnf.clauses.toList.map fun clause =>
      String.intercalate " " (clause.toList.map toString) ++ " 0\n") ++
    String.join (cube.map fun literal => s!"{literal} 0\n")

def literalHolds (model : Array Bool) (literal : Int) : Bool :=
  literal != 0 && literal.natAbs ≤ model.size &&
    model[literal.natAbs - 1]! == (literal > 0)

def CNF.checkModel (cnf : CNF) (model : Array Bool) : Bool :=
  model.size == cnf.variables && cnf.clauses.all (fun clause => clause.any (literalHolds model))

/-- Missing variables are completed with false; the completed assignment must
still satisfy every original clause. Conflicting/out-of-range values are errors. -/
def parseModel (cnf : CNF) (output : String) : Except String (Array Bool) := do
  let mut values : Array (Option Bool) := Array.replicate cnf.variables none
  let mut ended := false
  for line in output.splitOn "\n" do
    let tokens := words line
    if tokens.isEmpty || tokens[0]! != "v" then continue
    for token in tokens.toList.drop 1 do
      unless !ended do throw "Model data after terminator"
      let some literal := token.toInt? | throw "Invalid model literal"
      if literal == 0 then ended := true
      else
        unless literal.natAbs ≤ cnf.variables do throw "Model literal outside variable range"
        let index := literal.natAbs - 1
        let value := literal > 0
        if let some previous := values[index]! then
          unless previous == value do throw "Conflicting model assignments"
        values := values.set! index (some value)
  unless ended do throw "Missing model terminator"
  let model := values.map (·.getD false)
  unless cnf.checkModel model do throw "Model does not satisfy the original CNF"
  return model

/-- Each internal node must contain both signs of one variable. Leaves are
exact cube paths, so a missing, repeated or prefix-overlapping leaf is rejected. -/
private def completeTree : Nat → List Cube → Bool
  | 0, _ => false
  | _ + 1, [[]] => true
  | fuel + 1, cubes@((literal :: _) :: _) =>
      if cubes.all (fun cube => cube.head?.any (fun head => head.natAbs == literal.natAbs)) then
        completeTree fuel ((cubes.filter (fun cube => cube.head? == some literal)).map List.tail) &&
        completeTree fuel ((cubes.filter (fun cube => cube.head? == some (-literal))).map List.tail)
      else false
  | _, _ => false

def validateCube (variables : Nat) (cube : Cube) : Except String Unit := do
  unless cube.all (fun literal => literal != 0 && literal.natAbs ≤ variables) do
    throw "Cube literal outside variable range"
  unless (cube.map Int.natAbs).Nodup do throw "Repeated variable in cube"

def validateCubes (variables : Nat) (cubes : Array Cube) : Except String Unit := do
  for cube in cubes do validateCube variables cube
  unless completeTree (variables + 1) cubes.toList do throw "Cubes do not form a complete split tree"

def parseCubes (variables maxCubes : Nat) (text : String) : Except String (Array Cube) := do
  let mut cubes : Array Cube := #[]
  for line in text.splitOn "\n" do
    let tokens := words line
    if tokens.isEmpty || tokens[0]! == "c" then continue
    unless tokens[0]! == "a" do throw "Expected a cube line: a LITERALS 0"
    let literals : List Int ← (tokens.toList.drop 1).mapM fun token =>
      match token.toInt? with
      | some value => pure value
      | none => throw "Invalid cube literal"
    let 0 :: reversed := literals.reverse | throw "Missing cube terminator"
    cubes := cubes.push reversed.reverse
    unless cubes.size ≤ maxCubes do throw "Cuber exceeded the cube limit"
  validateCubes variables cubes
  return cubes

structure Request where
  cnf : FileRef
  depth : Nat := 10
  splitDepth : Nat := 5
  cubesPerJob : Nat := 32
  maxCubes : Nat := 4096
  seconds : Nat := 300
  verifySeconds : Nat := 600
  deriving Repr, BEq, ToJson, FromJson

def Request.validate (request : Request) : Except String Unit := do
  request.cnf.validate
  unless request.depth ≤ 64 do throw "depth must be between 0 and 64"
  unless 0 < request.splitDepth && request.splitDepth ≤ 8 do throw "splitDepth must be between 1 and 8"
  unless 0 < request.cubesPerJob && request.cubesPerJob ≤ 256 do throw "cubesPerJob must be between 1 and 256"
  unless 0 < request.maxCubes && request.maxCubes ≤ 100000 do throw "maxCubes must be between 1 and 100000"
  unless 2 ^ request.depth ≤ request.maxCubes do
    throw "The depth's maximum leaf count (2^depth) exceeds maxCubes"
  unless 0 < request.seconds && request.seconds ≤ 86400 do throw "seconds must be between 1 and 86400"
  unless 0 < request.verifySeconds && request.verifySeconds ≤ 86400 do
    throw "verifySeconds must be between 1 and 86400"

/-- Every successful answer carries a certificate, not a solver status alone.
UNSAT certificates are checked against the exact stored formula including units. -/
inductive Answer where
  | sat (model : FileRef)
  | unverified (formula proof : FileRef)
  | unsat (formula proof verification : FileRef)
  | unknown (reason : String)
  | error (reason : String)
  deriving Repr, BEq, ToJson, FromJson, Inhabited

structure CubePlan where
  input : FileRef
  variables : Nat
  cubes : Array Cube
  deriving Repr, BEq, ToJson, FromJson

structure CubeResult where
  cube : Cube
  answer : Answer
  log : FileRef
  deriving Repr, BEq, ToJson, FromJson

inductive Cubing where
  /-- New decision paths relative to the parent cube. -/
  | split (children : Array Cube)
  /-- The cuber did not make progress; solve the parent with Kissat. -/
  | leaf
  | finished (result : CubeResult)
  deriving Repr, BEq, ToJson, FromJson

/-- Check every split before creating cloud branches. The extensions cover the
parent, use fresh variables, and consume at most this call's decision budget. -/
def validateSplit (parent : Cube) (depth : Nat) (children : Array Cube) : Except String Unit := do
  unless children.size > 1 do throw "A split must make progress"
  let variables := (parent ++ children.toList.flatten).foldl (fun n lit => max n lit.natAbs) 0
  validateCubes variables children
  for child in children do
    unless !child.isEmpty && child.length ≤ depth do throw "Split exceeds its decision-depth budget"
    unless ((parent ++ child).map Int.natAbs).Nodup do throw "Split repeats a parent variable"

inductive Conclusion where
  | sat (model : FileRef)
  | unsat
  | inconclusive
  deriving Repr, BEq, ToJson, FromJson, Inhabited

structure Toolchain where
  kissat : String := "8af8e56f174b778aef3aa45af9f739b2a5f492c2"
  march : String := "705b60c6491ef2b61988b3ce6ac674be1b90571d"
  checker : String := "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"
  binaries : String
  deriving Repr, BEq, ToJson, FromJson

/-- Portable evidence bundle. An offline verifier rechecks input binding, cube
coverage, every proof, and any SAT witness without trusting this conclusion. -/
structure Bundle where
  format : String := "cube-and-conquer/bundle/v2"
  request : Request
  plan : FileRef
  results : Array CubeResult
  tools : Toolchain
  deriving Repr, BEq, ToJson, FromJson

structure Report where
  outcome : Conclusion
  bundle : FileRef
  totalCubes : Nat
  solvedCubes : Nat
  deriving Repr, BEq, ToJson, FromJson

instance : Codec Cubing := jsonCodec _ "cube-and-conquer/cubing/v3"
instance : Codec CubeResult := jsonCodec _ "cube-and-conquer/cube-result/v3"
instance : Codec Report := jsonCodec _ "cube-and-conquer/report/v3"

/-- UNSAT needs all cubes; SAT needs just one valid witness. -/
def aggregate (total : Nat) (results : Array CubeResult) : Conclusion :=
  match results.findSome? (fun result => match result.answer with | .sat model => some model | _ => none) with
  | some model => .sat model
  | none => if total > 0 && results.size == total && results.all (fun result =>
      match result.answer with | .unsat .. => true | _ => false) then .unsat else .inconclusive

end CubeAndConquer
