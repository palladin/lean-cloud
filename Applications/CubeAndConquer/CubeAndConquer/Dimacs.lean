import CubeAndConquer.Model

namespace CubeAndConquer.Dimacs

structure Info where
  variables : Nat
  clauses : Nat
  deriving BEq, Repr

/-- Read in fixed blocks, accepting arbitrary clause line breaks. The line bound
protects against malformed inputs; normal DIMACS can wrap clauses freely. -/
def lines (path : System.FilePath) (action : String → IO Unit) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .read
  let mut pending := ""
  repeat
    let bytes ← handle.read 65536
    if bytes.isEmpty then break
    let some text := String.fromUTF8? bytes | throw (IO.userError "DIMACS/tools require ASCII text")
    unless text.toList.all (fun c => c.toNat < 128) do throw (IO.userError "DIMACS/tools require ASCII text")
    let parts := (pending ++ text).splitOn "\n"
    pending := parts.getLast!
    unless pending.utf8ByteSize ≤ 8 * 1024 * 1024 do
      throw (IO.userError "Text line exceeds 8 MiB; wrap DIMACS clauses across lines")
    for line in parts.dropLast do
      unless line.utf8ByteSize ≤ 8 * 1024 * 1024 do
        throw (IO.userError "Text line exceeds 8 MiB; wrap DIMACS clauses across lines")
      action line
  if !pending.isEmpty then action pending

/-- Scan without retaining the clause database. If a model is supplied, check
it against every original clause while scanning. -/
def scan (path : System.FilePath) (model : Option (Array Bool) := none) : IO Info := do
  let header ← IO.mkRef (none : Option Info)
  let count ← IO.mkRef 0
  let openClause ← IO.mkRef false
  let holds ← IO.mkRef false
  lines path fun line => do
    let tokens := words line
    if tokens.isEmpty || tokens[0]! == "c" then return
    if tokens[0]! == "p" then
      unless (← header.get).isNone && tokens.size == 4 && tokens[1]! == "cnf" do
        throw (IO.userError "Expected one DIMACS header")
      let some variables := tokens[2]!.toNat? | throw (IO.userError "Invalid variable count")
      let some clauses := tokens[3]!.toNat? | throw (IO.userError "Invalid clause count")
      unless variables < 2147483647 && clauses < 2147483647 do
        throw (IO.userError "DIMACS counts exceed native solver integer range")
      if let some model := model then
        unless model.size == variables do throw (IO.userError "Model size differs from CNF")
      header.set (some ⟨variables, clauses⟩)
    else
      let some info ← header.get | throw (IO.userError "Clause before DIMACS header")
      for token in tokens do
        let some literal := token.toInt? | throw (IO.userError "Invalid DIMACS literal")
        if literal == 0 then
          if model.isSome && !(← holds.get) then throw (IO.userError "Model falsifies a CNF clause")
          count.modify (· + 1)
          unless (← count.get) ≤ info.clauses do throw (IO.userError "Too many clauses")
          openClause.set false
          holds.set false
        else
          unless literal.natAbs ≤ info.variables do throw (IO.userError "Literal outside DIMACS range")
          openClause.set true
          if let some model := model then holds.modify (· || literalHolds model literal)
  let some info ← header.get | throw (IO.userError "Missing DIMACS header")
  unless !(← openClause.get) && (← count.get) == info.clauses do
    throw (IO.userError "Truncated CNF or wrong clause count")
  return info

/-- Preserve the input formula and append cube units, changing only its header.
The resulting file is stored with the proof, so it can be checked independently. -/
def withCube (source target : System.FilePath) (info : Info) (cube : Cube) : IO Unit := do
  unless info.clauses + cube.length < 2147483647 do throw (IO.userError "Too many cube clauses")
  let output ← IO.FS.Handle.mk target .write
  lines source fun line => do
    if (words line)[0]? == some "p" then
      output.putStr s!"p cnf {info.variables} {info.clauses + cube.length}\n"
    else output.putStr (line ++ "\n")
  for literal in cube do output.putStr s!"{literal} 0\n"
  output.flush

def model (path : System.FilePath) (variables : Nat) : IO (Array Bool) := do
  let values ← IO.mkRef (Array.replicate variables (none : Option Bool))
  let ended ← IO.mkRef false
  lines path fun line => do
    let tokens := words line
    unless tokens[0]? == some "v" do return
    for token in tokens.toList.drop 1 do
      unless !(← ended.get) do throw (IO.userError "Model data after terminator")
      let some literal := token.toInt? | throw (IO.userError "Invalid model literal")
      if literal == 0 then ended.set true
      else
        unless literal.natAbs ≤ variables do throw (IO.userError "Model literal outside range")
        let index := literal.natAbs - 1
        let value := literal > 0
        if let some previous := (← values.get)[index]! then
          unless previous == value do throw (IO.userError "Conflicting model assignments")
        values.modify (·.set! index (some value))
  unless ← ended.get do throw (IO.userError "Model terminator missing")
  return (← values.get).map (·.getD false)

def writeModel (path : System.FilePath) (values : Array Bool) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .write
  handle.putStr "s SATISFIABLE\n"
  for first in [: (values.size + 15) / 16] do
    handle.putStr "v"
    for i in [first * 16 : min (first * 16 + 16) values.size] do
      handle.putStr s!" {if values[i]! then Int.ofNat (i+1) else -Int.ofNat (i+1)}"
    handle.putStr "\n"
  handle.putStr "v 0\n"
  handle.flush

end CubeAndConquer.Dimacs
