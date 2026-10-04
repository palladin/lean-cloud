import LeanCloudCli.Model

namespace LeanCloudCli.Process

/-- Preserve split UTF-8 sequences and CRLF across pipe reads. -/
structure Decoder where
  pending : ByteArray := ByteArray.empty
  afterCR : Bool := false

def decode (decoder : Decoder) (chunk : ByteArray) (finished := false) : String × Decoder := Id.run do
  let bytes := decoder.pending ++ chunk
  let mut index := 0
  let mut text := ""
  let mut afterCR := decoder.afterCR
  while index < bytes.size do
    let byte := bytes[index]!
    let count := if byte ≥ 0xC2 && byte ≤ 0xDF then 2
      else if byte ≥ 0xE0 && byte ≤ 0xEF then 3
      else if byte ≥ 0xF0 && byte ≤ 0xF4 then 4 else 1
    if !finished && index + count > bytes.size then break
    let decoded := bytes.utf8DecodeChar? index
    let char := decoded.getD '�'
    index := index + if decoded.isSome then char.utf8Size else 1
    if char == '\r' then text := text.push '\n'
    else if char == '\n' then
      if !afterCR then text := text.push '\n'
    else text := text ++ safe (String.singleton char)
    afterCR := char == '\r'
  return (text, ⟨bytes.extract index bytes.size, afterCR⟩)

private structure Tail where
  lines : Array String := #[]
  pending : String := ""

private def lastLines (lines : Array String) : Array String :=
  lines.extract (lines.size - 20) lines.size

private def Tail.append (tail : Tail) (text : String) : Tail := Id.run do
  let parts := (tail.pending ++ text).splitOn "\n"
  -- Bound memory even when a tool emits one enormous line. The disk log is uncut.
  let clip (line : String) := if line.length ≤ 1024 then line
    else "…" ++ String.ofList (line.toList.drop (line.length - 1023))
  return ⟨lastLines (tail.lines ++ (parts.dropLast.map clip).toArray), clip parts.getLast!⟩

private def Tail.text (tail : Tail) : String :=
  String.intercalate "\n" (lastLines (tail.lines ++
    (if tail.pending.isEmpty then #[] else #[tail.pending]))).toList

private def writeOutput (out err : String) : Cli Unit := do
  unless out.isEmpty do request (.write out)
  unless err.isEmpty do request (.write err true)
  unless out.isEmpty && err.isEmpty do request .flush

private partial def drain (id : ProcessId) (consume : String → String → Cli Unit)
    (stdout stderr : Decoder := {}) (tail : Tail := {}) : Cli (UInt32 × Tail) := do
  let chunk ← request (.pollProcess id 50)
  let (out, stdout) := decode stdout chunk.stdout chunk.exitCode.isSome
  let (err, stderr) := decode stderr chunk.stderr chunk.exitCode.isSome
  consume out err
  let tail := (tail.append out).append err
  if let some code := chunk.exitCode then
    return (code, tail)
  drain id consume stdout stderr tail

private def finishOutput : Cli Unit := do
  -- Keep the next CLI message separate from an unterminated final output line.
  request (.write "\n")
  request .flush

/-- Consume output incrementally; only a bounded tail stays in memory. -/
def stream (command : String) (args : Array String) : Cli UInt32 := do
  let id ← request (.startProcess command args)
  try
    let (code, _) ← drain id writeOutput
    finishOutput
    pure code
  finally request (.closeProcess id)

/-- Save decoded plain-text output incrementally in both modes. Quiet failures
    display the last 20 lines; verbose mode displays every chunk as it arrives.
    The caller supplies a fresh log path whose parent directory already exists. -/
def runLogged (command : String) (args : Array String) (log : System.FilePath)
    (verbose := false) : Cli Unit := do
  request (.writeFile log "")
  try
    let id ← request (.startProcess command args)
    let (code, tail) ← try
      drain id (fun out err => do
        unless out.isEmpty && err.isEmpty do request (.appendFile log (out ++ err))
        if verbose then writeOutput out err)
      finally request (.closeProcess id)
    if verbose then finishOutput
    unless code == 0 do
      unless verbose || tail.text.isEmpty do
        printError ("Last output (up to 20 lines):\n" ++ tail.text)
        request .flush
      throw s!"{command} exited with code {code}."
  catch error =>
    throw s!"{error} Output log (may be partial): {log}"

end LeanCloudCli.Process
