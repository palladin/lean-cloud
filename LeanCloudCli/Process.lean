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

private partial def drain (id : ProcessId) (stdout stderr : Decoder := {}) : Cli UInt32 := do
  let chunk ← request (.pollProcess id 50)
  let (out, stdout) := decode stdout chunk.stdout chunk.exitCode.isSome
  let (err, stderr) := decode stderr chunk.stderr chunk.exitCode.isSome
  unless out.isEmpty do request (.write out)
  unless err.isEmpty do request (.write err true)
  unless out.isEmpty && err.isEmpty do request .flush
  if let some code := chunk.exitCode then
    -- Keep the next CLI message separate from an unterminated final output line.
    request (.write "\n")
    request .flush
    return code
  drain id stdout stderr

/-- No accumulated process log: output is consumed incrementally by the host or shell. -/
def stream (command : String) (args : Array String) : Cli UInt32 := do
  let id ← request (.startProcess command args)
  try drain id finally request (.closeProcess id)

end LeanCloudCli.Process
