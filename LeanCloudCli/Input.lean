import LeanCloudCli.Effects

namespace LeanCloudCli.Input

inductive Key where
  | text (value : String)
  | enter | tab | backTab | backspace | delete | left | right | home | end
  | up | down | pageUp | pageDown | interrupt | eof | escape | clear | killEnd
  | idle
  deriving BEq, Repr

private def sequenceKey : String → Key
  | "[A" => .up | "[B" => .down | "[C" => .right | "[D" => .left
  | "[H" | "OH" | "[1~" | "[7~" => .home
  | "[F" | "OF" | "[4~" | "[8~" => .end
  | "[3~" => .delete | "[5~" => .pageUp | "[6~" => .pageDown | "[Z" => .backTab
  | _ => .idle

private def escapeSequence : Cli String := do
  let mut sequence := ""
  for _ in [:12] do
    let byte ← request (.key 20)
    if byte == 0 then break
    sequence := sequence.push (Char.ofNat byte.toNat)
    if sequence.length == 1 then
      unless byte == 91 || byte == 79 do break
    else if byte ≥ 64 && byte ≤ 126 then break
  return sequence

/-- A bracketed paste is one edit. Embedded newlines never submit commands. -/
private partial def paste (bytes : ByteArray := ByteArray.empty) (ending : String := "") : Cli Key := do
  let byte ← request (.key 100)
  if byte == 3 then return .interrupt
  if byte == 4 then return .eof
  let bytes := if byte == 0 then bytes else bytes.push byte.toUInt8
  let ending := if byte == 0 then ending else
    let text := ending.push (Char.ofNat byte.toNat)
    String.ofList (text.toList.drop (text.length - 6))
  if ending == "\x1b[201~" then
    let some text := String.fromUTF8? (bytes.extract 0 (bytes.size - 6)) | return .idle
    return .text (String.ofList (text.toList.map fun c =>
      if c.toNat < 32 || (127 ≤ c.toNat && c.toNat ≤ 159) then ' ' else c))
  paste bytes ending

/-- Decode terminal bytes in Eff; native code only polls the terminal. -/
def read (timeoutMs : UInt32 := 100) : Cli Key := do
  let byte ← request (.key timeoutMs)
  match byte.toNat with
  | 0 => return .idle
  | 3 => return .interrupt
  | 4 => return .eof
  | 9 => return .tab
  | 10 | 13 => return .enter
  | 8 | 127 => return .backspace
  | 1 => return .home
  | 5 => return .end
  | 11 => return .killEnd
  | 21 => return .clear
  | 27 =>
    let sequence ← escapeSequence
    if sequence == "[200~" then paste
    else return if sequence.isEmpty then .escape else sequenceKey sequence
  | value =>
    if value < 32 then return .idle
    let count := if value < 128 then 1 else if value < 224 then 2 else if value < 240 then 3 else 4
    let mut bytes := ByteArray.empty.push byte.toUInt8
    for _ in [:count - 1] do
      let next ← request (.key 20)
      if next < 128 || next ≥ 192 then return .idle
      bytes := bytes.push next.toUInt8
    return match String.fromUTF8? bytes with
      | some text => .text text
      | none => .idle

end LeanCloudCli.Input
