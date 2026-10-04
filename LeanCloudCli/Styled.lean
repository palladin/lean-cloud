import Lean

namespace LeanCloudCli.Styled

inductive Color where
  | normal | muted | green | yellow | red | cyan | magenta | blue | header | selected
  deriving BEq, Repr

private def Color.escape : Color → String
  | .normal => "\x1b[0m" | .muted => "\x1b[0;2m"
  | .green => "\x1b[0;32m" | .yellow => "\x1b[0;33m" | .red => "\x1b[0;1;31m"
  | .cyan => "\x1b[0;36m" | .magenta => "\x1b[0;35m" | .blue => "\x1b[0;34m"
  | .header => "\x1b[0;30;46m" | .selected => "\x1b[0;1;37;44m"

structure Span where
  text : String
  color : Color := .normal
  deriving BEq, Repr

abbrev Line := Array Span

def text (value : String) (color : Color := .normal) : Line := #[⟨value, color⟩]

def sanitize (value : String) : String := String.ofList (value.toList.map fun c =>
  if c.toNat < 32 || (127 ≤ c.toNat && c.toNat ≤ 159) then ' ' else c)

def length (line : Line) : Nat := line.foldl (fun n span => n + span.text.length) 0

def slice (line : Line) (start stop : Nat) : Line := Id.run do
  let mut offset := 0
  let mut result := #[]
  for span in line do
    let value := String.ofList (span.text.toList.drop (start - offset) |>.take (stop - max start offset))
    unless value.isEmpty do result := result.push { span with text := value }
    offset := offset + span.text.length
  return result

def statusColor (status : String) : Color :=
  if ["running", "completed", "healthy", "up", "done"].any (fun word => status.startsWith word) then .green
  else if ["failed", "error", "cancelled", "killed", "unavailable"].any (fun word => status.startsWith word) then .red
  else if ["paused", "pausing", "killing", "pending", "join", "partial", "waiting"].any (fun word => status.startsWith word) then .yellow
  else .muted

/-- Clip visible text before adding our own colors. Source, logs and node names
never get to supply terminal escape sequences. Every colored line resets. -/
def render (line : Line) (width : Nat) (color := false) : String := Id.run do
  let clipped := width < length line
  let mut remaining := if clipped then width - 1 else width
  let mut result := ""
  for span in line do
    let value := String.ofList ((sanitize span.text).toList.take remaining)
    remaining := remaining - value.length
    unless value.isEmpty do
      result := result ++ (if color then span.color.escape else "") ++ value
  if clipped && width > 0 then result := result ++ (if color then Color.muted.escape else "") ++ "…"
  return result ++ (if color then Color.normal.escape else "")

def plain (line : Line) : String := render line (length line)

end LeanCloudCli.Styled
