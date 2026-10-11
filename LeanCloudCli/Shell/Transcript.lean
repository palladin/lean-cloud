import LeanCloudCli.Styled

namespace LeanCloudCli.Shell

/-- Positions refer to original lines, so selection survives wrapping and resizing. -/
structure Position where
  line : Nat
  column : Nat
  deriving BEq, Repr, Inhabited

private def Position.before (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column < b.column)

structure Selection where
  anchor : Position
  focus : Position
  dragging : Bool := false
  deriving BEq, Repr

def Selection.bounds (selection : Selection) : Position × Position :=
  if selection.focus.before selection.anchor then (selection.focus, selection.anchor)
  else (selection.anchor, selection.focus)

structure TranscriptRow where
  origin : Position
  text : Styled.Line
  deriving Inhabited, Repr

/-- The transcript owns output; the terminal is only a viewport. `top = none`
follows new output, while a selected row stays put as a command streams. -/
structure Transcript where
  lines : Array Styled.Line := #[#[]]
  rows : Array TranscriptRow := #[⟨⟨0, 0⟩, #[]⟩]
  width : Nat := 80
  tailStart : Nat := 0
  top : Option Nat := none
  selection : Option Selection := none
  deriving Repr

namespace Transcript

/-- Common terminal cell widths (including CJK, emoji and combining accents).
Positions for copying still count original characters, never padding cells. -/
def cellWidth (c : Char) : Nat :=
  let n := c.toNat
  if (0x300 ≤ n && n ≤ 0x36f) || (0x1ab0 ≤ n && n ≤ 0x1aff) ||
      (0x1dc0 ≤ n && n ≤ 0x1dff) || (0x20d0 ≤ n && n ≤ 0x20ff) ||
      (0xfe00 ≤ n && n ≤ 0xfe0f) || (0xfe20 ≤ n && n ≤ 0xfe2f) || n == 0x200d then 0
  else if (0x1100 ≤ n && n ≤ 0x115f) || n == 0x2329 || n == 0x232a ||
      (0x2e80 ≤ n && n ≤ 0xa4cf) || (0xac00 ≤ n && n ≤ 0xd7a3) ||
      (0xf900 ≤ n && n ≤ 0xfaff) || (0xfe10 ≤ n && n ≤ 0xfe19) ||
      (0xfe30 ≤ n && n ≤ 0xfe6f) || (0xff00 ≤ n && n ≤ 0xff60) ||
      (0xffe0 ≤ n && n ≤ 0xffe6) || (0x1f300 ≤ n && n ≤ 0x1faff) ||
      (0x20000 ≤ n && n ≤ 0x3fffd) then 2
  else 1

private def wrap (line : Styled.Line) (index width : Nat) : Array TranscriptRow := Id.run do
  let mut rows := #[]
  let mut start := 0
  let mut column := 0
  let mut cells := 0
  for c in (Styled.plain line).toList do
    let size := cellWidth c
    if cells + size > max 2 width && cells > 0 then
      rows := rows.push ⟨⟨index, start⟩, Styled.slice line start column⟩
      start := column
      cells := 0
    cells := cells + size
    column := column + 1
  return rows.push ⟨⟨index, start⟩, Styled.slice line start column⟩

def resize (transcript : Transcript) (width : Nat) : Transcript := Id.run do
  let width := max 2 width
  if width == transcript.width then return transcript
  let anchor := transcript.top.bind fun top => transcript.rows[top]?.map (·.origin)
  let mut rows := #[]
  let mut tailStart := 0
  for (line, index) in transcript.lines.toList.zipIdx do
    tailStart := rows.size
    rows := rows ++ wrap line index width
  let top := anchor.map fun position =>
    (rows.findIdx? fun row => position.before row.origin).getD rows.size - 1
  return { transcript with width, rows, tailStart, top }

private def extend (line : Styled.Line) (text : String) (color : Styled.Color) : Styled.Line :=
  if text.isEmpty then line else
  match line.back? with
  | some span => if span.color == color then line.set! (line.size - 1) ⟨span.text ++ text, color⟩
      else line.push ⟨text, color⟩
  | none => #[⟨text, color⟩]

/-- Incrementally wrap only the unfinished line and the new output. Nothing is
discarded, and copying never inserts newlines for soft-wrapped screen rows. -/
def append (transcript : Transcript) (text : String) (color : Styled.Color := .normal) : Transcript := Id.run do
  let parts := text.splitOn "\n"
  let mut lines := transcript.lines
  lines := lines.set! (lines.size - 1) (extend (lines.back?.getD #[]) (Styled.sanitize parts.head!) color)
  for part in parts.drop 1 do
    lines := lines.push (Styled.text (Styled.sanitize part) color)
  let mut rows := transcript.rows.extract 0 transcript.tailStart
  let mut tailStart := transcript.tailStart
  for index in [transcript.lines.size - 1:lines.size] do
    tailStart := rows.size
    rows := rows ++ wrap lines[index]! index transcript.width
  return { transcript with lines, rows, tailStart }

def appendStyled (transcript : Transcript) (line : Styled.Line) : Transcript :=
  (line.foldl (fun transcript span => transcript.append span.text span.color) transcript).append "\n"

def plain (transcript : Transcript) : String :=
  String.intercalate "\n" (transcript.lines.toList.map Styled.plain)

def visibleStart (transcript : Transcript) (height : Nat) : Nat :=
  min (transcript.top.getD (transcript.rows.size - height)) (transcript.rows.size - height)

def scroll (transcript : Transcript) (height : Nat) (up : Bool) (amount : Nat) : Transcript :=
  let last := transcript.rows.size - height
  let current := transcript.visibleStart height
  let target := if up then current - amount else min last (current + amount)
  { transcript with top := if target == last then none else some target }

def selectAll (transcript : Transcript) : Transcript :=
  { transcript with selection := some ⟨⟨0, 0⟩,
      ⟨transcript.lines.size - 1, Styled.length (transcript.lines.back?.getD #[])⟩, false⟩ }

def hasSelection (transcript : Transcript) : Bool :=
  transcript.selection.any fun selection => selection.anchor != selection.focus

def selectedText (transcript : Transcript) : String := Id.run do
  let some selection := transcript.selection | return ""
  let (start, stop) := selection.bounds
  let mut lines := #[]
  for index in [start.line:min transcript.lines.size (stop.line + 1)] do
    let line := transcript.lines[index]!
    lines := lines.push (Styled.plain (Styled.slice line
      (if index == start.line then start.column else 0)
      (if index == stop.line then stop.column else Styled.length line)))
  return String.intercalate "\n" lines.toList

def positionAt (transcript : Transcript) (height row column : Nat) : Position := Id.run do
  let index := min (transcript.rows.size - 1) (transcript.visibleStart height + min (height - 1) row)
  let entry := transcript.rows[index]!
  let mut offset := 0
  let mut cells := 0
  for c in (Styled.plain entry.text).toList do
    if cells + cellWidth c > column then break
    cells := cells + cellWidth c
    offset := offset + 1
  return ⟨entry.origin.line, entry.origin.column + offset⟩

def visible (transcript : Transcript) (height : Nat) : Array Styled.Line := Id.run do
  let start := transcript.visibleStart height
  return (transcript.rows.extract start (start + height)).map fun row => Id.run do
    let some selection := transcript.selection | return row.text
    let (first, last) := selection.bounds
    let line := row.origin.line
    if line < first.line || line > last.line then return row.text
    let lo := if line == first.line then first.column - row.origin.column else 0
    let hi := if line == last.line then last.column - row.origin.column else Styled.length row.text
    let selected := (Styled.slice row.text lo hi).map fun span => { span with color := .selected }
    return Styled.slice row.text 0 lo ++ selected ++ Styled.slice row.text hi (Styled.length row.text)

end Transcript
end LeanCloudCli.Shell
