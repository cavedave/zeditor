import ZEditor.Check
import ZEditor.Spec.Doc9

/-!
# A demonstration: type some keys and watch the editor

Runs a sequence of key presses through the executable versions of the
operations in `Check.lean` (with the C's readings of the word and line moves,
decision D3), each followed by the two tidying operations `RemTrailWS` and
`RemTrailNL`, as the Doc3 level of the specification requires. After each key it
draws the document: spaces as `·`, the cursor as `|`, and the cursor position
`(column, line)`.

Run with `lake env lean ZEditor/Demo.lean`. This is not part of the build and
not a proof: it is a way to see the specification's behaviour.
-/

namespace ZEditor.Demo

open ZEditor ZEditor.Check

/-- Look up an operation of `Check.ops` by name. -/
def op (name : String) : Chars → Option Chars :=
  ((ops.find? (·.1 == name)).map (·.2)).getD (fun _ => none)

/-- One key: the operation, then `RemTrailWS ; RemTrailNL`. An error leaves the
document unchanged. -/
def press (c : Chars) (name : String) : Chars × String :=
  match op name c with
  | some c' =>
    let m := remTrailWS c.1.length c'
    ((remTrailNL m).headD m, "OK")
  | none => (c, "error: nothing to move over")

/-- Draw a document: one row per display line, spaces as `·`, cursor as `|`. -/
def render (c : Chars) : String :=
  let (L, x, y) := display c
  let showLine (l : List Char) : String := String.ofList (l.map fun ch => if ch = ' ' then '·' else ch)
  let rows := (List.range L.length).map fun i =>
    let l := L.getD i []
    let body := if i + 1 = y then showLine (l.take (x - 1)) ++ "|" ++ showLine (l.drop (x - 1))
                else showLine l
    s!"    {i + 1}│ {body}"
  String.intercalate "\n" rows ++ s!"\n     └ cursor at column {x}, line {y}"

/-- Keys: a name from `Check.ops`, or `type "text"` for several InsertChar. -/
inductive Key where
  | k (name : String)
  | type (text : String)

/-- Insert any character (the demo's `ops` table only has `a`, space, newline). -/
def pressChar (c : Chars) (ch : Char) : Chars :=
  let c' := (insChar ch 0 c).getD c
  let m := remTrailWS c.1.length c'
  (remTrailNL m).headD m

def run (c : Chars) : Key → Chars × String
  | .k n => press c n
  | .type t => (t.toList.foldl pressChar c, s!"typed \"{t}\"")

def script : List Key :=
  [.type "the cat sat",
   .k "LeftMoveWord", .k "LeftMoveWord",
   .k "RightDeleteWord",
   .k "MoveToTop", .k "LeftMoveChar",
   .k "MoveToBot",
   .type " on mats ",
   .k "InsertChar nl",
   .type "the end",
   .k "LeftMoveLine", .k "LeftMoveLine",
   .k "RightMoveWord", .k "RightMoveWord"]

def describe : Key → String
  | .k n => n
  | .type t => s!"type \"{t}\""

/-- A small window onto the display (Doc9): 12 columns by 2 lines, moved only
when the cursor would leave it, as `WindowPolicy` allows. -/
def winP : WinParams := ⟨12, 2, by decide, by decide⟩

def window (c : Chars) (ox oy : Nat) : Nat × Nat × String :=
  let (L, x, y) := display c
  let ox := if ox < x ∧ x ≤ ox + winP.winWidth then ox else x - 1
  let oy := if oy < y ∧ y ≤ oy + winP.winHeight then oy else y - 1
  let W := winLinesOf winP L ox oy
  let rows := (List.range winP.winHeight).map fun i =>
    let l := W.getD i []
    let cells := (List.range winP.winWidth).map fun j =>
      if i + 1 = y - oy ∧ j + 1 = x - ox then '▮'
      else match l[j]? with | some ' ' => '·' | some ch => ch | none => ' '
    s!"    ║{String.ofList cells}║"
  let top := "    ╔" ++ String.ofList (List.replicate winP.winWidth '═') ++ "╗"
  let bot := "    ╚" ++ String.ofList (List.replicate winP.winWidth '═') ++ "╝"
  (ox, oy, String.intercalate "\n" ([top] ++ rows ++ [bot]) ++
    s!"  offsets ({ox}, {oy})")

def demo : IO Unit := do
  let mut c : Chars := ([], [])
  IO.println "Start: the empty document"
  IO.println (render c)
  for key in script do
    let (c', rep) := run c key
    c := c'
    IO.println s!"\n▶ {describe key}   [{rep}]"
    IO.println (render c)
  IO.println "\nThe same document through a 12 × 2 window (Doc9), cursor ▮:"
  let mut ox := 0
  let mut oy := 0
  for key in [Key.k "MoveToTop", .k "RightMoveWord", .k "RightMoveWord", .k "RightMoveWord",
              .k "RightMoveLine", .k "RightMoveChar"] do
    let (c', _) := run c key
    c := c'
    let (ox', oy', pic) := window c ox oy
    ox := ox'; oy := oy'
    IO.println s!"\n▶ {describe key}"
    IO.println pic

#eval demo

end ZEditor.Demo
