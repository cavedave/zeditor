import ZEditor.Spec.Doc3

/-!
# Exhaustive check of the Doc3 proof obligation

PO 1 for Doc3 (printed pp.79–80): from any Doc3 state, an edit operation
followed by `RemTrailWS` and `RemTrailNL` gives a state satisfying the Doc3
invariant. The book argues this informally. This file checks it by
computation on every document up to a given length over the characters
`a`, space and newline, at every cursor position, for every operation.

This is testing, not proof. The executable operations follow the definitions
(and the witnesses built in `Total.lean` and `Doc3.lean`) but are not
themselves proved equal to them.
-/

namespace ZEditor.Check

open ZEditor

/-- A document as the characters left and right of the cursor. -/
abbrev Chars := List Char × List Char

/-- `Right OP ≙ Mirror ; OP ; Mirror` on character pairs. -/
def right (f : Chars → Option Chars) : Chars → Option Chars := fun (l, r) =>
  (f (r.reverse, l.reverse)).map fun (l', r') => (r'.reverse, l'.reverse)

/-- The left operations; `none` means the error case (state unchanged). -/
def leftMvChar : Chars → Option Chars
  | (l, r) => if l = [] then none else some (l.dropLast, l.getLastD ' ' :: r)
def leftMvWord : Chars → Option Chars
  | (l, r) => if l = [] then none else
      let W := words l; some (FW W.dropLast, W.getLastD [] ++ r)
def leftMvLine : Chars → Option Chars
  | (l, r) => if l = [] then none else
      let L := lines l; some (FL L.dropLast, L.getLastD [] ++ r)
def leftDelChar : Chars → Option Chars
  | (l, r) => if l = [] then none else some (l.dropLast, r)
def leftDelWord : Chars → Option Chars
  | (l, r) => if l = [] then none else some (FW (words l).dropLast, r)
def leftDelLine : Chars → Option Chars
  | (l, r) => if l = [] then none else some (FL (lines l).dropLast, r)
def mvBottom : Chars → Option Chars
  | (l, r) => if r = [] then none else some (l ++ r, [])
def insChar (x : Char) (spaces : Nat) : Chars → Option Chars
  | (l, r) => if x = tab then some (l ++ List.replicate spaces sp, r) else some (l ++ [x], r)

/-- Every operation of `EditOps1` (with the C reading of word and line moves),
with a label. A tab may insert any positive number of spaces; we try 1 and 2. -/
def ops : List (String × (Chars → Option Chars)) :=
  [("RightMoveChar", right leftMvChar), ("LeftMoveChar", leftMvChar),
   ("RightMoveWord", right leftMvWord), ("LeftMoveWord", leftMvWord),
   ("RightMoveLine", right leftMvLine), ("LeftMoveLine", leftMvLine),
   ("MoveToTop", right mvBottom), ("MoveToBot", mvBottom),
   ("RightDeleteChar", right leftDelChar), ("LeftDeleteChar", leftDelChar),
   ("RightDeleteWord", right leftDelWord), ("LeftDeleteWord", leftDelWord),
   ("RightDeleteLine", right leftDelLine), ("LeftDeleteLine", leftDelLine),
   ("InsertChar a", insChar 'a' 0), ("InsertChar sp", insChar sp 0),
   ("InsertChar nl", insChar nl 0),
   ("InsertChar tab(1)", insChar tab 1), ("InsertChar tab(2)", insChar tab 2)]

/-- The Doc2 display of a document: lines and cursor `(x, y)`. -/
def display (c : Chars) : List (List Char) × Nat × Nat :=
  let L := FDLinv c.1
  (FDLinv (c.1 ++ c.2), (L.getLastD []).length + 1, L.length)

def visibleB (l : List Char) : Bool := l.getLast? != some sp
def visibleseqB (L : List (List Char)) : Bool := L == [[]] || L.getLast? != some []

/-- The Doc3 invariant, computed. -/
def inv3 (c : Chars) : Bool :=
  let (L, x, y) := display c
  let cur := L.getD (y - 1) []
  (List.range L.length).all (fun i => i + 1 == y || visibleB (L.getD i [])) &&
  visibleB (cur.drop (x - 1)) && visibleseqB (L.drop y)

/-- Characters of the display `L` with cursor `(x, y)` (as `Doc2.ofDisplay`). -/
def ofDisplay (L : List (List Char)) (x y : Nat) : Chars :=
  let cur := L.getD (y - 1) []
  (FDL (L.take (y - 1) ++ [cur.take (x - 1)]), FDL (cur.drop (x - 1) :: L.drop y))

/-- `RemTrailWS`, as constructed in `RemTrailWS_total`. -/
def remTrailWS (prevCP : Nat) (c : Chars) : Chars :=
  let (L, x, y) := display c
  let p := (FDLinv ((c.1 ++ c.2).take prevCP)).length
  if p = y then
    let cur := L.getD (y - 1) []
    ofDisplay (L.set (y - 1) (cur.take (x - 1) ++ stripSp (cur.drop (x - 1)))) x y
  else
    ofDisplay (L.set (p - 1) (stripSp (L.getD (p - 1) []))) x y

/-- `RemTrailNL`: both permitted outcomes (strip all trailing empty lines, or,
when every line below the cursor is empty, keep one). -/
def remTrailNL (c : Chars) : List Chars :=
  let (L, x, y) := display c
  let below := L.drop y
  let outs := [stripNull below] ++
    (if below ≠ [] ∧ below.all (· = []) then [[[]]] else [])
  outs.map fun B => ofDisplay (L.take y ++ B) x y

/-- All documents over `a`, space, newline of length at most `n`. -/
def docs : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [[]] ++ ((docs n).flatMap fun d => ['a', sp, nl].map (· :: d)) |>.eraseDups

/-- All Doc3 states from documents of length at most `n`. -/
def states (n : Nat) : List Chars :=
  (docs n).flatMap (fun d => (List.range (d.length + 1)).map fun k => (d.take k, d.drop k))
    |>.filter inv3

/-- Failures of PO 1: operation, before-state, after-state. -/
def failures (n : Nat) : List (String × Chars × Chars) :=
  (states n).flatMap fun s =>
    ops.flatMap fun (name, f) =>
      let m₁ := (f s).getD s
      let m₂ := remTrailWS s.1.length m₁
      (remTrailNL m₂).filterMap fun m₃ => if inv3 m₃ then none else some (name, s, m₃)

/-- Number of Doc3 states checked and number of failures. -/
def summary (n : Nat) : Nat × Nat := ((states n).length, (failures n).length)

#eval summary 6
#eval (failures 6).take 5

/-! ## Doc4: the QP cursor moves -/

/-- The QP target of each operation (`none`: the QP error case). Page height 2. -/
def qpOps : List (String × (Nat × Nat → Option (Nat × Nat))) :=
  [("CursorUpChar", fun (x, y) => if 1 < y then some (x, y - 1) else none),
   ("CursorUpPage", fun (x, y) => if 2 < y then some (x, y - 2) else none),
   ("CursorDownChar", fun (x, y) => some (x, y + 1)),
   ("CursorDownPage", fun (x, y) => some (x, y + 2)),
   ("CursorRightChar", fun (x, y) => some (x + 1, y))]

/-- The printed `PadWSNL` has an outcome only if the target line, when inside
the display, is visible. -/
def padPossible (L : List (List Char)) (qy : Nat) : Bool :=
  qy > L.length || visibleB (L.getD (qy - 1) [])

/-- `PadWSNL` as the C does it: pad the target line with spaces, or add empty
lines and a line of spaces below the document. -/
def padC (c : Chars) (qx qy : Nat) : Chars :=
  let (L, _, _) := display c
  if qy ≤ L.length then
    let l := L.getD (qy - 1) []
    ofDisplay (L.set (qy - 1) (l ++ List.replicate (qx - 1 - l.length) sp)) qx qy
  else
    ofDisplay (L ++ List.replicate (qy - L.length - 1) [] ++ [List.replicate (qx - 1) sp]) qx qy

/-- States where the printed spec leaves only "Editor full". -/
def stuck (n : Nat) : List (String × Chars) :=
  (states n).flatMap fun s =>
    let (L, x, y) := display s
    qpOps.filterMap fun (name, f) =>
      match f (x, y) with
      | some (_, qy) => if padPossible L qy then none else some (name, s)
      | none => none

/-- Failures of PO 1 for the QP moves with the C's padding: the result breaks
the Doc3 invariant or the cursor is not where the QP move put it. -/
def failures4 (n : Nat) : List (String × Chars × Chars) :=
  (states n).flatMap fun s =>
    let (_, x, y) := display s
    qpOps.flatMap fun (name, f) =>
      match f (x, y) with
      | none => []
      | some (qx, qy) =>
        let m₂ := remTrailWS s.1.length (padC s qx qy)
        (remTrailNL m₂).filterMap fun m₃ =>
          let (_, x', y') := display m₃
          if inv3 m₃ && x' == qx && y' == qy then none else some (name, s, m₃)

#eval ((stuck 6).length, (stuck 6).take 4)
-- Every stuck case is `CursorRightChar` with the cursor at the end of a line ending in a space.
#eval (stuck 6).all fun (name, (l, r)) =>
  name == "CursorRightChar" && l.getLast? == some sp && (r == [] || r.head? == some nl)
#eval ((failures4 6).length, (failures4 6).take 3)

end ZEditor.Check
