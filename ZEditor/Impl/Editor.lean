import ZEditor.Spec.Doc9

/-!
# The editor's core (first prototype)

A small, runnable core: the document, a handful of operations, the window, and
the screen as text. No input or output happens here; `Main.lean` connects it to
a terminal.

The document is held as the specification holds it: the characters left and
right of the cursor. Every operation is followed by the two tidying operations
of Doc3 (`RemTrailWS ; RemTrailNL`), and the window follows the Doc9 window
policy. The operations follow the specification's definitions, with the C's
readings where decisions have been made (D3); they are not yet proved to meet
the specification. That is the next stage.
-/

namespace ZEditor.Impl

open ZEditor

/-- A document: the characters left and right of the cursor (`Left_Char`,
`Right_Char`). -/
abbrev Chars := List Char × List Char

/-- The Doc2 display: lines, and the cursor `(column, line)` counted from 1. -/
def display (c : Chars) : List (List Char) × Nat × Nat :=
  let L := FDLinv c.1
  (FDLinv (c.1 ++ c.2), (L.getLastD []).length + 1, L.length)

/-- The document with display lines `L` and cursor `(x, y)` (as `Doc2.ofDisplay`). -/
def ofDisplay (L : List (List Char)) (x y : Nat) : Chars :=
  let cur := L.getD (y - 1) []
  (FDL (L.take (y - 1) ++ [cur.take (x - 1)]), FDL (cur.drop (x - 1) :: L.drop y))

/-- `RemTrailWS`: remove trailing spaces from the line the cursor was on
(`prevCP` is the old cursor position, `FlagPrevCursor`). -/
def remTrailWS (prevCP : Nat) (c : Chars) : Chars :=
  let (L, x, y) := display c
  let p := (FDLinv ((c.1 ++ c.2).take prevCP)).length
  if p = y then
    let cur := L.getD (y - 1) []
    ofDisplay (L.set (y - 1) (cur.take (x - 1) ++ stripSp (cur.drop (x - 1)))) x y
  else
    ofDisplay (L.set (p - 1) (stripSp (L.getD (p - 1) []))) x y

/-- `RemTrailNL`: remove empty lines at the end of the document, below the cursor. -/
def remTrailNL (c : Chars) : Chars :=
  let (L, x, y) := display c
  ofDisplay (L.take y ++ stripNull (L.drop y)) x y

/-- The Doc3 promotion: an operation is followed by `RemTrailWS ; RemTrailNL`. -/
def tidy (prevCP : Nat) (c : Chars) : Chars := remTrailNL (remTrailWS prevCP c)

/-! ## Operations

Each returns `none` in its error case (at the top or bottom of the document),
where the document does not change. -/

/-- `InsertChar` (not tab). -/
def insertChar (ch : Char) (c : Chars) : Option Chars := some (c.1 ++ [ch], c.2)

/-- `InsertChar` of a tab: spaces to the next multiple of 4 columns (`InsTab`
allows any positive number). -/
def insertTab (c : Chars) : Option Chars :=
  let (_, x, _) := display c
  some (c.1 ++ List.replicate (4 - (x - 1) % 4) sp, c.2)

/-- `LeftDeleteChar` (Backspace). -/
def leftDeleteChar (c : Chars) : Option Chars :=
  if c.1 = [] then none else some (c.1.dropLast, c.2)

/-- `RightDeleteChar` (Delete). -/
def rightDeleteChar (c : Chars) : Option Chars :=
  match c.2 with
  | [] => none
  | _ :: r => some (c.1, r)

/-- `LeftMoveChar`. -/
def leftMoveChar (c : Chars) : Option Chars :=
  if c.1 = [] then none else some (c.1.dropLast, c.1.getLastD ' ' :: c.2)

/-- `RightMoveChar`. -/
def rightMoveChar (c : Chars) : Option Chars :=
  match c.2 with
  | [] => none
  | ch :: r => some (c.1 ++ [ch], r)

/-- `PadWSNL`, as the C does it (`PadWSNLC`): move the cursor to `(qx, qy)`,
padding the line with spaces, or the document with empty lines, as needed. -/
def padTo (c : Chars) (qx qy : Nat) : Chars :=
  let (L, _, _) := display c
  if qy ≤ L.length then
    let l := L.getD (qy - 1) []
    ofDisplay (L.set (qy - 1) (l ++ List.replicate (qx - 1 - l.length) sp)) qx qy
  else
    ofDisplay (L ++ List.replicate (qy - L.length - 1) [] ++ [List.replicate (qx - 1) sp]) qx qy

/-- `CursorUpChar_Doc4`: up one line, keeping the column. -/
def cursorUp (c : Chars) : Option Chars :=
  let (_, x, y) := display c
  if y ≤ 1 then none else some (padTo c x (y - 1))

/-- `CursorDownChar_Doc4`: down one line, keeping the column (past the end, the
document is padded with empty lines). -/
def cursorDown (c : Chars) : Option Chars :=
  let (_, x, y) := display c
  some (padTo c x (y + 1))

/-! ## The editor -/

structure Editor where
  doc      : Chars
  offsetX  : Nat := 0
  offsetY  : Nat := 0
  file     : String
  saved    : List Char      -- the content as last read or written
  message  : String := ""
  quitWarned : Bool := false

def Editor.content (e : Editor) : List Char := e.doc.1 ++ e.doc.2
def Editor.modified (e : Editor) : Bool := e.content != e.saved

/-- Apply an operation: on success, tidy (Doc3); on error, leave the document. -/
def Editor.apply (e : Editor) (op : Chars → Option Chars) : Editor :=
  match op e.doc with
  | some d => { e with doc := tidy e.doc.1.length d, message := "", quitWarned := false }
  | none => { e with message := "Cannot move there", quitWarned := false }

/-- The window policy (Doc9): keep each offset while the cursor stays in the
window; otherwise move just far enough to bring it back. -/
def Editor.scroll (e : Editor) (w h : Nat) : Editor :=
  let (_, x, y) := display e.doc
  let ox := if x ≤ e.offsetX then x - 1 else if x > e.offsetX + w then x - w else e.offsetX
  let oy := if y ≤ e.offsetY then y - 1 else if y > e.offsetY + h then y - h else e.offsetY
  { e with offsetX := ox, offsetY := oy }

/-- The window's lines (`winLinesOf`), padded to `h` rows, and the cursor's
position in the window, counted from 1. -/
def Editor.screen (e : Editor) (w h : Nat) : List String × Nat × Nat :=
  let (L, x, y) := display e.doc
  let rows := (List.range h).map fun i =>
    String.ofList (((L.getD (e.offsetY + i) []).drop e.offsetX).take w)
  (rows, x - e.offsetX, y - e.offsetY)

/-- The status line. -/
def Editor.status (e : Editor) : String :=
  let (_, x, y) := display e.doc
  let name := if e.modified then e.file ++ " [modified]" else e.file
  let msg := if e.message.isEmpty then "Ctrl-S save  Ctrl-Q quit" else e.message
  s!" zeditor  {name}  line {y}, col {x}  {msg}"

/-! ## Keys -/

inductive Key where
  | char (c : Char)
  | enter | tab | backspace | delete
  | left | right | up | down
  | save | quit
  | other

/-- What a key does to the editor. Saving and quitting are handled by the caller,
which owns the file system; here they only set messages. -/
def Editor.press (e : Editor) : Key → Editor
  | .char ch => e.apply (insertChar ch)
  | .enter => e.apply (insertChar nl)
  | .tab => e.apply insertTab
  | .backspace => e.apply leftDeleteChar
  | .delete => e.apply rightDeleteChar
  | .left => e.apply leftMoveChar
  | .right => e.apply rightMoveChar
  | .up => e.apply cursorUp
  | .down => e.apply cursorDown
  | .save | .quit | .other => e

/-- Open a document: the cursor at the top. -/
def Editor.open (file : String) (text : List Char) : Editor :=
  { doc := ([], text), file, saved := text }

end ZEditor.Impl
