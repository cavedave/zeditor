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

/-- Remove empty lines at the end of `B`, but keep one if there was any: the
document keeps its final newline (decision D4). -/
def keepFinalNewline (B : List (List Char)) : List (List Char) :=
  let s := stripNull B
  if s.length < B.length then s ++ [[]] else s

/-- `RemTrailNL`: remove empty lines at the end of the document, below the
cursor, keeping at most one, so that a final newline survives (decision D4). The
printed specification allows one to remain only when every line below the cursor
is empty; the C removes them all. -/
def remTrailNL (c : Chars) : Chars :=
  let (L, x, y) := display c
  ofDisplay (L.take y ++ keepFinalNewline (L.drop y)) x y

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
  /-- The mark, as a position in the text (decision D5, as in the C, where
  `MP = −1` means no mark). -/
  mark     : Option Nat := none
  /-- The paste buffer (`PBuff`). -/
  pBuff    : List Char := []
  /-- Whether the document has been edited since it was last read or saved
  (decision D6, as the C's `DocChanged`; the specification keeps no such
  record, finding 7f). -/
  changed  : Bool := false

def Editor.content (e : Editor) : List Char := e.doc.1 ++ e.doc.2
/-- Unsaved changes: any edit since the last read or save, as the C's
`DocChanged`. Typing a character and deleting it again still counts. -/
def Editor.modified (e : Editor) : Bool := e.changed

/-! ## The mark

The mark is a position in the text, or none (decision D5). The specification
records it instead as two pieces of text (`MarkSeq`, `MarkedSeq`), which causes
findings 6a to 6e; the C keeps a position `MP`, and so do we. -/

/-- The length of the longest common prefix of two lists. -/
def commonPrefix : List Char → List Char → Nat
  | a :: as, b :: bs => if a = b then commonPrefix as bs + 1 else 0
  | _, _ => 0

/-- Where a position in `old` ends up in `new`, when `new` differs from `old` in
one stretch (as each tidying step and each padding step does): positions before
the change stay, positions after it shift, positions inside it move to its start. -/
def adjustPos (old new : List Char) (m : Nat) : Nat :=
  let p := commonPrefix old new
  let s := commonPrefix (old.drop p).reverse (new.drop p).reverse
  if m ≤ p then m
  else if m + s ≥ old.length then m + new.length - old.length
  else p

/-- Apply an operation: on success, tidy (Doc3); on error, leave the document.
`edit` says whether the operation changes the text (insert, delete) or is a
cursor move. -/
def Editor.applyKind (e : Editor) (op : Chars → Option Chars) (edit : Bool) : Editor :=
  match op e.doc with
  | some d₁ =>
    let d₂ := remTrailWS e.doc.1.length d₁
    let d₃ := remTrailNL d₂
    let content (c : Chars) := c.1 ++ c.2
    -- An edit clears the mark, as the specification (`ResetMark`, §5.1.1) and the C
    -- (`Update_Doc6`, which sets `MP = −1`) both do. Emacs instead keeps the mark
    -- and shifts it as text is inserted or deleted before it; that would be a later
    -- change (decision D5).
    -- A cursor move keeps the mark on the same text, adjusted for any spaces or
    -- newlines the move pads in or the tidying removes, as the C does
    -- (`Update_Doc6`: `MP = MP − WSRem + WSIns`).
    let mark :=
      if edit then none
      else e.mark.map fun m =>
        adjustPos (content d₂) (content d₃)
          (adjustPos (content d₁) (content d₂) (adjustPos (content e.doc) (content d₁) m))
    -- An edit sets the changed flag, as the C's `Update_Doc8` sets `DocChanged`
    -- for every operation that is not a move. Moves do not set it, even when
    -- the tidying removes spaces (as in the C).
    { e with doc := d₃, mark, changed := e.changed || edit, message := "", quitWarned := false }
  | none => { e with message := "Cannot move there", quitWarned := false }

def Editor.apply (e : Editor) (op : Chars → Option Chars) : Editor := e.applyKind op true
def Editor.move (e : Editor) (op : Chars → Option Chars) : Editor := e.applyKind op false

/-- The cursor as a position in the text. -/
def Editor.cursor (e : Editor) : Nat := e.doc.1.length

/-- The marked text: from the mark to the cursor, whichever comes first. `none`
when there is no mark or nothing is marked (`ErrorNoTextMarked`). -/
def Editor.marked (e : Editor) : Option (Nat × Nat) :=
  match e.mark with
  | some m => if m = e.cursor then none else some (min m e.cursor, max m e.cursor)
  | none => none

/-- `SetMark_Doc5`: the mark at the cursor. -/
def Editor.setMark (e : Editor) : Editor :=
  { e with mark := some e.cursor, message := "Mark set", quitWarned := false }

/-- `Lift_Doc6`: copy the marked text to the paste buffer; nothing else changes. -/
def Editor.lift (e : Editor) : Editor :=
  match e.marked with
  | some (lo, hi) =>
    { e with pBuff := ((e.doc.1 ++ e.doc.2).drop lo).take (hi - lo),
             message := s!"Copied {hi - lo} characters", quitWarned := false }
  | none => { e with message := "No text marked", quitWarned := false }

/-- `Cut_Doc6`: copy the marked text to the paste buffer and remove it, on
whichever side of the cursor the mark is; the mark is cleared; then tidy. -/
def Editor.cut (e : Editor) : Editor :=
  match e.marked with
  | some (lo, hi) =>
    let t := e.doc.1 ++ e.doc.2
    let e' := { e with pBuff := (t.drop lo).take (hi - lo), mark := none }
    { (e'.apply (fun _ => some (t.take lo, t.drop hi))) with
        message := s!"Cut {hi - lo} characters", pBuff := (t.drop lo).take (hi - lo) }
  | none => { e with message := "No text marked", quitWarned := false }

/-- `Paste_Doc6`: insert the paste buffer at the cursor and mark the pasted text
(the mark at the old cursor, as the C's `MP=CP` before inserting; the printed
`Pst` gets this wrong, finding 6a); then tidy. -/
def Editor.paste (e : Editor) : Editor :=
  if e.pBuff.isEmpty then { e with message := "Paste buffer empty", quitWarned := false }
  else
    let oldCursor := e.cursor
    let e' := e.apply (fun c => some (c.1 ++ e.pBuff, c.2))
    { e' with mark := some oldCursor, message := s!"Pasted {e.pBuff.length} characters" }

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
  let markInfo := match e.marked with
    | some (lo, hi) => s!"  [{hi - lo} marked]"
    | none => if e.mark.isSome then "  [mark set]" else ""
  let msg := if e.message.isEmpty then "Ctrl-S save  Ctrl-Q quit" else e.message
  let msg := markInfo ++ "  " ++ msg
  s!" zeditor  {name}  line {y}, col {x}  {msg}"

/-! ## Keys -/

inductive Key where
  | char (c : Char)
  | enter | tab | backspace | delete
  | left | right | up | down
  | setMark | copy | cut | paste
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
  | .left => e.move leftMoveChar
  | .right => e.move rightMoveChar
  | .up => e.move cursorUp
  | .down => e.move cursorDown
  | .setMark => e.setMark
  | .copy => e.lift
  | .cut => e.cut
  | .paste => e.paste
  | .save | .quit | .other => e

/-- Open a document: the cursor at the top. -/
def Editor.open (file : String) (text : List Char) : Editor :=
  { doc := ([], text), file, saved := text }

end ZEditor.Impl
