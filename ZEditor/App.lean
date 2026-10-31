import ZEditor.Impl.Editor

/-!
# The terminal program, for either edition

    zeditor FILE                  edit FILE full-screen (the 1990 edition)
    zeditor2026 FILE              the same, the 2026 edition
    zeditor --keys SCRIPT FILE    run the keys in SCRIPT, print the screen

Keys: typing inserts, Enter, Tab, Backspace, Delete, the arrow keys,
Ctrl-Space sets the mark, Ctrl-C copies the marked text, Ctrl-X cuts it,
Ctrl-V pastes, Ctrl-S saves, Ctrl-Q quits. With unsaved changes, the 1990
edition saves and then quits (as the specification's Quit and the C do); the
2026 edition asks for Ctrl-Q to be pressed twice.

The shape follows Neilson's `main.c`: take over the terminal, load the file,
draw, then loop: read a key, apply the operation, redraw.
-/

namespace ZEditor.App

open ZEditor.Impl

/-! ## The terminal -/

/-- Run `stty` on the terminal (stdin inherited) and return its output. -/
def stty (args : Array String) : IO String := do
  let child ← IO.Process.spawn
    { cmd := "stty", args, stdin := .inherit, stdout := .piped, stderr := .null }
  let out ← child.stdout.readToEnd
  let _ ← child.wait
  return out.trimAscii.toString

/-- The terminal's size as (columns, rows). -/
def termSize : IO (Nat × Nat) := do
  match (← stty #["size"]).splitOn " " with
  | [r, c] => return (c.toNat?.getD 80, r.toNat?.getD 24)
  | _ => return (80, 24)

def esc (s : String) : String := "\x1b[" ++ s

/-- Read one key from the keyboard (raw mode). -/
def readKey (stdin : IO.FS.Stream) : IO Key := do
  let b ← stdin.read 1
  if b.isEmpty then return .quit
  match b[0]!.toNat with
  | 13 | 10 => return .enter
  | 127 | 8 => return .backspace
  | 9 => return .tab
  | 0 => return .setMark        -- Ctrl-Space
  | 3 => return .copy           -- Ctrl-C
  | 24 => return .cut           -- Ctrl-X
  | 22 => return .paste         -- Ctrl-V
  | 19 => return .save          -- Ctrl-S
  | 17 => return .quit          -- Ctrl-Q
  | 27 =>                       -- an escape sequence: arrows, Delete
    let s ← stdin.read 2
    match s.toList.map (·.toNat) with
    | [91, 65] => return .up
    | [91, 66] => return .down
    | [91, 67] => return .right
    | [91, 68] => return .left
    | [91, 51] => let _ ← stdin.read 1; return .delete   -- ESC [ 3 ~
    | _ => return .other
  | n => return if 32 ≤ n ∧ n < 127 then .char (Char.ofNat n) else .other

/-- Draw the window and the status line, and place the cursor. -/
def draw (e : Editor) (w h : Nat) : IO Unit := do
  let (rows, cx, cy) := e.screen w (h - 1)
  let stdout ← IO.getStdout
  let mut out := esc "?25l" ++ esc "H"
  for r in rows do
    out := out ++ r ++ esc "K" ++ "\r\n"
  out := out ++ esc "7m" ++ String.ofList (e.status.toList.take w) ++ esc "K" ++ esc "0m"
  out := out ++ esc s!"{cy};{cx}H" ++ esc "?25h"
  stdout.putStr out
  stdout.flush

/-- Write the document to its file. -/
def save (e : Editor) : IO Editor := do
  try
    IO.FS.writeFile e.file (String.ofList e.content)
    return { e with saved := e.content, changed := false, message := "Saved",
                    quitWarned := false }
  catch err =>
    return { e with message := s!"Cannot save: {err}" }

/-- Read a file; a file that does not exist is an empty new document. -/
def load (file : String) : IO (List Char × Bool) := do
  if ← System.FilePath.pathExists file then
    return ((← IO.FS.readFile file).toList.filter (· != '\r'), false)
  else
    return ([], true)

/-- Quit. Returns the editor and whether to stop.

1990 edition: as the specification's Quit and the C's `Quit_Quote`: if the
document has changed, save it, then quit; if saving fails, stay. Otherwise
report "Document not changed" and quit.

2026 edition: with unsaved changes, ask for Quit to be pressed again. -/
def quit (e : Editor) : IO (Editor × Bool) := do
  if e.edition.quitAsks then
    if e.modified && !e.quitWarned then
      return ({ e with message := "Unsaved changes: Ctrl-Q again to quit, Ctrl-S to save",
                       quitWarned := true }, false)
    else return (e, true)
  else
    if e.modified then
      let e' ← save e
      return (e', !e'.modified)
    else return ({ e with message := "Document not changed" }, true)

/-! ## The interactive editor -/

def interactive (edition : Edition) (file : String) : IO Unit := do
  let (text, isNew) ← load file
  let saved ← stty #["-g"]
  let _ ← stty #["raw", "-echo"]
  let stdout ← IO.getStdout
  stdout.putStr (esc "?1049h" ++ esc "2J")      -- the alternate screen
  try
    let stdin ← IO.getStdin
    let mut e := Editor.open edition file text
    e := { e with message := if isNew then "New file" else s!"Read {text.length} characters" }
    let mut running := true
    while running do
      let (w, h) ← termSize
      e := e.scroll w (h - 1)
      draw e w h
      match ← readKey stdin with
      | .save => e ← save e
      | .quit =>
        let (e', stop) ← quit e
        e := e'
        if stop then running := false
      | k => e := e.press k
  finally
    stdout.putStr (esc "?1049l")                 -- back to the normal screen
    stdout.flush
    let _ ← stty #[saved]

/-! ## The scripted mode -/

/-- A script has one key per line: `type TEXT`, or a key name
(`Enter`, `Tab`, `Backspace`, `Delete`, `Left`, `Right`, `Up`, `Down`, `Mark`,
`Copy`, `Cut`, `Paste`, `Save`, `Quit`). After a `Quit` that stops the editor,
the remaining keys are ignored. -/
def parseScript (s : String) : List Key :=
  (s.splitOn "\n").flatMap fun line =>
    if line.startsWith "type " then
      ((line.drop 5).toString.toList).map Key.char
    else match line.trimAscii.toString with
      | "Enter" => [.enter] | "Tab" => [.tab] | "Backspace" => [.backspace]
      | "Delete" => [.delete] | "Left" => [.left] | "Right" => [.right]
      | "Up" => [.up] | "Down" => [.down] | "Save" => [.save] | "Quit" => [.quit]
      | "Mark" => [.setMark] | "Copy" => [.copy] | "Cut" => [.cut] | "Paste" => [.paste]
      | _ => []

def scripted (edition : Edition) (scriptFile file : String) : IO Unit := do
  let (text, _) ← load file
  let keys := parseScript (← IO.FS.readFile scriptFile)
  let mut e := Editor.open edition file text
  let mut stopped := false
  for k in keys do
    if !stopped then
      match k with
      | .save => e ← save e
      | .quit =>
        let (e', stop) ← quit e
        e := e'
        stopped := stop
      | k => e := e.press k
  let (w, h) := (40, 8)
  e := e.scroll w h
  let (rows, cx, cy) := e.screen w h
  IO.println ("┌" ++ "".pushn '─' w ++ "┐")
  for i in [0:rows.length] do
    let r := rows.getD i ""
    let r := if i + 1 = cy then String.ofList (r.toList.take (cx - 1)) ++ "|" ++
                String.ofList (r.toList.drop (cx - 1)) else r
    IO.println ("│" ++ r ++ "".pushn ' ' (w - r.length) ++ "│")
  IO.println ("└" ++ "".pushn '─' w ++ "┘")
  IO.println e.status
  if stopped then IO.println " (quit)"

def run (edition : Edition) (cmd : String) (args : List String) : IO UInt32 := do
  match args with
  | [file] => interactive edition file; return 0
  | ["--keys", script, file] => scripted edition script file; return 0
  | _ =>
    IO.eprintln s!"usage: {cmd} FILE\n       {cmd} --keys SCRIPT FILE"
    return 1

end ZEditor.App
