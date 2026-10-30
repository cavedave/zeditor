# zeditor: a Lean 4 formalisation of a Z-specified text editor

This project translates a published Z specification of a full-screen text editor into Lean 4 and checks it. It records the problems the formalisation found and the decisions made about them. The aim is a runnable editor written in Lean and proved to meet the corrected specification.

## The source

D. S. Neilson, *From Z to C: Illustration of a Rigorous Development Method*, Technical Monograph PRG-101, Oxford University Computing Laboratory, Programming Research Group, Hilary 1990. ISBN 0-902928-78-3.

The scanned monograph is included as `source/Zeditor.pdf` (278 pages, SHA-256 `5c00b1450a147cddf8248f11cb5d12de1f68fc40ff3fcfee46ffbc48499608e3`). It and the transcriptions of its Z specification and C code in `docs/` are included with permission. **D. S. Neilson retains the copyright** in the monograph, its Z specification and its C code (© 1990 D. S. Neilson). They are not covered by this repository's MIT licence.

## Licence

Our own work (the Lean code, `README.md`, `FINDINGS.md` and `docs/corrections.csv`) is released under the MIT License. The original monograph and its transcriptions remain © 1990 D. S. Neilson. See [`LICENSE`](LICENSE) for exactly which files fall under which terms.

The monograph specifies an editor in Z (Part Three), refines the specification step by step towards code using a refinement calculus (Parts Two and Four), and prints the resulting C program (Appendix C). The specification is built as a hierarchy of nine levels, each adding one concern:

| Level | Adds |
|---|---|
| Doc1 | the document as text left and right of the cursor; move, delete, insert by character, word and line |
| Doc2 | the document as display lines with a cursor position |
| Doc3 | display invariants (no trailing whitespace or empty lines) |
| QP, Doc4 | free cursor movement |
| Doc5, Doc6 | marked text; lift, cut and paste |
| Doc7 | the quote buffer and commands: save, write, append, quit, input, move-to-line, escape |
| Doc8 | search and replace with regular expressions |
| Doc9 | a window onto the display: scroll, pan, centre |

The scanned PDF's text layer is unusable, so the relevant parts were transcribed from the page images. The transcriptions are in `docs/`:

| File | Contents |
|---|---|
| `zeditor-p001-020.md` | Parts One and Two (start): overview and refinement calculus, PDF pp.1–20 |
| `zeditor-part3-zspec.md` | Part Three in full: the Z specification with prose, examples, lemmas and proofs |
| `zeditor-spec-core.md` | Part Three reduced to its definitions only, with a level-by-level map to the C code |
| `zeditor-appendixC-code.md` | Appendix C: the C implementation |
| `corrections.csv` | every doubtful reading in the transcriptions, by ID (`[?N]` in the text) |
| `eyecheck/` | the scan pages behind the findings that rest on a single symbol, at native resolution |

## This project

```
zeditor/
  README.md  FINDINGS.md   -- this file; the findings and the decisions about them
  source/Zeditor.pdf    -- the original monograph
  docs/                 -- transcriptions (above)
  ZEditor.lean          -- root module
  ZEditor/Spec/Doc1.lean   -- §1: the Doc1 document model, translated from the Z
  ZEditor/Spec/Unique.lean -- word and line views are unique (Corollaries 3:1.2a, 3:1.2c)
  ZEditor/Spec/Total.lean  -- every document has word and line views; the operations are total
  ZEditor/Spec/Doc2.lean   -- §2: the unbounded display (lines and screen cursor)
  ZEditor/Spec/Doc3.lean   -- §3: no trailing spaces or empty lines; RemTrailWS, RemTrailNL
  ZEditor/Spec/Doc4.lean   -- §4: the quarter-plane cursor (QP), Doc4, PadWSNL
  ZEditor/Spec/Doc5.lean   -- §5.1: marked text
  ZEditor/Spec/Doc6.lean   -- §5.2: the paste buffer; lift, cut and paste
  ZEditor/Spec/Doc7.lean   -- §6: the quote buffer, operating-system I/O, quoted commands
  ZEditor/Spec/Doc8.lean   -- §7: search and replace
  ZEditor/Spec/Doc9.lean   -- §8: the window onto the display (the complete editor)
  ZEditor/Check.lean    -- exhaustive computational checks of the Doc3 and Doc4 proof obligations
  ZEditor/Demo.lean     -- a scripted demonstration
  ZEditor/Impl/Editor.lean -- the runnable editor's core
  Main.lean             -- the terminal program
```

Plain Lean 4 (toolchain in `lean-toolchain`), no Mathlib. Build with `lake build`. `Check.lean` is not part of the build; run it with `lake env lean ZEditor/Check.lean`.

### How the Z is translated

- A state schema becomes a `structure`; its predicate becomes proof fields, so every value of the type satisfies the invariant.
- An operation schema on `ΔState` becomes a relation `State → State → Prop` between before- and after-state. Inputs (`x?`) and outputs (`rep!`) become extra arguments. This keeps the specification's non-determinism: for example, a tab may insert any positive number of spaces, and an insert may always answer "Editor full".
- Schema composition `S ; T` becomes relational composition `⨾`; disjunction and conjunction of schemas become `∨` and `∧`.
- Z sequences are `List`; `front` is `dropLast`, `⁀/` is `flatten`, `rev` is `reverse`.
- Each Lean definition's doc comment quotes the Z it comes from. Where the printed Z cannot be taken literally, the comment says so and states the reading used.

## What the formalisation found

All findings are tracked in [`FINDINGS.md`](FINDINGS.md), one row each, with severity, evidence, what the C does, and a Decision column. Decisions on what to do about them are deliberately left until the whole specification has been worked through.

Writing the specification in Lean, where every definition must type-check and every claim must be proved, exposed problems in the printed Z that the book's own semi-formal proofs did not catch. Each one is backed by a theorem in `ZEditor/Doc1.lean`.

### 1. The definition of a line is contradictory

The book defines `Line ≙ seq (Char − {nl})`, a possibly empty sequence of non-newline characters. But its own examples split a document into lines that include newline lines, e.g. "the⏎canary" becomes `⟨⟨t,h,e⟩, ⟨nl⟩, ⟨c,a,n,a,r,y⟩⟩`, and `DocLineSeq` tests `l1 ≠ ⟨nl⟩`. Taken literally, the printed definition means:

- no document containing a newline has a line view at all (`printed_lines_have_no_nl`);
- the empty document has two different line views, `⟨⟩` and `⟨⟨⟩⟩`, so the "one-to-one" function `FL` is not one-to-one and Corollary 3:1.2c is false (`printed_lines_not_unique`).

We use the reading the examples need: a line is a non-empty run of non-newline characters, or the newline on its own. This is decision [D1](FINDINGS.md#d1-what-a-line-is), which shows the relevant parts of the scan.

### 2. The word rule uses `=` where `⊆` is meant

`DocWordSeq` forbids adjacent words with `rng(w1) = WhiteSpace ⇒ rng(w2) ≠ WhiteSpace`, and the same for `NonWhiteSpace`. With `=`, the `NonWhiteSpace` clause never applies, since no finite word contains every non-space character. Then `⟨⟨c,a⟩,⟨t⟩⟩` is a valid word view of "cat", and word views are not unique. We read it as "the word is drawn from" (`⊆`), which is what the prose says.

### 3. Moving by a word or a line is not a total operation

This is the most significant finding. Section 1.6 defines "the total operations on the Doc1 state", e.g.

    LeftMoveWord_Doc1 ≙ (LeftMvWord ∧ Success) ∨ ErrorTopOfDoc

`LeftMvWord` is the generic move `Mv` applied to the word view. `Mv` keeps the content unchanged *as a sequence of words*: `Left ⁀ Right = Left′ ⁀ Right′`. When the cursor is inside a word, as in "ca|t", the left side is the word `⟨c,a⟩` and the right side the word `⟨t⟩`. Moving left one word would leave the word sequence `⟨⟨c,a⟩, ⟨t⟩⟩` on the right, which is not a valid word view. So no after-state exists. The error case does not apply either, because the cursor is not at the top. The "total" operation therefore has no outcome at all (`leftMoveWord_Doc1_stuck`). The same holds for moving by a line when the cursor is inside a line.

The C code shows what was intended. `LeftMoveWord_Doc1` (Appendix C, p.ii) always succeeds when the cursor is not at the top, moving "ca|t" to "|cat". That is the same move with the content kept unchanged *as a sequence of characters*, using `Ξ_Cont Doc1`, which the book defines in §1.3 but does not use here. Lean checks that this reading produces exactly the C's result (`leftMvWordC_caT`).

With that correction, every one of the fifteen operations of §1.6 is proved total (`Total.lean`: `LeftMoveWordC_Doc1_total`, `RightDeleteLine_Doc1_total`, `MoveToTop_Doc1_total`, …). So the four word and line moves are exactly where the book's claim fails; the character moves, all six deletes, move-to-top/bottom and insert are total as printed.

This matters because the whole method rests on these operations: every higher level promotes them, and Part Four refines them into the C. The book discharges proof obligations informally ("the result follows from the definition of DocWordSeq"), and the problem slipped through. It is exactly the kind of error a machine-checked formalisation is for.

### 4. Doc2 and Doc3: smaller problems

- **`RemTrailWS` uses variables it does not declare.** It is declared on `ΔUD` (the display only), but its `where` clause computes the previous cursor line from `Left_Char` and `Right_Char`, which belong to Doc1. It only makes sense on `ΔDoc2`, which is how it is used and how we define it.
- **`visibleseq` is undefined where it is used.** It is defined with `last L`, and Doc3 applies it to the lines below the cursor, which are often none at all, where `last` is undefined. The book's prose says the empty sequence counts as a visibleseq, and we read it that way.
- **The empty-line invariant is weaker than its stated reason.** `visibleseq` exempts `⟨⟨⟩⟩` so that the empty document is allowed. Doc3 applies it to the lines *below the cursor*, where the same exemption lets one invisible empty line survive at the end of the document. The book's reason for the invariant is that such lines cannot be seen. The C (`RemTrailNL`) removes it, which is a legitimate refinement of the weaker Z.
- **The consistency proof for Doc2** (printed p.73) concludes `Uₙ = ⟨l, r⟩`, a two-element sequence, where it means the single line `l ⁀ r`. The formal version is `FDLinv_append`.
- **Lemma 3:2.2d** is justified by "Lemmas 3:1.3a and 3:2.1b", which do not exist.

What holds up: the book asserts without proof that `RemTrailWS` and `RemTrailNL` are total, and both are now proved (`RemTrailWS_total`, `RemTrailNL_total`). The main Doc3 obligation, that every edit followed by the two tidying operations restores the invariant, is argued informally in the book. It is not yet proved in Lean, but an exhaustive check (`Check.lean`) finds no counterexample in all 21,014 Doc3 states from documents of up to 8 characters over `a`, space and newline, for all 15 operations. The same check with `RemTrailWS` removed finds 1,310 failures, so it does detect violations.

An observation about the C: bug #605 (`if (OPType=LeftMove || …`) assigns rather than compares. `LeftMove` is 5, so the test is always true and `OPType` is overwritten. The effect is that the C runs both tidying routines after *every* operation, which is exactly what the Z specifies (`OP_Doc3 ≙ … ; RemTrailWS ; RemTrailNL` for every operation). Code after it that reads `OPType` sees the wrong value.

### 5. Moving right after typing a space reports "Editor full"

§4 lets the cursor move beyond the text, into the "quarter plane" to the right of and below it. When it does, `PadWSNL` pads the document with spaces and empty lines to reach the cursor. For a move within the existing lines it requires

    UDLines QPCurY visible_prefix UDCurLine′

meaning the old line must be a `visible_prefix` of the padded line. But `visible_prefix` demands that its first argument be *visible*, with no trailing space. Under the Doc3 invariant the cursor line is the one line allowed to end in spaces, and only when the cursor is at its end. That is exactly the position after typing a space at the end of a line.

From there, pressing → (`CursorRightChar`) targets the same line. The first case of `PadWSNL` is impossible, the second (below the text) does not apply, and the operation's only remaining outcome is its `ErrorFull` disjunct. The editor would answer **"Editor full"**. Lean proves this for the document "a␣|" (`cursorRight_after_space`). The book states, "The operation is total", which is false.

The exhaustive check (`Check.lean`) shows this is the *only* way the QP moves get stuck. Up to 8 characters there are 3,581 stuck (state, operation) cases, and every one is → with the cursor at the end of a line ending in a space. The C (`CursorRightChar_Doc4`) inserts a space and moves on. With that reading of the padding (`PadWSNLC`: the old line is a prefix of the new one and only spaces are added), the check finds no failures of the Doc4 invariant or the cursor position for any of the five moves from any of the 21,014 states.

A smaller point: the book says the tidying operations "ensure that the Doc3 invariant is maintained". In fact `PadWSNL` may add more spaces than needed, which leaves trailing spaces right of the cursor that `RemTrailWS` does not remove (it only cleans the *previous* cursor line). Those outcomes are excluded only because `ΔDoc4` requires the after-state to satisfy the invariant.

### 6. Cut, paste and the mark

§5 adds a mark and a paste buffer. All three of its new operations are wrong as printed. In each case the scan was re-checked, and the C does what the prose describes.

**Paste can only report "Editor full".** The prose says the pasted text becomes marked text, with the mark at the old cursor position. `Pst` sets `Left_Char′ = Left_Char ⁀ PBuff` and `MarkSeq′ = Left_Char`, but `MarkedSeq′ = ⟨⟩` where it should be `PBuff`. The after-state then breaks the `MarkedText` invariant, because `MarkSeq′ ⁀ MarkedSeq′` is the old `Left_Char`, not the new one. So `Pst` has no outcome unless the cursor is at the top of the document. Paste's only remaining answer is its `ErrorFull` disjunct (`pst_impossible`, `paste_only_full`). The C sets the mark at the old cursor and then inserts, which is the intended `MarkedSeq′ = PBuff` (`PstC`).

**Cut either does anything or nothing.** The book calls `RemMText` "a total operation which removes marked text". Its second rule, for a mark below the cursor, has the premise `MarkedSeq ⁀ MarkSeq = Left_Char` where `Right_Char` is meant (#313). Two consequences:
- With the mark below the cursor, neither premise normally holds, so the document after a Cut is completely unconstrained. Cut may replace the whole document with anything (`remMText_mark_below_unconstrained`).
- When `MarkSeq` and `MarkedSeq` commute, both premises hold and they contradict each other. For example, in "aa|" with the mark between the a's, Cut has no outcome at all, not even an error (`remMText_both_premises`, `cut_no_outcome`). This happens whenever the marked text and the text before the mark repeat, for example inside a run of spaces.

The C removes the text on whichever side the mark is (`RemMTextC`).

**A mark at the top of the document is no mark.** "Mark set" is represented as `MarkSeq ⁀ MarkedSeq ≠ ⟨⟩`. Setting the mark with the cursor at the top gives `MarkSeq′ = MarkedSeq′ = ⟨⟩`, which is the representation of "no mark" (`setMark_at_top`). The promotion rules then go wrong one way or the other:
- As printed, the rules split cursor operations by the *after*-state (`MarkSeq′ ⁀ MarkedSeq′ ≠ ⟨⟩`). Then any cursor move may produce any mark, even when none was set (`cursorOp_mark_unconstrained`).
- Read as conditions on the before-state, a mark set at the top is simply lost, and text cannot be marked starting from the top of the document.

The C keeps the mark as a position `MP`, with `MP = −1` for "no mark", so it has no such ambiguity.

### 7. The quoted commands

§6 adds commands typed into a quote buffer: save, write, append, quit, input, move to line and escape. It also adds an abstract model of the operating system's file store. The suspect lines were all re-checked against the scan.

**Three commands can never complete normally.** In each case pressing the quote key has no outcome at all. The command text is valid, so the "Quote error" case doesn't apply either.
- **Quit** (`quit_stuck`): `RequestQuit` contains both `WriteSeq! = MarkedSeq` and `WriteSeq! = Left_Char ⁀ Right_Char`. These agree only when the whole document is marked.
- **Move to line** (`moveToLine_stuck`): `MoveLineNumber_Quote` is defined but left out of `Quote_StateQuote`. The same gap makes the empty command, pressing the quote key twice, stuck (`emptyQuote_stuck`).
- **Input while text is marked** (`input_marked_stuck`): `QuoteRequestContentChange` requires `MarkedSeq = ⟨⟩` on the *before*-state (the prime is missing).

**Reading a file returns anything.** `SysRead` says `¬ NoReadError! ⇒ ReadSeq! = storedseq(…)`, which is the wrong way round. A successful read is unconstrained (`sysRead_success_any`).

**Error cases may change what they should not touch.** In Z, a disjunction of schemas has the combined signature of its parts. Any variable a part does not mention is unconstrained in that part. Several error branches therefore allow arbitrary changes:
- "Cannot open file" may change any file in the store (`writeToStore_cannot_open_any`).
- A failed Input may replace the whole document with anything (`input_error_any_document`).
- Save's "Document not changed" may change any file (`save_any_store`).
- Typing into the quote buffer may rename the document, so a later Save writes to an arbitrary file (`quoteEdit_any_name`).

**Save and Quit cannot tell whether the document changed.** The state has no record of changes, so "Document not changed" is always a permitted answer. Quit may exit without saving the user's edits. The C has a `DocChanged` flag.

Smaller problems:
- **Undefined names:** `DocCurX′`, `ExchMTextPBuff`, `CursorLeftChar_Quote`, and others.
- **Files have no identity:** `SysGetPtr` does not relate the pointer to the file name, so saving and then reading the same file need not give the text back.
- **Move to line:** if it were reachable, it would leave the document content unconstrained, and line 0 would have no outcome.

### 8. Search and replace

§7 adds a search buffer, a replace buffer, and searches up and down with a loosely specified form of regular expression. Each finding was re-checked against the scan.

- **Replace cannot replace** (`replace_ok_unchanged`). `PromoteReplace` was evidently copied from `PromoteSearch` and still contains `Ξ_Cont Doc1`, "the content does not change". The prose says the opposite. A successful Replace therefore leaves the document as it was, and at a match the only general answer is "Editor full".
- **Searching while a mark is set fails when the text is there** (`downSearch_marked_stuck`, and the same for Replace in `replace_marked_full`). `PromoteSearchUnMark` says `MarkSeq = MarkedSeq′ = ⟨⟩`: the first has no prime, so the mark must be absent *before* the search.
- **Searching away from a line ending in a space fails.** `PromoteSearch` also contains `Ξ_Cont Doc1`, but leaving a line that ends in a space requires the tidying operations to remove the space, which changes the content. Lean proves the key step: in Doc3, a content-preserving move to another line requires the old line to be visible (`xiCont_other_line_visible`). The book's own prose says a search "may necessitate the removal of whitespace".
- **A down search may move up** (`downSearch_may_go_up`). "The first match after the cursor" is written as "no match in positions `#Left + 2 .. #Left′ + matchedlength − 1`". For a match *behind* the cursor this range is empty, so the condition holds trivially. Nothing says the cursor moves forward. In "a|xa", a down search for "a" may jump back to the start. Up searches may move down in the same way.
- **Smaller problems.** The constraint on `regexpmatches` (`# e ≥ s`) does not type-check, and `matches` refers to an undefined `s`. Only the domain of `matchedlength` is specified, so the number of characters a Replace removes is unconstrained. The disjuncts of the search and replace operations are grouped by layout, contrary to Z's precedence rules, which would give a meaningless reading.

### 9. The window

§8, the window onto the display, is the cleanest section. The window policy (keep the window if the cursor is still in it, otherwise scroll, pan, or both) is proved total, as the book claims (`WindowPolicy_total`). The window and the display cursor agree, which is the content of Lemma 3:8.2a. Only edge cases are wrong:

- **Lemma 3:8.2a is undefined at the end of a line.** It equates the characters under the two cursors. When the cursor is after the last character of its line, which is always so in the empty document, there is no character. Stated with partial indexing it holds everywhere (`Doc9.char_at_cursor`).
- **Centring a one-line window has no outcome.** `HalfWinHeight = WinHeight/2` is claimed to be at least 1 but is 0 when `WinHeight = 1` (`centreWindow_height_one`). For any taller window, centring is total (`CentreWindow_Doc9_total`).
- **"We thus discharge PO 1 for each Doc8 operation"** is true only relative to Doc8. The window policy carries totality up (`promote9_total`), but it cannot repair the Doc8 operations shown above to have no outcome.

### Other errors in the original, noticed during transcription

These are recorded in `docs/corrections.csv`:

- The general `Rel` schema is defined with predicate `invrel` (printed p.13) but restated with `absinv` (p.17).
- The proof of Lemma 3:1.2.2b (lines) repeats the steps of Lemma 3:1.2.2a (words): `FW`, `tail`, `postfix` instead of `FL`, `front`, `prefix`.
- `RemMText` has `MarkedSeq ⁀ MarkSeq = Left_Char` where `Right_Char` is expected (#313).
- The `Window` schema uses `# WinLines` where `WindowLines` is meant; Lemmas 8.2a and 8.2c mix up `WinWidth` and `WinHeight`.
- `ErrorReplaceFull_Doc` uses `rep!` without declaring it.
- Several names differ between definition and use (`ErrorQPAtTop`/`ErrorQPTop`, `QPCurUp`/`QPCursorUp`, `McBottom`/`MvBottom`).
- In the C: `RemTrailWS` tests `if (OPType=LeftMove || …` with assignment `=` rather than `==` (#605); `PanicWriteToStore` declares `SysFtr` but uses `SysPtr` (#802).

## The C code as a guide

The C program is not the specification, but it is useful in two ways:

1. **It shows intent where the Z is wrong or ambiguous**, as with word movement above.
2. **It is a refinement to verify.** The C stores the document in a gap buffer (`Arr`, with indices `LP`, `RP`, `CP`), and Part Four gives the relation between that representation and the Z state. Writing the gap buffer in Lean and proving each C function satisfies its Z operation would make the book's method fully formal.

## Running the editor

A first prototype runs as a full-screen terminal editor:

    lake build
    .lake/build/bin/zeditor notes.txt

Typing inserts text; Enter, Tab, Backspace, Delete and the arrow keys work; **Ctrl-S** saves and **Ctrl-Q** quits (press it twice if there are unsaved changes). The status line at the bottom shows the file, whether it has unsaved changes, and the cursor position.

It can also run a script of keys and print the resulting screen, which is how it is tested:

    .lake/build/bin/zeditor --keys script.txt notes.txt

where `script.txt` has one key per line: `type some text`, or a key name (`Enter`, `Tab`, `Backspace`, `Delete`, `Left`, `Right`, `Up`, `Down`, `Save`).

Tests: `sh tests/save.sh` checks that saving writes exactly the document's text and nothing else.

Note for macOS Terminal: save with **Ctrl-S**, not **⌘S**. Terminal catches ⌘S itself and saves its whole window (as "Terminal Saved Output.txt"), before the editor sees the key.

**A lesson from first use.** The first time the editor was tried, ⌘S was pressed to save, out of habit from every other Mac application. Terminal saved its own window instead, including the earlier shell history, and it looked as though the editor had saved far more than the document. A terminal program can never receive ⌘ keys: Terminal keeps them for itself. Ctrl-S was the convention of 1990 terminals (and of Neilson's era); ⌘S is the convention users now expect. The status line names Ctrl-S for this reason, but the mismatch remains a real usability hazard for any terminal editor on a Mac.

The prototype is `Main.lean` (the terminal) and `ZEditor/Impl/Editor.lean` (the editor itself, with no input or output). Every key is followed by the specification's tidying operations, so trailing spaces vanish when you leave a line, and moving the cursor past the end of the text pads the document as Doc4 specifies. The operations are not yet proved to meet the specification; that comes next. `ZEditor/Demo.lean` is a scripted demonstration run inside Lean (`lake env lean ZEditor/Demo.lean`).

## From the C to a Lean editor

The runnable Lean editor has the same design as Neilson's C: a full-screen terminal editor, like `vi` or `nano`. The C's `main.c` is:

```c
GetTermCapAndSetWin(); SetTerminal();      /* take over the terminal */
StartEditFile(FName, ...);                 /* read the file */
DisplayTheWindow();                        /* draw the first screen */
while (TRUE) {
    ExecuteCommand();                      /* = OP_Doc9(KbdRead()) */
    if (Not(CharAvailable())) DisplayTheWindow();
    SetDocCursor();
}
```

and the Lean editor follows the same four steps:

| Step | Neilson's C | Lean |
|---|---|---|
| Take over the terminal | `GetTermCapAndSetWin`, `SetTerminal` (termcap; vt220 and Sun keyboards) | `stty raw -echo` and the terminal's alternate screen (standard ANSI codes) |
| Load the file | `StartEditFile` | read the file into the document state |
| Each key | `OP_Doc9(KbdRead())` | key ↦ operation, then the Doc9 operation |
| Draw | `DisplayTheWindow`, `SetDocCursor` | draw the window, place the cursor |

The specification fits a terminal unusually well: the Doc9 *window* (`WinWidth` × `WinHeight` with two offsets) is the terminal screen, and the window policy proved total in `Doc9.lean` is what decides when the screen scrolls.

Three things make the Lean editor simpler to follow than the C:

1. **No incremental redrawing.** On a 1990 terminal at 9600 baud, redrawing a screen was slow. So the C redraws only when no key is waiting (`CharAvailable`) and keeps careful account of what changed: `WSRem`, `NLRem`, `WSIns`, `Update_Doc3`, `Update_Doc4` and so on. That bookkeeping is a large part of the C. A modern terminal redraws a whole screen in a few milliseconds, so the Lean editor redraws the window after every key.
2. **One state value instead of global variables.** The C keeps its state in global variables (`LP`, `RP`, `CP`, `CurX`, `CurY`, `MP`, `EState`, …) that every function reads and writes. The Lean editor passes a single document value through its loop: a key and a document go in, a new document comes out. Each step can be read, tested and proved on its own.
3. **The operations are the specification's operations.** In the C, the link between, say, `LeftMoveWord_Doc1` and its Z schema is the informal argument of Part Four. In Lean, the operation the loop calls is the one the specification describes, and the aim is to prove each one meets it.

So the design is Neilson's, without the parts that existed only because 1990 terminals were slow.

## Status and plan

- [x] Doc1 translated (`ZEditor/Spec/Doc1.lean`): states, all operations, error cases, the total operations
- [x] Problems 1–3 above proved
- [x] Word and line views are unique (Corollaries 3:1.2a and 3:1.2c, which the book states without proof): `DocWordSeq.unique`, `DocLineSeq.unique`. Proved once for a general "cut into blocks of one class" shape (`Blocks.unique`) and applied to both.
- [x] Every character sequence has a word and a line view (`words`, `lines`, i.e. `FW⁻¹` and `FL⁻¹`), so `FW` and `FL` really are bijections, and a `Doc1` state is determined by its characters (`Doc1.ext_chars`)
- [x] `Mirror ; Mirror ≙ ΞDoc1` in full (`mirror_mirror_iff`)
- [x] All fifteen §1.6 operations total, with the corrected word and line moves
- [x] Doc2 (`Doc2.lean`): `FDL`/`FDL⁻¹` with the book's defining equations proved; Lemmas 3:2.1a, 3:2.2a–d; every Doc1 state has exactly one display (`Doc2.ofDoc1`, `Doc2.ext`), which is the book's consistency argument; the fifteen operations promoted and total
- [x] Doc3 (`Doc3.lean`): the invariant, `visible_prefix`, `visibleseq_prefix` (Lemmas 3:3.2a, 3:3.2c), PO 0 (`Initialize_Doc3_exists`), `RemTrailWS` and `RemTrailNL` total, promotion `OP_Doc3`
- [ ] Doc3 PO 1 (edits followed by the tidying operations restore the invariant): checked exhaustively up to 8 characters; proof to do
- [x] QP and Doc4 (`Doc4.lean`): the QP moves and their errors, all four total; Doc4 with Lemma 3:4.2a and PO 0; promotion of the Doc3 operations and of the QP moves with `PadWSNL`; problem 5 proved, and the C's padding (`PadWSNLC`) checked exhaustively up to 8 characters
- [x] Doc5 and Doc6 (`Doc5.lean`, `Doc6.lean`): marked text, set mark, the promotion rules, the paste buffer, Lift (total), Cut, Paste, PO 0 for both; problem 6 proved, with the C's readings of `RemMText` and `Pst` given
- [x] Doc7 (`Doc7.lean`): the quote buffer and its edit operations (PO 2: all total); the operating-system layer (`SysWrite`, `SysRead`, `WriteToStore`, `ReadFromStore`) over an abstract store; the Doc7 state; every quoted command; `Quote_Doc7`; promotion of the edit operations; problem 7 proved
- [x] Doc8 (`Doc8.lean`): search and replace buffers, regular expressions as parameters, up and down search, Replace, promotion; problem 8 proved
- [x] Doc9 (`Doc9.lean`): the window, offsets and window cursor; Lemmas 3:8.2a (corrected), 8.2b, 8.2c; Centre Window; the window policy (total); promotion of the Doc8 operations
- [x] **The whole of Part Three is formalised**, Doc1 to Doc9
- [x] A first runnable prototype: a full-screen terminal editor (open, type, move, save, quit), and a scripted mode for tests
- [ ] Decisions on the remaining findings (`FINDINGS.md`)
- [ ] Grow the editor to all the specification's operations, and prove each meets the corrected specification
- [ ] Refinement: the C gap buffer for Doc1 and the proof that it implements the Z operations
