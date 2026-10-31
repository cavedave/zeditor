# To do

The working list. Finished items move to the status list in `README.md`.

## Decisions on the findings (`FINDINGS.md`)

- [x] D1 what a line is (finding 1)
- [x] D2 telling words apart (finding 2)
- [x] D3 word and line moves, following the C (finding 3)
- [ ] One short write-up for the ill-formed and minor findings: 4a, 4b, 4d (deferred for now)
- [ ] The real choices, which change how the editor behaves:
  - [x] 4c: the final newline is kept (decision D4, ★ modern convention)
  - [ ] Follow-up to D4: add a final newline on save if a file lacks one, as vim and nano do?
  - [x] 6a–6e: the mark is a position, as in the C (decision D5); edits clear it, moves keep it on the same text
  - [ ] Follow-up to D5: keep the mark through edits, as Emacs does?
  - [x] 7f: a changed flag, as the C's `DocChanged` (decision D6)
  - [x] 7h: the real file system, as the C (decision D7) — **to discuss**: what the specification should say about files
  - [x] 9b: centre on the true middle line, `(WinHeight + 1) / 2` (decision D8, ★ modern convention)
- [ ] The design findings found by stating claims: N1 (moving deletes a space), N2 (Enter then Backspace loses a space), N3 (nothing is required to succeed)
- [ ] The remaining "follow the C" findings: 5, 7a, 7b, 7c, 7d, 8a, 8b, 8c, 8d
- [ ] The frame finding 7e (errors change nothing), and the ill-formed/minor 5b, 7g, 8e, 9a, 9c

## The editor: a minimum viable product

- [x] First prototype: open, type, Enter, Tab, Backspace, Delete, arrows, Ctrl-S save, Ctrl-Q quit; scripted mode; `tests/save.sh`
- [ ] Choose and document key bindings
- [ ] Word and line moves (decision D3)
- [x] Mark, Lift (copy), Cut, Paste (decision D5); `tests/mark.sh`
- [ ] Show the marked text on screen (highlight)
- [ ] Search and Replace
- [ ] Quoted commands: save as, write, append, input, move to line, escape to the shell
- [ ] Centre the window (using `MidWinHeight`, decision D8)
- [ ] Characters beyond ASCII (UTF-8 input)
- [ ] Terminal resizing (the specification assumes a fixed window size)
- [ ] Prove the editor's operations meet the corrected specification (refinement)
- [ ] Change the Lean specification's Doc3 invariant to decision D4 (at most one empty line at the end), and Doc5/Doc6 to decision D5 (the mark as a position)

## After the MVP

- [ ] **A property-based fuzzer.** Random key sequences on the editor, checking after every key the Doc3 invariant, and round-trip claims (Enter then Backspace, insert then Backspace, Cut then Paste, copy all then Paste). A good test of it: it should rediscover findings N1 and N2 on its own.
- [ ] Example ("golden") tests, one per decision, showing the corrected behaviour with an exact expected screen

## Security

The specification is about correctness (doing the right thing to the text). It says nothing about what the text can do to the terminal, to a reader, or to an AI that reads the file.

- [ ] **S1. Control codes in a file reach the terminal.** The prototype prints document characters straight to the screen. A file containing the escape sequence `ESC ] 0 ; … BEL` changes the terminal's window title when opened (confirmed on the raw output, 2026-10-31); some terminals act on other escape sequences too. Fix: show control characters visibly, as vim does (`^[`).
  *Note:* the 1990 C did handle this. Its `ReadFromStore` discards control characters when reading a file and warns the user (`CntrlFound`), probably to protect the screen rather than for security. The specification never mentions it (`Char` is any character), so our prototype, built from the specification, lost the protection. The mirror image of the main finding: where spec and code disagreed the code was right, but where the code knew something the spec did not say, rebuilding from the spec dropped it. (The C's way silently deletes the characters, so saving changes the file; showing them is better.)
- [ ] **S2. Invisible characters are invisible.** Unicode tag characters (used inside some flag emoji, and used by attackers to hide instructions that an AI reads but a person does not see), direction-control characters ("Trojan Source"), zero-width characters, and look-alike letters. Fix: show them visibly or mark them.
- [ ] **A claim to prove: "what you see is what is in the file".** No document character reaches the terminal as a control code, and every invisible character is shown visibly. This conflicts with the specification's assumption that one character takes one column (Doc2, Doc9), so the display part of the specification must change.
- [ ] **An edit log with hashes.** Record each edit as (SHA-256 before, the operation, SHA-256 after). With a deterministic, verified core, anyone can replay an edit and compare hashes: the hash shows *what* the file is, and replay shows whether the edit did what it claimed. Relevant to agents editing files.

## Proofs and claims

- [ ] A full proof of the Doc3 proof obligation (now checked exhaustively up to 8 characters)
- [ ] The claims still to check (`issues_notdefined.md`): the nearest match in a down search; Replace leaves the replacement; Lift copies exactly the marked text; insert then Backspace; every key has an outcome at the top level
- [ ] Optional: the C's gap buffer in Lean, proved to implement the Z (the book's Part Four, made formal)

## Evidence

- [ ] Photographs of the doubtful pages from a physical copy (`docs/photo-requests.md`)
- [ ] Optional: transcribe Part Four and Appendices A and B, to compare our refinement with the author's

## Writing

- [ ] `LESSONS.md`: reading an old formal text; the mistakes of the time, classified, with methods to avoid them; hardware constraints and an assumption register
- [ ] Discussion: why revisit a formal specification from 1990 (area 1)
- [ ] Discussion (after all decisions are made): specifications, functional programming and side effects. Do "pure" mathematical descriptions struggle with effects such as a file system? How the Z models the outside world (an abstract `Store`, finding 7h, decision D7), how Lean separates effects (`IO`), and what that means for specifying an editor
- [ ] Paper, "what a 30-year-old formal specification teaches us": literature search first (mechanised checking of published Z, e.g. with Z/EVES or ProofPower; finding errors in published designs with Alloy); consider asking D. S. Neilson to comment or co-author

## Ideas (research directions)

- [ ] Compare with vi and Emacs: test the editor-independent claims of `issues_notdefined.md` against them, driven headless (`vim -es`, `nvim --headless`, `emacs --batch`); parameterise the specification (word rule, whitespace policy, cursor after delete) and find which parameters each editor implements
- [ ] What 35 years added: undo/redo, crash recovery, Unicode and display width, resizing, soft wrap, multiple files, incremental search, collaborative editing, and more. Try adding them to the specification: features that sit on top (undo) fit Neilson's hierarchy; cross-cutting ones (Unicode changes `Char` at the bottom) do not. Start by making `Char` and display width parameters and seeing which proofs survive
- [ ] Feeding back into Lean: a verified "apply an edit, convert a position" core for language servers (UTF-16 vs UTF-8 positions); a trustworthy edit layer for agents (proved frame properties plus hashes); a small "Z in Lean" library for porting other legacy specifications

## Repository

- [ ] Change the GitHub description from "PhD thesis" to "Technical Monograph PRG-101 (1990)"
