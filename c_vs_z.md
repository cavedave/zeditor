# Where the C and the Z disagree

The monograph contains two descriptions of one editor, written by the same author: the Z specification (Part Three) and the C program (Appendix C). The book's method says the C is derived from the Z, by the refinement steps of Part Four. Where the two disagree is therefore some of the most informative evidence the book holds: each disagreement shows either where the specification drifted from what the author meant, or where knowledge lived in the code and never reached the specification.

This file gathers every disagreement we have found, sorted by kind. References are to findings in `FINDINGS.md`, claims in `issues_notdefined.md`, and pages of Appendix C (printed in roman numerals).

## Summary

| Kind | What it means | How many |
|---|---|---|
| A. The Z is wrong, the C does what was meant | the specification drifted from the author's intent; the code did not | 17 |
| B. The C knows something the Z does not say | knowledge that lived only in the code | 8 |
| C. The Z leaves a choice, the C makes one | allowed by the specification, but worth knowing | 6 |
| D. They agree, and both surprise | the disagreement is with the user, not between the two | 3 |
| E. A bug in the C as printed | what the listing would do if it is exactly what ran | 1 |

The pattern of A and B together is the main lesson. **Where the Z and the C disagree, the C is right**: in every case of kind A, the C does what the prose of the specification describes. And **where the C knows something the Z does not say**, a program rebuilt from the specification alone loses it. Our own prototype did exactly that (B1). Neither description alone holds the whole design.

## A. The Z is wrong, and the C does what was meant

In each case the printed Z gives no outcome, a contradictory one, or an unconstrained one, and the C does what the surrounding prose says.

| # | Behaviour | The Z | The C | Finding |
|---|---|---|---|---|
| A1 | Move left or right by a word or a line, from inside a word or line | no outcome at all | moves to the start or end of the word or line (`LeftMoveWord_Doc1`, p.ii) | 3 (D3) |
| A2 | → at the end of a line ending in a space | only "Editor full" | inserts a space and moves (`CursorRightChar_Doc4`, p.vii) | 5 |
| A3 | Paste | only "Editor full" (the marks contradict the invariant) | inserts the text and marks it (`Paste_Doc6`, p.ix) | 6a |
| A4 | Cut with the mark below the cursor | the document after it is unconstrained | removes the marked text (`RemMText`, p.ix) | 6b |
| A5 | Cut when the marked text repeats the text before the mark | no outcome at all | removes the marked text | 6c |
| A6 | Quit | no outcome unless the whole document is marked | saves if changed, then exits (`Quit_Quote`, p.xii) | 7a |
| A7 | Move to line *n* (type a number in the quote buffer) | no outcome: the command is missing from the list | moves to the line (`MoveLineNumberOrError_Quote`, p.xiii) | 7b |
| A8 | The empty quote command (quote key pressed twice) | no outcome | handled as above | 7b |
| A9 | Input a file while text is marked | no outcome (a missing prime) | reads the file (`Input_Quote`, p.xiii) | 7c |
| A10 | Reading a file | a successful read may return any text (`¬` inverted) | returns the file's contents (`ReadFromStore`) | 7d |
| A11 | An error while saving or reading | may change any file, or the document | changes nothing | 7e |
| A12 | Replace | a successful Replace leaves the text unchanged | replaces (`Replace_Doc8`, p.xi) | 8a |
| A13 | Search or Replace while a mark is set | no outcome when the text is found | searches; the mark is adjusted | 8b |
| A14 | Search away from a line ending in a space | no outcome | searches, and tidies the line | 8c |
| A15 | Down search | may move the cursor up | searches forward from the cursor (`DownSearch_Doc8`, p.xi) | 8d |
| A16 | Mark set at the top of the document | indistinguishable from no mark | a real mark, `MP = 0` (no mark is `MP = −1`) | 6d |
| A17 | Which side of the cursor the mark is on | ambiguous in some states ("ab\|ba") | always clear: the mark is a position | 6e |

## B. The C knows something the Z does not say

Behaviour that exists only in the code. A program built from the specification alone, as our first prototype was, does not have it.

| # | Behaviour in the C | Where | In the Z | Consequence |
|---|---|---|---|---|
| B1 | **Control characters in a file are discarded on reading, with a warning** ("CntrlFound") | `ReadFromStore`, `StartEditFile` | `Char` is any character | Our prototype, built from the spec, prints them to the terminal: a crafted file can change the terminal's window title (S1) |
| B2 | **A record of whether the document has changed** (`DocChanged`) | throughout | none | The Z cannot tell whether Quit or Save is needed; Quit may lose edits (7f) |
| B3 | **Crash recovery**: on a lost line (`SIGHUP`) or a fatal signal, unsaved work is written to `~/fred.save` before exiting | `PanicExit`, `PanicWriteToStore` | none | A 1990 feature that modern editors still need (vim's swap files) |
| B4 | **Backup file** written before saving over the original | `WriteBackupFile` | none | |
| B5 | **Suspend** with Ctrl-Z, and resume, restoring the terminal | `Suspend` | none | |
| B6 | **Interrupts**: a long operation can be stopped (`NoInterrupt`, `SIGINT`) | `SetInterrupts` | none | |
| B7 | **Open at a given line**, from the command line | `main` (`InitialLine`) | none | |
| B8 | **Files by name**: the real file system | `ReadFromStore`, `WriteToStore` | a pointer unrelated to the file name (7h) | Saving then reading the same name need not give the text back, in the Z |

## C. The Z leaves a choice, and the C makes one

The specification deliberately allows several outcomes; the C picks one. Not disagreements in the strict sense, but these are the choices a reimplementation must make again.

| # | Choice | The Z allows | The C chooses | Our editor |
|---|---|---|---|---|
| C1 | Empty lines at the end of the document | removing them, or keeping one (in one case) | removes them all, including a file's final newline | 1990 edition: the same; 2026 edition: keeps the final newline (D4) |
| C2 | Tab width | any positive number of spaces | to the next multiple of 8 (`tabstop`) | the same |
| C3 | Padding when the cursor moves past the text | any amount of padding (finding 5b) | exactly enough | exactly enough |
| C4 | When the window scrolls | any window that contains the cursor | redraws only when no key is waiting; scroll and pan rules | keep the window while the cursor is in it, else move just enough |
| C5 | The mark after a cursor move | anywhere (finding 6d) | adjusted for spaces and newlines added or removed (`Update_Doc6`, p.viii) | the same, as the C (decision D5) |
| C6 | "Editor full" | always allowed (N3) | only when the fixed-size array is full | never (memory is not fixed) |

## D. They agree, and both surprise

The Z and the C agree, but the behaviour surprises a user. Found by stating claims the monograph never made (`issues_notdefined.md`).

| # | Behaviour | Finding |
|---|---|---|
| D1 | Typing "a␣", then ←, deletes the space: "a␣", ←, →, "b" gives "ab" | N1 |
| D2 | Enter then Backspace in "ab␣\|cd" gives "abcd" | N2 |
| D3 | Word moves treat a run of spaces as a word, so "delete word" at `cat\|␣sat` deletes only the space | (demo) |

## E. A bug in the C as printed

| # | What | Detail |
|---|---|---|
| E1 | When the tidying runs, and what the bug really does | The Z tidies after *every* operation. The C was written to tidy only after certain kinds of operation. But the first test is written `OPType=LeftMove`, an assignment (bug #605). Because `=` binds more loosely than `||` in C, the line means `OPType = (LeftMove || …)`, that is `OPType = 1`, which is `LeftInsert`. If the listing is exactly what ran, then after every key, cursor moves included: `RemTrailNL` never runs (it needs `LeftMove` or `RightInsert`); `Update_Doc6` clears the mark, so a mark could never survive a cursor move and marking could not work; and `Update_Doc8` sets `DocChanged`. Broken marking is too obvious to have gone unnoticed, so the printed line is probably not what was compiled (a printing or transcription difference, or a different version). The monospaced font confirms a single `=` in the listing (`docs/eyecheck/pv_C605_OPType_zoom4x.png`); a photograph of the physical page is requested. (An earlier version of this note said the bug sets `OPType` to `LeftMove` and makes the C tidy after every operation as the Z does; that ignored C's operator precedence and was wrong.) |

## Errors in the C itself

Not disagreements with the Z, but recorded here for completeness (from `FINDINGS.md`):

- **#605**, above.
- **#802**: `PanicWriteToStore` declares `SysFtr` and uses `SysPtr`. Either a printing error or code that would not compile as printed.
