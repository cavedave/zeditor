# Claims the monograph does not make

`FINDINGS.md` records where the printed specification is wrong. This file is about something different: **behaviour the specification never states at all**, and what happens when it is stated and checked.

## Why look for missing claims

The monograph states **structural** claims: initialisation establishes each invariant (PO 0), each operation preserves it (PO 1), the operations of §1.6 are "total" (always have an outcome), word views are unique. Where those claims are false, we found them false; that is most of `FINDINGS.md`.

It states almost no **behavioural** claims, the kind a user relies on:

- *round trips*: Cut then Paste gives the text back; Save then reading the file gives the same text;
- *progress*: a down search moves forward;
- *safety*: Quit never discards unsaved changes; an error changes nothing;
- *liveness*: an insertion succeeds when there is room.

Such claims matter because of **slip risk**: the chance that a one-symbol writing mistake (a missing prime `′`, a `¬`, `Left` for `Right`) changes the meaning while still looking plausible and still being well-formed. A slip survives as long as no claim depends on it. State the claim and check it, and the slip shows.

## Method

For each claim:

1. state it precisely, as a Lean theorem;
2. check it against **the printed specification**, against **our corrected version** where we have one, and against what **the C** does;
3. record the result. If the claim fails, say whether that is an error, or a consequence of the design that the author may not have intended.

All the Lean is in `ZEditor/Claims.lean`, which builds as part of `lake build`. Every result below is proved there.

## Summary

| # | Claim | Printed spec | Our current version | The C | What it showed |
|---|---|---|---|---|---|
| C1 | Cut then Paste gives the text back | **fails** (Paste impossible) | **fails** on "ab\|ba" | holds | **New finding 6e**: the mark's side of the cursor is ambiguous. With the mark as a position, as in the C, the claim is **proved for every document** |
| C2 | An editor that refuses every insertion does *not* meet the spec | **fails**: it does meet it | fails | n/a | **New finding N3**: no operation is ever required to succeed |
| C3 | An error changes nothing | holds for Doc1–Doc6; **fails** for file operations | (same) | holds | Confirms finding 7e |
| C4 | Quit never discards unsaved changes | **fails** | fails | holds | Confirms finding 7f |
| C5 | Reading a file gives back what was written | **fails** | fails | holds | Confirms findings 7d, 7h |
| C6 | A down search moves forward | **fails** | fails | holds | Confirms finding 8d |
| C7 | Moving the cursor does not change the text | **fails** | **fails** | **fails** | **New finding N1**: stepping back over a space you just typed deletes it |
| C8 | Enter then Backspace gives back the text | **fails** | **fails** | **fails** | **New finding N2**: a space between two words is lost |

C7 and C8 fail in the C too. They are not slips but consequences of a design rule, and only stating the claim brings them out.

## The claims in detail

### C1. Cut then Paste gives the text back

Cut the marked text, then Paste it straight back: the text should be unchanged.

- **Printed:** fails. In "x[ab]|y" Cut correctly leaves "x|y", but the printed Paste is then impossible (finding 6a). Lean: `printed_cut_paste_fails`.
- **Our first fix** (repairing the `Left`/`Right` slip of finding 6b): fails too, which we did not expect. The monograph stores the mark as two text sequences, `MarkSeq` and `MarkedSeq`. In "ab|ba" with `MarkSeq = a` and `MarkedSeq = b`, they fit two ways at once: the mark one place back (the "b" *before* the cursor is marked), or one place forward (the "b" *after* it is marked). The state does not say which. Cut has to remove both, which is impossible, so it has no outcome. This is **finding 6e**. Lean: `mark_side_ambiguous`, `remMTextC_no_outcome`.
- **The mark as a position**, as the C keeps it (`MP`, with −1 for no mark): the claim holds, **for every document**. Lean: `cut_then_paste`.

So the repair for §5 is not to patch the schemas one at a time but to adopt the C's *representation* of the mark. That removes findings 6b, 6d and 6e together.

### C2. An editor that refuses every insertion does not meet the specification

It does meet it. "Editor full" (`ErrorFull`) has no precondition: it is always a permitted answer to an insertion, to Paste, and to every up, down, right and page move of the cursor. A program that never inserts anything and never moves the cursor up or down satisfies those parts of the specification. Lean: `insert_may_always_refuse`, `paste_may_always_refuse`, `cursorDown_may_always_refuse`.

The reason is deliberate. Part Two's "∞-refinement" lets the abstract specification ignore memory limits by allowing "full" anywhere. But nothing then says when the editor *must* succeed: the specification has no capacity, so it cannot say "if there is room, the insertion succeeds". This is **finding N3**. It is also why findings 5 and 6a went unnoticed: where an operation was stuck, "Editor full" was still a permitted answer, so the bug looked like a resource limit.

### C3. An error changes nothing

- **Holds** for the document operations: every error of Doc1 is `Doc1Unchanged`. Lean: `doc1_errors_change_nothing`.
- **Fails** for the file operations of §6 (finding 7e). In Z, a branch of an operation that does not mention a variable leaves it unconstrained. So "Cannot open file" may change any file, and a failed Input may replace the whole document. Lean: `writeToStore_cannot_open_any`, `input_error_any_document`, `save_any_store`.

### C4. Quit never discards unsaved changes

Fails. Whenever Quit can run at all (finding 7a), it may answer "Document not changed" and exit without writing anything, whatever has been typed. The specification keeps no record of whether the document has changed (finding 7f). Lean: `quit_may_discard`. The C keeps a `DocChanged` flag. Our prototype editor asks for Ctrl-Q twice when there are unsaved changes.

### C5. Reading a file gives back what was written

Fails, twice over. Even at the same storage pointer, straight after a successful write, a successful read may return any text, because `SysRead` is inverted (finding 7d). Lean: `write_then_read_any`. And nothing links a file name to a storage pointer (finding 7h), so a file written as `notes.txt` need not be the one read back as `notes.txt`.

### C6. A down search moves forward

Fails. The "first match after the cursor" condition is empty when the match is behind the cursor, so a down search may jump backwards (finding 8d). Lean: `downSearch_may_go_up`.

### C7. Moving the cursor does not change the text

Fails, by design, in the specification and in the C alike. The Doc3 rule forbids spaces at the end of a line to the right of the cursor, and the tidying runs after *every* operation, moves included. So:

- type "a␣": the text is "a␣|", allowed because the space is left of the cursor;
- press ←: the text would be "a|␣", with a trailing space right of the cursor, so the tidying deletes it, giving "a|";
- press →, type "b": the text is "**ab**", not "a b".

Lean: `step_back_deletes_space`. Tried on the running editor: typing `a␣`, ←, →, `b` saves the file as `ab`. This is **finding N1**. The C's `RemTrailWS` does the same.

### C8. Enter then Backspace gives back the text

Fails, by design. In "ab␣|cd" (cursor after the space):

- Enter makes "ab␣" a finished line, and a finished line may not end in a space, so the space is removed: "ab" / "|cd";
- Backspace joins the lines again: "ab|cd".

The text "ab cd" has become "**abcd**". Lean: `enter_backspace_loses_space`. Tried on the running editor, with the same result. This is **finding N2**. The C does the same.

N1 and N2 come from the same rule: "no trailing spaces", applied eagerly. The rule's purpose was sound (on a 1990 terminal a trailing space is invisible), but applied after every keystroke it deletes text the user typed on purpose. Stating the user's expectation as a claim is what made this visible.

## Not defined at all

Some behaviour the specification deliberately leaves open, and an implementation must choose:

- **Tab width.** A tab inserts "one or more" spaces (`InsTab`). Our prototype uses the next multiple of 4.
- **Key bindings.** No operation is tied to a key.
- **Capacity.** There is no maximum size, so "Editor full" is never required and never forbidden (C2).
- **When to scroll.** The window may move whenever the cursor stays in view (`CursorInWindow`).
- **The mark after a cursor move.** When a mark is set, a cursor move may leave it anywhere (`CursorOps_MarkSet`, finding 6d).

## Claims still to check

- A down search finds the *nearest* match, not just some match.
- Replace leaves the replacement text at the cursor.
- Lift copies exactly the marked text.
- Insert a character, then Backspace, gives back the text (expected to hold).
- From every state, every key has an outcome at the top level, Doc9. This would collect all the "stuck" findings in one statement.
