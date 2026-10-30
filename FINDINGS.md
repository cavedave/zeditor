# Findings tracker

Problems in the printed specification found by the formalisation. The detailed write-ups are in `README.md` ("What the formalisation found"); the evidence is in the Lean files. **Decisions are deliberately left open** until the whole specification has been worked through.

Severity:
- **stuck**: a user action has no correct outcome (only an error, or no outcome at all)
- **unsafe**: an operation may do something it should not
- **ill-formed**: the Z does not type-check or is undefined as written; the intent is clear
- **weak**: the spec allows behaviour its own text says it should not
- **minor**: errors in the book's informal proofs or naming, no effect on the spec's meaning

For each finding the Lean development currently uses the reading shown in "Reading used". For **stuck** and **unsafe** problems, both the printed version and the corrected version are defined.

| # | § | Finding | Severity | Lean evidence | C behaviour | Reading used | Decision |
|---|---|---|---|---|---|---|---|
| 1 | 1.2 | `Line ≙ seq (Char − {nl})` excludes the newline lines the book's own examples use; line views then don't exist (or aren't unique) | ill-formed | `printed_lines_have_no_nl`, `printed_lines_not_unique` | n/a | `seq₁ (Char − {nl}) ∪ {⟨nl⟩}` | **Fixed** to the intended definition ([D1](#d1-what-a-line-is)) |
| 2 | 1.2 | `DocWordSeq` uses `rng w = NonWhiteSpace` where `⊆` is meant: the rule never applies, so word views are not unique and Corollary 3:1.2a fails | ill-formed | (comment in `DocWordSeq`) | n/a | `⊆` | **Fixed**: read `=` as `⊆` ([D2](#d2-telling-words-apart)) |
| 3 | 1.6 | Word and line moves are not total: inside a word or line there is no outcome at all | stuck | `leftMoveWord_Doc1_stuck` | moves (`LeftMoveWord_Doc1`) | C reading (`MvWordC`, `MvLineC`), content kept as characters | **Fixed** ⚠ follows the C ([D3](#d3-moving-by-a-word-or-a-line)) |
| 4a | 3.3 | `RemTrailWS` is declared on `ΔUD` but uses `Left_Char`/`Right_Char` | ill-formed | (definition on `ΔDoc2`) | n/a | `ΔDoc2` | open |
| 4b | 3.1 | `visibleseq` uses `last L` on a possibly empty sequence | ill-formed | (comment in `visibleseq`) | n/a | empty sequence is a visibleseq, as the prose says | open |
| 4c | 3.1 | The empty-line invariant allows one invisible empty line at the end of the document, contrary to its stated purpose | weak | `Check.lean` | removes it | as printed | open |
| 4d | 2.2 | Consistency proof says `Uₙ = ⟨l, r⟩` for `l ⁀ r`; Lemma 3:2.2d cites lemmas that don't exist | minor | `FDLinv_append`, `Initialize_Doc2_display` | n/a | n/a | open |
| 5 | 4.2.2 | → (`CursorRightChar`) after typing a space at the end of a line can only answer "Editor full"; `PadWSNL` is not total as claimed | stuck | `cursorRight_after_space`; `Check.lean` (3,581 cases, all this one) | inserts a space and moves | both defined (`PadWSNL`, `PadWSNLC`) | open |
| 5b | 4.2.2 | Padding may add surplus spaces that the tidying operations don't remove; only `ΔDoc4` excludes them | minor | (README) | pads exactly | as printed | open |
| 6a | 5.2 | Paste can only answer "Editor full": `Pst` sets `MarkedSeq′ = ⟨⟩` instead of `PBuff`, breaking the `MarkedText` invariant | stuck | `pst_impossible`, `paste_only_full` | marks the pasted text | both defined (`Pst`, `PstC`) | open |
| 6b | 5.2 | Cut with the mark below the cursor may replace the whole document (`Left_Char` for `Right_Char`, #313) | unsafe | `remMText_mark_below_unconstrained` | removes the marked text | both defined (`RemMText`, `RemMTextC`) | open |
| 6c | 5.2 | Cut has no outcome at all when the marked text repeats the text before the mark (e.g. "aa\|", mark in the middle) | stuck | `remMText_both_premises`, `cut_no_outcome` | removes the marked text | both defined | open |
| 6d | 5.1 | A mark set at the top of the document is indistinguishable from no mark; as printed, cursor moves may create a mark from nothing | weak | `setMark_at_top`, `cursorOp_mark_unconstrained` | `MP = −1` for no mark | as printed | open |

| 7a | 6.4.4 | Quit has no outcome unless the whole document is marked: `RequestQuit` says both `WriteSeq! = MarkedSeq` and `WriteSeq! = Left_Char ⁀ Right_Char` | stuck | `quit_stuck` | writes the document if changed, then exits | as printed | open |
| 7b | 6.5 | Move-to-line can never run: `MoveLineNumber_Quote` is missing from `Quote_StateQuote`, and a number is valid quote text, so it is not a "Quote error" either. The empty command (quote key pressed twice) is stuck the same way | stuck | `moveToLine_stuck`, `emptyQuote_stuck` | `MoveLineNumberOrError_Quote` is the fall-through case | as printed | open |
| 7c | 6.4 | Input has no outcome while text is marked: `QuoteRequestContentChange` has unprimed `MarkedSeq = ⟨⟩` | stuck | `input_marked_stuck` | reads the file | as printed | open |
| 7d | 6.2 | `SysRead` is inverted (`¬ NoReadError! ⇒ ReadSeq! = …`): a successful read may return any text | unsafe | `sysRead_success_any` | returns the file | as printed | open |
| 7e | 6.2–6.6 | Error branches leave the file store, the document or the document name unconstrained (Z schema disjunction): "Cannot open file" may change any file; a failed Input may replace the document with anything; "Document not changed" may change any file; editing the quote buffer may rename the document | unsafe | `writeToStore_cannot_open_any`, `input_error_any_document`, `save_any_store`, `quoteEdit_any_name` | n/a | as printed | open |
| 7f | 6.4.2, 6.4.4 | No record of whether the document has changed, so Save and Quit may always answer "Document not changed"; Quit may exit without saving edits | unsafe | `save_any_store` | `DocChanged` flag | as printed | open |
| 7g | 6.2–6.7 | Undefined or ill-typed names: `DocCurX′`/`DocCurY′`, `ExchMTextPBuff`, `CursorLeftChar_Quote`/`CursorRightChar_Quote`, `rep!` in `ErrorIllegalQBuffEditOp`, `SysReturnControl` composed as if a schema, `ΔDocI`, `UnsuitableFile`, `SuccGetSysPtr` | ill-formed | (comments in `Doc7.lean`) | n/a | obvious readings | open |
| 7h | 6.2, 6.4.6 | `SysGetPtr` does not relate the pointer to the file name, so files are not identified by name (saving then reading the same name need not give the text back); `RequestMvLineNumber` leaves the document content unconstrained; line number 0 gives `UDCurY′ = 0`, which has no outcome | weak | (comments in `Doc7.lean`) | n/a | as printed | open |

| 8a | 7.5 | Replace cannot replace: `PromoteReplace` contains `Ξ_Cont Doc1` (content unchanged), so a successful Replace leaves the document as it was; at a match the only general answer is "Editor full" | stuck | `replace_ok_unchanged` | replaces | as printed | open |
| 8b | 7.3 | Search with a mark set has no outcome when the text is found: `PromoteSearchUnMark` has unprimed `MarkSeq = ⟨⟩` (same in `PromoteReplaceUnMark`) | stuck | `downSearch_marked_stuck`, `replace_marked_full` | searches; the mark is adjusted | as printed | open |
| 8c | 7.3 | Search from a line ending in a space has no outcome when the text is on another line: `PromoteSearch` also contains `Ξ_Cont Doc1`, which forbids the tidying the Doc3 invariant then requires (the prose itself says a search may remove whitespace) | stuck | `xiCont_other_line_visible` | searches and tidies | as printed | open |
| 8d | 7.3–7.4 | A down search may move the cursor up (and an up search down): "first match" is stated as an empty range when the match is behind the cursor; nothing requires moving forward | unsafe | `downSearch_may_go_up` | searches forward from the cursor | as printed | open |
| 8e | 7.2–7.5 | `regexpmatches` constraint `# e ≥ s` does not type-check; `matches` uses an undefined `s`; `matchedlength` has only its domain specified, so the amount of text a Replace removes is unconstrained; `CopyQBuffRBuff` renames schemas instead of variables; `ErrorReplaceFull_Doc` lacks `rep!`; the disjunct grouping of the search/replace operations contradicts Z precedence | ill-formed | (comments in `Doc8.lean`) | n/a | layout grouping; `matchedlength` a parameter | open |
| 9a | 8.2 | Lemma 3:8.2a ("the character under the window cursor is the one under the display cursor") is undefined when the cursor is after the last character of its line, which is always the case in the empty document; proof step 8 (and 8.2c step 6) mix up `WinWidth` and `WinHeight`; `Window` writes `# WinLines` | minor | `Doc9.char_at_cursor` (the true, partial-indexing form) | n/a | partial indexing | open |
| 9b | 8.2.1 | `HalfWinHeight = WinHeight/2` is said to be at least 1, but is 0 for a one-line window; Centre Window then has no outcome | stuck (edge case) | `centreWindow_height_one`; total for `WinHeight ≥ 2` (`CentreWindow_Doc9_total`) | n/a | as printed | open |
| 9c | 8.2.2 | "We thus discharge PO 1 for each Doc8 operation": the window policy is total (proved), but this only carries totality up from Doc8, where it already fails for findings 3, 5, 6, 7 and 8 | minor | `WindowPolicy_total`, `promote9_total` | n/a | n/a | open |

## Decisions

How each decision was reached, with the evidence from the scan.

**Policy when following the C.** Where the printed specification gives no usable answer, and the C program printed in the same monograph shows what the author intended, we follow the C. Every such decision is marked **⚠ follows the C** in the table above and carries a warning at the top of its section. The warning says what we changed, why the printed specification cannot be used as it stands, and that the result is our reading of the author's intent rather than his text. Anyone who prefers the printed text can find both versions in the Lean code: the printed one under its original name, the C's version with a `C` suffix (for example `MvWord` and `MvWordC`).

### D1. What a line is

*Finding 1. Decided 2026-10-30: fix to the intended definition.*

**What the monograph says.** §1.2 (printed p.55, PDF p.58) defines

    Line ≙ seq (Char − {nl})

that is, a line is any sequence of characters that contains no newline (`nl`), including the empty sequence.

![The definitions of Word and Line, printed p.55](docs/eyecheck/p58_1_Line_definition.png)

**Why it is contradictory.** Two pages later (printed p.57, PDF p.60) the monograph gives its own example of the line view of a document. It takes the characters

![The example character sequence, printed p.57](docs/eyecheck/p60_1_example_chars.png)

that is, "the⏎canary⏎⏎ate", and splits them into the lines

    ⟨⟨t,h,e⟩, ⟨nl⟩, ⟨c,a,n,a,r,y⟩, ⟨nl⟩, ⟨nl⟩, ⟨a,t,e⟩⟩

in which every newline is a line of its own. By the definition on p.55, `⟨nl⟩` is not a line, so this example is not a line view. The very next definition, `DocLineSeq`, also tests whether a line equals `⟨nl⟩`, which no line could. The definition and the way it is used contradict each other. Taken literally:

- a document containing any newline has no line view at all, so moving or deleting by line is undefined for every multi-line document (`printed_lines_have_no_nl`);
- because empty lines are allowed, even the empty document has two different line views, `⟨⟩` and `⟨⟨⟩⟩`, so the function `FL` that the monograph declares one-to-one is not (`printed_lines_not_unique`), and Corollary 3:1.2c is false.

**What was intended.** The example, `DocLineSeq`, the lemmas of §1.2.2 and the C (`LeftMoveLine_Doc1` moves over a single newline, or back to the start of the line) all treat a line as *either a non-empty run of characters other than newline, or a single newline on its own*.

**Decision.** Use the intended definition:

    Line ≙ seq₁ (Char − {nl}) ∪ {⟨nl⟩}

This is `IsLine` in `ZEditor/Spec/Doc1.lean`. With it, every document has exactly one line view (proved: `lines_ok`, `DocLineSeq.unique`, `FL_lines`).

### D2. Telling words apart

*Finding 2. Decided 2026-10-30: read `=` as `⊆` (subset).*

**What the monograph says.** The box defining `DocWordSeq` (printed p.56, PDF p.59) says that in a valid word view no two adjacent words `w1`, `w2` are of the same kind:

![The DocWordSeq box, printed p.56](docs/eyecheck/p59_2_DocWordSeq.png)

    rng (w1) = WhiteSpace     ⇒  rng (w2) ≠ WhiteSpace
    rng (w1) = NonWhiteSpace  ⇒  rng (w2) ≠ NonWhiteSpace

`rng w` is the set of characters occurring in the word `w`. `WhiteSpace` is `{sp}`; `NonWhiteSpace` is every character except space and newline.

**Why it does not work as printed.** The symbol really is a plain `=` (confirmed by eye); the problem is its meaning, not its printing. The first line is fine: a word of spaces has exactly `{sp}` as its set of characters. The second line never applies: `rng (w1) = NonWhiteSpace` would need the word to contain *every* character other than space and newline, which no word does. So nothing forbids two non-space words next to each other, and "cat" has several word views, for example `⟨⟨c,a,t⟩⟩` and `⟨⟨c,a⟩,⟨t⟩⟩`. The corollary printed immediately below the box (Corollary 3:1.2a, "as a direct consequence of this definition … the sequences themselves are equal") is then false.

**Could we be wrong?** Possibly the author used `=` loosely, meaning "the word's characters are all of this kind"; written mathematics often does. That is exactly the `⊆` reading we adopt, so the question is only whether to call this an error in the text or an informal use of `=`. Taken strictly, as Z defines `=`, it is an error: the monograph's own corollary needs `⊆`. Read as `⊆`, the first line means the same as printed (a non-empty word whose characters are drawn from `{sp}` has exactly `{sp}`), and the second line gains the meaning the corollary needs. No other reading we can find makes the corollary true.

**Decision.** Read both lines with `⊆`:

    rng (w1) ⊆ WhiteSpace     ⇒  ¬ (rng (w2) ⊆ WhiteSpace)
    rng (w1) ⊆ NonWhiteSpace  ⇒  ¬ (rng (w2) ⊆ NonWhiteSpace)

This is `DocWordSeq` in `ZEditor/Spec/Doc1.lean`. With it, every document has exactly one word view (proved: `words_ok`, `DocWordSeq.unique`, `FW_words`), which is Corollary 3:1.2a.

### D3. Moving by a word or a line

*Finding 3. Decided 2026-10-30: adopt the C's behaviour. A move keeps the text unchanged as characters, not as words or lines.*

> **⚠ This decision follows the C, not the printed specification.**
>
> As printed, moving left or right by a word or a line has **no result** whenever the cursor is inside a word or a line. The specification gives neither a move nor an error, so it does not say what the editor should do. We have made the editor do what the C program in the same monograph does: move to the start (or end) of the word or line. We believe this is what the author intended (he defines the necessary rule himself, in §1.3, but does not use it here). It is nevertheless our reading, not his text. The printed operations are kept in the Lean code as `MvWord` and `MvLine`, next to the versions we use, `MvWordC` and `MvLineC`.

**What the monograph says.** §1.1.1 (printed p.54, PDF p.57) defines one generic move, `Mv[X]`. It works on a pair `Left`, `Right` of sequences of `X`: "*Left* must not be empty, its last element being moved to the beginning of *Right*". The text is kept unchanged by `Ξ_Cont`, "a before- and after-document whose content hasn't changed (i.e. it allows for a change of current position)", defined as `Left ⁀ Right = Left′ ⁀ Right′`:

![Ξ_Cont and the generic move Mv, printed p.54](docs/eyecheck/p57_3_XiCont_and_Mv.png)

§1.2.1 (printed p.58, PDF p.61) then uses the same move for characters, words and lines: `Mv_Word ≙ Mv[DocWordSeq]`, `Mv_Line ≙ Mv[DocLineSeq]`. Its expansion of `Mv_Line` shows what that means: `Left`, `Right`, `Left′` and `Right′` must all be valid line sequences, and the content is kept unchanged *as a sequence of lines*:

![Mv for words and lines, and the expanded Mv_Line, printed p.58](docs/eyecheck/p61_3_MvWord_MvLine.png)

§1.6, "The Total Operations On The Doc1 State", then defines, for example, `LeftMoveWord_Doc1 ≙ (LeftMvWord ∧ Success) ∨ ErrorTopOfDoc`. "Total" means the operation always has an outcome. Its expansion for lines (printed p.68, PDF p.71):

![LeftMoveLine_Doc1 expanded, printed p.68](docs/eyecheck/p71_3_LeftMoveLine_Doc1.png)

**Why it gets stuck: an example.** Take the document "cat" with the cursor between `a` and `t`: "ca|t".

- Seen as words, the cursor splits the word: `Left` is the one word "ca", and `Right` is the one word "t".
- Move left by a word: the last word of `Left`, "ca", moves to the front of `Right`, so `Right′` would be the two words "ca", "t".
- But two letter-words side by side are not a valid word sequence. That is exactly what the word rule forbids (see D2), and `Right′` must be valid. So there is no allowed result.
- The error case, `ErrorTopOfDoc`, applies only when the cursor is at the top of the document, and here it is not.

So the operation has **no outcome at all**: not a move, not an error message. The same happens for lines: in "ab|c", moving left by a line would make `Right′` the two text lines "ab", "c" with no newline between them, which `DocLineSeq` forbids. This happens whenever the cursor is inside a word or a line, which is most of the time. Lean proves it for "ca|t" (`leftMoveWord_Doc1_stuck`).

**What the C does.** `LeftMoveWord_Doc1` (Appendix C, p.ii) moves the cursor back over a newline, a run of spaces, or the rest of the word, and always succeeds unless the cursor is at the top:

```c
int LeftMoveWord_Doc1()
{
 if (CP!=0) { if       (GetArrCont(CP)==nl) { CP--; }
              else if (GetArrCont(CP)==sp) { LMWSWord(); }
              else                         { LMNWSWord(); }
              return(OK);
            }
 else       { return(Top); }
}
```

From "ca|t" it moves to "|cat". `LeftMoveLine_Doc1` does the same for lines.

**What was intended.** The move should keep the text unchanged *as characters*, and the word and line views on each side are then recomputed from the characters. In the example, "ca" joins "t" and becomes the word "cat". The monograph defines exactly this in §1.3 as `Ξ_Cont Doc1 ≙ Ξ_Cont Pair[Char] ∧ ΔDoc1`, but does not use it for the moves.

**Could we be wrong?**
- For words, the problem only appears once the word rule works as intended (D2). With the printed `=` (finding 2), "ca" next to "t" would be allowed and the move would succeed, so one could argue that the two errors cancel out. They do not fully. With the printed rule a document's word view is not unique, so the monograph's Corollary 3:1.2a fails. And nothing rescues lines: the line rule `DocLineSeq` is printed correctly, and forbids two text lines side by side under either definition of a line (D1).
- Perhaps the author meant word and line moves to be used only at word or line boundaries. But nothing in the specification restricts the cursor in that way. Character moves put it inside words, and §1.6 calls these operations total. The C moves from anywhere.

**Decision.** Use the C's behaviour. A word move keeps the characters unchanged (`Ξ_Cont Doc1`), requires `Left_Word ≠ ⟨⟩`, and sets `Left_Word′ = front Left_Word`; the same for lines. These are `MvWordC` and `MvLineC` in `ZEditor/Spec/Doc1.lean`. Lean proves that this gives the C's result ("ca|t" to "|cat", `leftMvWordC_caT`), and that with it all fifteen operations of §1.6 are total (`LeftMoveWordC_Doc1_total` and the others in `ZEditor/Spec/Total.lean`).

## Readings to confirm by eye

**All 11 confirmed by eye on 2026-10-30.** Every finding that rests on a single symbol has now been checked independently against the scan; none was a misreading.

These findings rest on one symbol or line in the scan. Each was checked from page images at 160–200 dpi; an independent check against the printed page is worthwhile before any decision. Page numbers are PDF pages of `source/Zeditor.pdf` (printed page in brackets).

The scan is 1-bit black-and-white at 199 ppi, so nothing finer than that can be recovered from it. The checklist pages are extracted at exactly the native resolution, with no resampling, in `docs/eyecheck/` (named by page and finding). Only a physical copy or an independent scan could do better. No other copy has been found (searched 2026-10-30); the scan's SHA-256 is `5c00b1450a147cddf8248f11cb5d12de1f68fc40ff3fcfee46ffbc48499608e3`, so any copy with that checksum is this same scan.

| ✓ | Finding | What to look at | Page |
|---|---|---|---|
| ✓ | 1 | `Line ≙ seq (Char − {nl})`, not `seq₁`, and no `∪ {⟨nl⟩}` (confirmed by eye 2026-10-30) | 58 (55) |
| ✓ | 2 | `DocWordSeq` box: `rng (w1) = NonWhiteSpace` with a plain `=` (not `⊆`) (confirmed by eye 2026-10-30) | 59 (56) |
| ✓ | 5 | `PadWSNL`: `UDLines QPCurY visible_prefix UDCurLine′` (visible_prefix, not prefix) (confirmed by eye 2026-10-30; the same schema uses plain `prefix` in its second case, so the choice was deliberate) | 88 (85) |
| ✓ | 6b, 6c | `RemMText`, third line: `MarkedSeq ⁀ MarkSeq = Left_Char` (Left, not Right) (confirmed by eye 2026-10-30) | 92 (89) |
| ✓ | 6a | `Pst`: `MarkedSeq′ = ⟨⟩` (confirmed by eye 2026-10-30) | 93 (90) |
| ✓ | 7d | `SysRead`: `¬ NoReadError! ⇒ ReadSeq! = …` (the ¬) (confirmed by eye 2026-10-30: a single ¬ at the start of the predicate, the only negation in the schema) | 98 (95) |
| ✓ | 7c | `QuoteRequestContentChange`: `MarkSeq′ = MarkedSeq = ⟨⟩` (no prime on MarkedSeq) (confirmed by eye 2026-10-30) | 101 (98) |
| ✓ | 7a | `RequestQuit`: both `WriteSeq! = MarkedSeq` and `WriteSeq! = Left_Char ⁀ Right_Char` (confirmed by eye 2026-10-30) | 104 (101) |
| ✓ | 7b | `Quote_StateQuote`: eight disjuncts, no `MoveLineNumber_Quote` (confirmed by eye 2026-10-30) | 108 (105) |
| ✓ | 8b, 8c | `PromoteSearch` contains `Ξ_Cont Doc1`; `PromoteSearchUnMark`: `MarkSeq = MarkedSeq′` (no prime on MarkSeq) (confirmed by eye 2026-10-30) | 114 (111) |
| ✓ | 8a, 8b | `PromoteReplace` contains `Ξ_Cont Doc1`; `PromoteReplaceUnMark`: no prime on MarkSeq (confirmed by eye 2026-10-30) | 117 (114) |
| ✓ | 8d | `SuccDownSch_Doc`: `n, m = (# Left_Char + 2), (# Left_Char′ + matchedlength (SBuff, Right_Char′) − 1)` (confirmed by eye 2026-10-30) | 112 (109) |

## Errors in the C

| # | Where | Finding | Note |
|---|---|---|---|
| C1 | `RemTrailWS` (#605) | `if (OPType=LeftMove \|\| …)` assigns instead of comparing | Always true; makes the C run both tidying routines after every operation, which matches the Z. Later code reading `OPType` sees the wrong value. |
| C2 | `PanicWriteToStore` (#802) | declares `SysFtr`, uses `SysPtr` | Would not compile as printed (or a transcription/print error). |

## Errors in the book's text (transcription notes)

See `docs/corrections.csv` for the full list. Ones that affect meaning:
- `Rel` defined with `invrel` (p.13) and restated with `absinv` (p.17).
- Proof of Lemma 3:1.2.2b repeats the steps of Lemma 3:1.2.2a.
- `Window` uses `# WinLines` for `WindowLines`; Lemmas 8.2a and 8.2c mix up `WinWidth` and `WinHeight`.
- `ErrorReplaceFull_Doc` uses `rep!` undeclared.
- Names that differ between definition and use: `ErrorQPAtTop`/`ErrorQPTop`, `QPCurUp`/`QPCursorUp`, `McBottom`/`MvBottom`, `MoveTopDoc`/`MoveToTop`.
