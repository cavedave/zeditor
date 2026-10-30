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
| 1 | 1.2 | `Line ≙ seq (Char − {nl})` excludes the newline lines the book's own examples use; line views then don't exist (or aren't unique) | ill-formed | `printed_lines_have_no_nl`, `printed_lines_not_unique` | n/a | `seq₁ (Char − {nl}) ∪ {⟨nl⟩}` | open |
| 2 | 1.2 | `DocWordSeq` uses `rng w = S` where `⊆` is meant; word views not unique | ill-formed | (comment in `DocWordSeq`) | n/a | `⊆` | open |
| 3 | 1.6 | Word and line moves are not total: inside a word or line there is no outcome at all | stuck | `leftMoveWord_Doc1_stuck` | moves (`LeftMoveWord_Doc1`) | C reading (`MvWordC`, `MvLineC`), content kept as characters | open |
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

## Readings to confirm by eye

**All 11 confirmed by eye on 2026-10-30.** Every finding that rests on a single symbol has now been checked independently against the scan; none was a misreading.

These findings rest on one symbol or line in the scan. Each was checked from page images at 160–200 dpi; an independent check against the printed page is worthwhile before any decision. Page numbers are PDF pages of `source/Zeditor.pdf` (printed page in brackets).

The scan is 1-bit black-and-white at 199 ppi, so nothing finer than that can be recovered from it. The checklist pages are extracted at exactly the native resolution, with no resampling, in `docs/eyecheck/` (named by page and finding). Only a physical copy or an independent scan could do better. No other copy has been found (searched 2026-10-30); the scan's SHA-256 is `5c00b1450a147cddf8248f11cb5d12de1f68fc40ff3fcfee46ffbc48499608e3`, so any copy with that checksum is this same scan.

| ✓ | Finding | What to look at | Page |
|---|---|---|---|
| ✓ | 1 | `Line ≙ seq (Char − {nl})`, not `seq₁`, and no `∪ {⟨nl⟩}` (confirmed by eye 2026-10-30) | 58 (55) |
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
