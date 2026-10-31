# Pages to photograph from a physical copy

The only digital copy of the monograph (`source/Zeditor.pdf`, SHA-256 `5c00b1450a147cddf8248f11cb5d12de1f68fc40ff3fcfee46ffbc48499608e3`) is a 1-bit black-and-white scan at 199 ppi. Some of the marks that matter most in Z are at the limit of what that scan can show: a prime `′` (meaning "after"), a negation `¬`, a small subscript. A photograph of a physical copy is independent of the scan and can settle these doubts.

**The book.** D. S. Neilson, *From Z to C: Illustration of a Rigorous Development Method*, Technical Monograph PRG-101, Oxford University Computing Laboratory, Programming Research Group, Hilary 1990. ISBN 0-902928-78-3. Please check first that the library holds a copy, and note its library and shelfmark.

**Finding the pages.** Use the **printed page** number, the number printed on the page itself. The schemas are boxes with their name at the top left (for example `SysRead`), so on each page look for the named box.

**How to photograph.** Even light, the phone held parallel to the page. Take two photos of each page: the whole page, and a close-up of the line in question, filling the frame. Name them by printed page, for example `p095.jpg` and `p095-close.jpg`.

**Tick each one off** in the ✓ column as you go.

## A. Essential: 14 pages

Each of these pages carries a problem found in the specification (`FINDINGS.md`) that depends on one small mark or line. Ranked with the most fragile marks first: a missing prime or a `¬` is a few pixels in the scan, whereas a whole word is easy to read.

| ✓ | Rank | Printed page | Where on the page | What to look at | Why it matters |
|---|---|---|---|---|---|
| ☐ | 1 | **95** | bottom, the box `SysRead` | Its last line begins **`¬ NoReadError! ⇒`**. Is the `¬` there? | Finding 7d: with the `¬`, a successful file read may return any text |
| ☐ | 2 | **98** | middle, the line `QuoteRequestContentChange ≙ [ QuoteRequest \| MarkSeq′ = MarkedSeq = < > ]` | Which name has the prime `′`: `MarkSeq` (first), `MarkedSeq` (second), or both? | Finding 7c: if only `MarkSeq′`, Input is impossible while text is marked |
| ☐ | 3 | **111** | upper half, the box `PromoteSearch` and the line `PromoteSearchUnMark` below it | In the line, is there a prime on the first name, **`MarkSeq`**? In the box, is the second line **`Ξ`**`Cont Doc1` (Ξ, not Δ)? | Findings 8b, 8c: searching fails while a mark is set, or after a trailing space |
| ☐ | 4 | **114** | middle, the box `PromoteReplace` and the line `PromoteReplaceUnMark` below it | The same two questions as rank 3 | Finding 8a: Replace can never replace |
| ☐ | 5 | **89** | middle, the box `RemMText` | Third predicate line, before the `⇒`: does it end **`Left`**`Char` or `Right`Char? | Findings 6b, 6c: Cut may rewrite the whole document, or have no result |
| ☐ | 6 | **90** | top, the box `Pst` | Last line: **`MarkedSeq′ = < >`** (empty)? | Finding 6a: Paste can only answer "Editor full" |
| ☐ | 7 | **109** | lower half, the box `SuccDownSch_Doc`, its `where` line | `n, m = (# Left_Char + 2), (# Left_Char′ + matchedlength (SBuff, Right_Char′) − 1)`: are the primes on the second `Left` and on `Right` there? Also the small hooked symbol between `n .. m` and `(Left ⁀ Right)` two lines above | Finding 8d: a down search may move up |
| ☐ | 8 | **56** | top, the box `DocWordSeq` | Last two lines: is the symbol after `rng (w1)` a plain **`=`** or a subset sign `⊆`? Also, the line above them declares `w1, w2 : Word` twice: are the second pair the same letters? | Finding 2 (decision D2) |
| ☐ | 9 | **101** | bottom, the box `RequestQuit` | Two lines starting `WriteSeq! =`: one `= MarkedSeq`, one `= Left ⁀ Right`? | Finding 7a: Quit is impossible |
| ☐ | 10 | **85** | top, the box `PadWSNL` | Third line: `UDLines QPCurY` **`visible_prefix`** `UDCurLine′` (not plain `prefix`) | Finding 5: → after typing a space answers "Editor full" |
| ☐ | 11 | **105** | middle, the definition `Quote_StateQuote ≙ …` | Exactly eight names joined by `∨`, and **no** `MoveLineNumber`? | Finding 7b: Move-to-line can never run |
| ☐ | 12 | **55** | lower half, the two definitions `Word ≙ …` and `Line ≙ …` | `Line ≙ seq (Char − {nl})`: `seq`, not `seq₁`? | Finding 1 (decision D1) |
| ☐ | 13 | **57** | upper half, the character sequence `< t, h, e, nl, c, a, n, a, r, y, nl, nl, a, t, e >` and the line sequence below it | Are `< nl >` shown as separate lines in the line sequence? | Decision D1 (context) |
| ☐ | 14 | **v** (Appendix C) | upper half, the C function `RemTrailWS`, the line starting `if (OPType` | Is the first comparison **`OPType=LeftMove`** (one `=`) or `OPType==LeftMove` (two)? The other three on the line have two | Bug #605: with one `=`, the C as printed could not keep a mark through a cursor move |

## B. Useful: readings that could change the meaning

Doubts found while transcribing, where a different reading would change what the specification says (not just a spelling). The ID is the row in `docs/corrections.csv`. The positions on the page in this table are approximate: look for the named box or line.

| ✓ | Printed page | Where on the page | What to look at | ID |
|---|---|---|---|---|
| ☐ | **76** | lower half, the box defining `_ after _` | The symbol in `(1 .. N ⩤ S)`: domain *anti*-restriction `⩤` (a triangle with a bar) or plain restriction `◁`? With `◁`, "after" would mean "the first N" instead of "all but the first N" | 209 |
| ☐ | **98** | middle, the line `QuoteRequestNoChange ≙ QuoteRequest ∧ ΞDoc5` | Is the number after `Doc` a **5** (not 6 or 7)? | 405 |
| ☐ | **112** | upper half, the box `SuccUpSch_Doc` | The same hooked symbol as rank 7, between `n .. m` and `(Left ⁀ Right)` | 504 |
| ☐ | **108** | middle, the boxes `regexpmatches` and `matches` | `# e ≥ s` (is there a `#` before `s`?); and in `matches`, does the first line end `regexpmatches s` or `s2`? | 416, 417 |
| ☐ | **73** | middle, the box `Doc2`, third predicate | `UDCurY = #(FDL⁻¹ Left_Char)`: a plain `=` or a wavy one? | 206 |
| ☐ | **81** | top, the box `ErrorAtTopPage` | Declaration `y : ℕ`: is there a small subscript `1` (`ℕ₁`)? | 305 |
| ☐ | **88** | middle, the three lines `∀ OP : … • OP_Doc5 ≙ OP_Doc4 …` | Are the subscript numbers **5** and **4** in each line? | 309, 311 |
| ☐ | **113** | lower half, the line `CopyQBuffRBuff ≙ CopyQBuffSBuff[ReplaceBuffer \ SearchBuffer]` | Is the separator a backslash `\` or a slash `/`? | 507 |
| ☐ | **78** | bottom, the last paragraph of §3.3 | "the cursor line after `UDCurY − 1`": `UDCurY` or `UDCurX`? | 304 |

## C. Nice to have

- **The rest of Part Three** (printed pages 45–123): about 40 other small doubts, such as a blurred letter in a name or a number in a proof. They are listed in `docs/corrections.csv` (IDs 101–512). None changes the meaning.
- **Appendix C, the C code** (printed pages i–xlv): 127 doubts, almost all where the typewriter font makes letters look alike (h and b, O and D, w and v, `=` and `==`). Photographing all 45 pages would settle every one at once. IDs 601–831 in `docs/corrections.csv`.

Parts One and Two (printed pages 1–44) need no photographs.
