/-!
# Doc1: the document model (Part Three, §1)

Neilson, *From Z to C*, Oxford PRG-101 (1990), printed pp.54–68 (PDF pp.57–71).
Source text: `docs/zeditor-spec-core.md`, section 1.

How the Z is translated:
* A state schema becomes a `structure`; its predicate becomes proof fields.
* An operation schema on `ΔDoc1` becomes a relation `Doc1 → Doc1 → Prop`
  (before-state, after-state). The invariant of both states is built into `Doc1`.
* Inputs `x?` and outputs `rep!` become extra arguments.
* `S ; T` (schema composition) is relational composition `⨾`.
* Z sequences are `List`; `front` is `dropLast`, `⁀/` is `flatten`.

Where the printed spec cannot be taken literally, the definition says so and gives
the reading used. The theorems at the end show why these readings are forced.
-/

namespace ZEditor

/-! ## §1.1 The generic document -/

/-- `Pair[X] ≙ [ Left, Right : X ]` -/
structure Pair (X : Type) where
  left  : X
  right : X

/-- `Ξ_Cont Pair[X] ≙ [ ΔPair[X] | Left ⁀ Right = Left′ ⁀ Right′ ]` -/
def XiCont (p p' : Pair (List α)) : Prop :=
  p.left ++ p.right = p'.left ++ p'.right

/-- `Mv[X]`: content unchanged, `Left ≠ ⟨⟩`, `Left′ = front Left`. -/
def Mv (p p' : Pair (List α)) : Prop :=
  XiCont p p' ∧ p.left ≠ [] ∧ p'.left = p.left.dropLast

/-- `Del[X]`: `Left ≠ ⟨⟩`, `Left′ = front Left`, `Right′ = Right`. -/
def Del (p p' : Pair (List α)) : Prop :=
  p.left ≠ [] ∧ p'.left = p.left.dropLast ∧ p'.right = p.right

/-- `MvBot[X]`: content unchanged, `Right ≠ ⟨⟩`, `Right′ = ⟨⟩`. -/
def MvBot (p p' : Pair (List α)) : Prop :=
  XiCont p p' ∧ p.right ≠ [] ∧ p'.right = []

/-! ## §1.2 The character, word and line views -/

/-- `sp, nl : Char | sp ≠ nl` (and `tab`, used by the insert operation). -/
def sp  : Char := ' '
def nl  : Char := '\n'
def tab : Char := '\t'

/-- `WhiteSpace ≙ {sp}` -/
abbrev WhiteSpace (c : Char) : Prop := c = sp

/-- `NonWhiteSpace ≙ Char − {sp, nl}` -/
abbrev NonWhiteSpace (c : Char) : Prop := c ≠ sp ∧ c ≠ nl

/-- `Word ≙ seq₁ WhiteSpace ∪ seq₁ NonWhiteSpace ∪ ⟨nl⟩`
(the last part read as the set `{⟨nl⟩}`). -/
abbrev IsWord (w : List Char) : Prop :=
  (w ≠ [] ∧ ∀ c ∈ w, WhiteSpace c) ∨
  (w ≠ [] ∧ ∀ c ∈ w, NonWhiteSpace c) ∨
  w = [nl]

/-- Printed: `Line ≙ seq (Char − {nl})`.

That cannot be meant literally: the book's own line views contain `⟨nl⟩`
elements (printed p.57) and `DocLineSeq` tests `l1 ≠ ⟨nl⟩`. With the printed
definition no document containing a newline has a line view
(`printed_lines_have_no_nl`), and the line view is not unique
(`printed_lines_not_unique`). We use the reading the examples need:
`seq₁ (Char − {nl}) ∪ {⟨nl⟩}`. This is decision D1 in `FINDINGS.md`. -/
abbrev IsLine (l : List Char) : Prop :=
  (l ≠ [] ∧ nl ∉ l) ∨ l = [nl]

/-- The pairs `⟨a, b⟩` with `⟨a, b⟩ infix S`, i.e. the adjacent pairs of `S`. -/
def adjacent (S : List α) : List (α × α) := S.zip S.tail

/-- `DocWordSeq`: no two whitespace words and no two non-whitespace words adjacent.

Printed: `rng (w1) = WhiteSpace ⇒ rng (w2) ≠ WhiteSpace` and likewise for
`NonWhiteSpace`. With `=` the second clause never applies (no finite word uses
every non-space character), so `⟨⟨c,a⟩,⟨t⟩⟩` would be allowed and the word view
would not be unique, contrary to the prose and Corollary 3:1.2a. We read
`ran w = S` as "w is drawn from S" (`ran w ⊆ S`). This is decision D2 in
`FINDINGS.md`. -/
abbrev DocWordSeq (W : List (List Char)) : Prop :=
  (∀ w ∈ W, IsWord w) ∧
  ∀ p ∈ adjacent W,
    ((∀ c ∈ p.1, WhiteSpace c) → ¬ ∀ c ∈ p.2, WhiteSpace c) ∧
    ((∀ c ∈ p.1, NonWhiteSpace c) → ¬ ∀ c ∈ p.2, NonWhiteSpace c)

/-- `DocLineSeq`: a non-newline line is always followed by a newline line. -/
abbrev DocLineSeq (L : List (List Char)) : Prop :=
  (∀ l ∈ L, IsLine l) ∧
  ∀ p ∈ adjacent L, p.1 ≠ [nl] → p.2 = [nl]

/-- `FW : DocWordSeq ⤖ seq Char`, `FW W = ⁀/ W` -/
def FW (W : List (List Char)) : List Char := W.flatten

/-- `FL : DocLineSeq ⤖ seq Char`, `FL L = ⁀/ L` -/
def FL (L : List (List Char)) : List Char := L.flatten

/-! ## §1.3 The Doc1 state -/

/-- ```
┌─ Doc1 ─────────────────────────────
│ Pair_Char
│ Pair_Word
│ Pair_Line
├────────────────────────────────────
│ Left_Char = FW Left_Word = FL Left_Line
│ Right_Char = FW Right_Word = FL Right_Line
└────────────────────────────────────
```
`Right` is held in reading order: its head is the character after the cursor. -/
structure Doc1 where
  leftChar  : List Char
  rightChar : List Char
  leftWord  : List (List Char)
  rightWord : List (List Char)
  leftLine  : List (List Char)
  rightLine : List (List Char)
  leftWord_ok  : DocWordSeq leftWord
  rightWord_ok : DocWordSeq rightWord
  leftLine_ok  : DocLineSeq leftLine
  rightLine_ok : DocLineSeq rightLine
  left_inv  : leftChar = FW leftWord ∧ FW leftWord = FL leftLine
  right_inv : rightChar = FW rightWord ∧ FW rightWord = FL rightLine

/-- `Pair_Char`, `Pair_Word`, `Pair_Line`: the three views as pairs. -/
def Doc1.chars (d : Doc1) : Pair (List Char) := ⟨d.leftChar, d.rightChar⟩
def Doc1.words (d : Doc1) : Pair (List (List Char)) := ⟨d.leftWord, d.rightWord⟩
def Doc1.lines (d : Doc1) : Pair (List (List Char)) := ⟨d.leftLine, d.rightLine⟩

/-- An operation on `ΔDoc1`, without input or output. -/
abbrev Op := Doc1 → Doc1 → Prop

/-- Schema composition `S ; T`. -/
def seqOp (S T : Op) : Op := fun d d'' => ∃ d', S d d' ∧ T d' d''

infixl:60 " ⨾ " => seqOp

/-- `Ξ_Cont Doc1 ≙ Ξ_Cont Pair[Char] ∧ ΔDoc1` -/
def XiContDoc1 : Op := fun d d' => XiCont d.chars d'.chars

/-- `Initialize_Doc1 ≙ [ ΔDoc1 | Left_Char′ = Right_Char′ = ⟨⟩ ]` (a condition on
the after-state only). -/
def Initialize_Doc1 (d' : Doc1) : Prop := d'.leftChar = [] ∧ d'.rightChar = []

/-- `MvChar ≙ Mv_Char ∧ ΔDoc1`, etc. -/
def MvChar  : Op := fun d d' => Mv d.chars d'.chars
def MvWord  : Op := fun d d' => Mv d.words d'.words
def MvLine  : Op := fun d d' => Mv d.lines d'.lines
def DelChar : Op := fun d d' => Del d.chars d'.chars
def DelWord : Op := fun d d' => Del d.words d'.words
def DelLine : Op := fun d d' => Del d.lines d'.lines

/-- `MvBottom ≙ MvBot_Char ∧ ΔDoc1` (printed "McBottom", [?202]). -/
def MvBottom : Op := fun d d' => MvBot d.chars d'.chars

/-! ### §1.3.1 The insert operation -/

/-- `InsNonTab`: `x? ≠ tab`, `Left_Char′ = Left_Char ⁀ ⟨x?⟩`, `Right_Char′ = Right_Char`. -/
def InsNonTab (x : Char) : Op := fun d d' =>
  x ≠ tab ∧ d'.leftChar = d.leftChar ++ [x] ∧ d'.rightChar = d.rightChar

/-- `InsTab`: `x? = tab`, `Left_Char prefix Left_Char′`,
`rng (Left_Char′ − Left_Char) = {sp}`, `Right_Char′ = Right_Char`.
A tab inserts one or more spaces; how many is left open. -/
def InsTab (x : Char) : Op := fun d d' =>
  x = tab ∧ d.leftChar <+: d'.leftChar ∧
  d'.leftChar.length > d.leftChar.length ∧
  (∀ c ∈ d'.leftChar.drop d.leftChar.length, c = sp) ∧
  d'.rightChar = d.rightChar

/-- `InsChar ≙ InsNonTab ∨ InsTab` -/
def InsChar (x : Char) : Op := fun d d' => InsNonTab x d d' ∨ InsTab x d d'

/-! ## §1.4 Introducing direction -/

/-- `Mirror`: `Left_Char′ = rev Right_Char`, `Right_Char′ = rev Left_Char`. -/
def Mirror : Op := fun d d' =>
  d'.leftChar = d.rightChar.reverse ∧ d'.rightChar = d.leftChar.reverse

/-- `Right OP ≙ Mirror ; OP ; Mirror` -/
def Right (op : Op) : Op := Mirror ⨾ op ⨾ Mirror
/-- `Left OP ≙ OP` -/
def Left (op : Op) : Op := op

def RightMvChar  := Right MvChar
def LeftMvChar   := Left MvChar
def RightMvWord  := Right MvWord
def LeftMvWord   := Left MvWord
def RightMvLine  := Right MvLine
def LeftMvLine   := Left MvLine

def RightDelChar := Right DelChar
def LeftDelChar  := Left DelChar
def RightDelWord := Right DelWord
def LeftDelWord  := Left DelWord
def RightDelLine := Right DelLine
def LeftDelLine  := Left DelLine

def MvToTop := Right MvBottom
def MvToBot := Left MvBottom

/-! ## §1.5 Error messages -/

/-- `Report`: the book's reports are strings. -/
abbrev Report := String

/-- `Success ≙ [ rep! : Report | rep! = "OK" ]` -/
def Success (rep : Report) : Prop := rep = "OK"

/-- `Doc1Unchanged ≙ [ ΞDoc1 ; rep! : Report ]` -/
def Doc1Unchanged (d d' : Doc1) : Prop := d' = d

def ErrorTopOfDoc (d d' : Doc1) (rep : Report) : Prop :=
  Doc1Unchanged d d' ∧ d.leftChar = [] ∧ rep = "At top of document"

def ErrorBotOfDoc (d d' : Doc1) (rep : Report) : Prop :=
  Doc1Unchanged d d' ∧ d.rightChar = [] ∧ rep = "At bottom of document"

/-- No precondition: the editor may always report "full". This is how the spec
leaves room for a bounded implementation (Part Two, ∞-refinement). -/
def ErrorFull (d d' : Doc1) (rep : Report) : Prop :=
  Doc1Unchanged d d' ∧ rep = "Editor full"

/-! ## §1.6 The total operations on the Doc1 state -/

/-- An operation with output `rep!`. -/
abbrev TotalOp := Doc1 → Doc1 → Report → Prop

/-- `(op ∧ Success) ∨ err` -/
def orError (op : Op) (err : Doc1 → Doc1 → Report → Prop) : TotalOp :=
  fun d d' rep => (op d d' ∧ Success rep) ∨ err d d' rep

def RightMoveChar_Doc1   := orError RightMvChar  ErrorBotOfDoc
def LeftMoveChar_Doc1    := orError LeftMvChar   ErrorTopOfDoc
def RightMoveWord_Doc1   := orError RightMvWord  ErrorBotOfDoc
def LeftMoveWord_Doc1    := orError LeftMvWord   ErrorTopOfDoc
def RightMoveLine_Doc1   := orError RightMvLine  ErrorBotOfDoc
def LeftMoveLine_Doc1    := orError LeftMvLine   ErrorTopOfDoc

def RightDeleteChar_Doc1 := orError RightDelChar ErrorBotOfDoc
def LeftDeleteChar_Doc1  := orError LeftDelChar  ErrorTopOfDoc
def RightDeleteWord_Doc1 := orError RightDelWord ErrorBotOfDoc
/-- Printed with "ErrorTopOfDoe" ([?203]). -/
def LeftDeleteWord_Doc1  := orError LeftDelWord  ErrorTopOfDoc
def RightDeleteLine_Doc1 := orError RightDelLine ErrorBotOfDoc
def LeftDeleteLine_Doc1  := orError LeftDelLine  ErrorTopOfDoc

def InsertChar_Doc1 (x : Char) := orError (InsChar x) ErrorFull

def MoveToTop_Doc1 := orError MvToTop ErrorTopOfDoc
def MoveToBot_Doc1 := orError MvToBot ErrorBotOfDoc

/-! ## Checks -/

/-- `Mirror ; Mirror ≙ ΞDoc1`, at the character level. (The full statement also
needs the word and line views to be unique, Corollaries 3:1.2a and 3:1.2c.) -/
theorem mirror_mirror_chars (h : (Mirror ⨾ Mirror) d d') : d'.chars = d.chars := by
  obtain ⟨m, ⟨h1, h2⟩, h3, h4⟩ := h
  simp [Doc1.chars, h3, h4, h1, h2]

/-- With the printed `Line ≙ seq (Char − {nl})`, a line view never contains a
newline, so a document such as "the⏎cat" has no line view at all. -/
theorem printed_lines_have_no_nl (L : List (List Char))
    (h : ∀ l ∈ L, nl ∉ l) : nl ∉ FL L := by
  simp only [FL, List.mem_flatten, not_exists, not_and]
  exact fun l hl => h l hl

/-- With the printed `Line`, the empty document has two line views, so `FL` is not
one-to-one (Corollary 3:1.2c fails). -/
theorem printed_lines_not_unique :
    let PrintedDocLineSeq := fun (L : List (List Char)) =>
      (∀ l ∈ L, nl ∉ l) ∧ ∀ p ∈ adjacent L, p.1 ≠ [nl] → p.2 = [nl]
    PrintedDocLineSeq [] ∧ PrintedDocLineSeq [[]] ∧
    FL [] = FL [[]] ∧ ([] : List (List Char)) ≠ [[]] := by
  decide

/-- The document "ca|t": the cursor is inside the word "cat". -/
def caT : Doc1 where
  leftChar  := ['c', 'a']
  rightChar := ['t']
  leftWord  := [['c', 'a']]
  rightWord := [['t']]
  leftLine  := [['c', 'a']]
  rightLine := [['t']]
  leftWord_ok  := by decide
  rightWord_ok := by decide
  leftLine_ok  := by decide
  rightLine_ok := by decide
  left_inv  := by decide
  right_inv := by decide

/-- **The printed "total" operation `LeftMoveWord_Doc1` has no outcome when the
cursor is inside a word.** `Mv_Word` keeps the *word* sequence `Left ⁀ Right`
unchanged, so moving "ca" to the right side would need the word sequence
`⟨⟨c,a⟩,⟨t⟩⟩`, which is not a `DocWordSeq`; and `ErrorTopOfDoc` does not apply
because the cursor is not at the top. The same holds for `MvLine` inside a line. -/
theorem leftMoveWord_Doc1_stuck : ¬ ∃ d' rep, LeftMoveWord_Doc1 caT d' rep := by
  rintro ⟨d', rep, ⟨⟨hcont, -, hleft⟩, -⟩ | ⟨-, hnil, -⟩⟩
  · simp only [XiCont, Doc1.words, caT] at hcont hleft
    rw [hleft] at hcont
    have hr : d'.rightWord = [['c', 'a'], ['t']] := by simpa using hcont.symm
    have hok := d'.rightWord_ok
    rw [hr] at hok
    exact absurd hok (by decide)
  · simp [caT] at hnil

/-! ### The reading the C code implements

The C function `LeftMoveWord_Doc1` (Appendix C, p.ii) always succeeds when the
cursor is not at the top: from "ca|t" it moves to "|cat". That is `Mv` on the
word view with the content kept unchanged at the *character* level, i.e. using
`Ξ_Cont Doc1` (which the book defines in §1.3 but does not use here). -/

/-- `MvWord` as the C implements it: `Mv` on the word view, but with the content
kept unchanged as characters (`Ξ_Cont Doc1`) rather than as words.

**Warning: this departs from the printed specification.** As printed (`MvWord`),
a word move inside a word has no outcome (`leftMoveWord_Doc1_stuck`), so the
specification does not say what should happen. This version follows the C
program in the same monograph. It is decision D3 in `FINDINGS.md`, where the
reasons are given. -/
def MvWordC : Op := fun d d' =>
  XiContDoc1 d d' ∧ d.leftWord ≠ [] ∧ d'.leftWord = d.leftWord.dropLast

/-- `MvLine` as the C implements it (`LeftMoveLine_Doc1`, Appendix C p.ii). -/
def MvLineC : Op := fun d d' =>
  XiContDoc1 d d' ∧ d.leftLine ≠ [] ∧ d'.leftLine = d.leftLine.dropLast

def RightMvWordC := Right MvWordC
def LeftMvWordC  := Left MvWordC
def RightMvLineC := Right MvLineC
def LeftMvLineC  := Left MvLineC

def RightMoveWordC_Doc1 := orError RightMvWordC ErrorBotOfDoc
def LeftMoveWordC_Doc1  := orError LeftMvWordC  ErrorTopOfDoc
def RightMoveLineC_Doc1 := orError RightMvLineC ErrorBotOfDoc
def LeftMoveLineC_Doc1  := orError LeftMvLineC  ErrorTopOfDoc

/-- The document "|cat". -/
def cat0 : Doc1 where
  leftChar  := []
  rightChar := ['c', 'a', 't']
  leftWord  := []
  rightWord := [['c', 'a', 't']]
  leftLine  := []
  rightLine := [['c', 'a', 't']]
  leftWord_ok  := by decide
  rightWord_ok := by decide
  leftLine_ok  := by decide
  rightLine_ok := by decide
  left_inv  := by decide
  right_inv := by decide

/-- With the C's reading, "ca|t" moves to "|cat", as the C code does. -/
theorem leftMvWordC_caT : LeftMvWordC caT cat0 := by
  simp only [LeftMvWordC, Left, MvWordC, XiContDoc1, XiCont, Doc1.chars, caT, cat0]
  decide

end ZEditor
