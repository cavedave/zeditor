import ZEditor.Spec.Doc7

/-!
# Doc8: search and replace (Part Three, §7)

Printed pp.107–115 (PDF pp.110–118). A search buffer and a replace buffer are
added. Searches move the cursor to the next (or previous) match of the search
buffer; Replace replaces the match at the cursor with the replace buffer.

Grouping. The book writes, for example,
```
DownSearch_Doc8 ≙ FlagPrevCursor ;
                      SuccDownSearch ; RemTrailWS ; RemTrailNL ∧
                      PromoteSearchUnMark ∧ Success
                  ∨ UnSuccDownSearch ∧ PromoteSearchLeaveMark ∧ RepStringNotFound
                  ∨ ErrorSBuffEmpty
```
By the usual Z precedence (`∧` binds tighter than `∨`, which binds tighter than
`;`) this would compose the error cases after the search, which cannot be meant.
We follow the layout, as the book's own convention (Part 2) asks: each
disjunct is one line group, and the promotion schema constrains the whole of
its disjunct.
-/

namespace ZEditor

/-! ## §7.1 The Doc8 state -/

/-- `Doc8 ≙ Doc7 ∧ SearchBuffer ∧ ReplaceBuffer` -/
structure Doc8 extends Doc7 where
  sBuff : List Char
  rBuff : List Char

/-- `Initialize_Doc8 ≙ [ Initialize_Doc7 ∧ ΔDoc8 | SBuff′ = RBuff′ = ⟨⟩ ]` -/
def Initialize_Doc8 (filename : List Char) (d' : Doc8) : Prop :=
  Initialize_Doc7 filename d'.toDoc7 ∧ d'.sBuff = [] ∧ d'.rBuff = []

/-! ## §7.2 Regular expressions -/

/-- The book's loose definitions, as parameters:
* `RegExpression : ℙ (seq Char)`;
* `_ regexpmatches _`, constrained by `e regexpmatches s ⇒ # e ≥ s`, which does
  not type-check (a number compared with a sequence), so we leave it free;
* `matchedlength : seq Char × seq Char ⇸ ℕ`, of which only the domain is
  specified (`dom = matches`); its values are unconstrained, so the length of
  text a Replace removes is left completely open. -/
structure RegExps where
  isRegExp : List Char → Prop
  regexpmatches : List Char → List Char → Prop
  matchedlength : List Char → List Char → Nat

variable (R : RegExps)

/-- ```
∀ e : RegExpression ; s1, s2 ∈ seq Char | s1 ∉ RegExpression •
    e matches s2 ⇔ e regexpmatches s
    s1 matches s2 ⇔ s1 prefix s2
```
(`s` for `s2`.) A plain string matches a sequence that it prefixes. -/
def «matches» (s1 s2 : List Char) : Prop :=
  (R.isRegExp s1 → R.regexpmatches s1 s2) ∧ (¬ R.isRegExp s1 → s1 <+: s2)

/-- `∃ S in X • P S`: some contiguous segment of `X` satisfies `P`. -/
def segIn (X : List Char) (P : List Char → Prop) : Prop :=
  ∃ u S v, u ++ S ++ v = X ∧ P S

/-- `n .. m ↿ X`: the elements of `X` at positions `n` to `m` (from 1). -/
def extract (n m : Nat) (X : List Char) : List Char := (X.drop (n - 1)).take (m + 1 - n)

/-! ## §7.3–7.4 Search -/

/-- `CopyQBuffSBuff` / `CopyQBuffRBuff`: in the quote buffer, the buffer's text
becomes the search (replace) buffer and the state returns to the document.
The search operations are given here with the search text `sb` they use, so
the `_Doc` form uses `SBuff` and the `_Quote` form uses `QBuff`. -/
def searchText (d : Doc8) : List Char := if d.state = .doc then d.sBuff else d.qBuff

/-- The search buffer after a search: unchanged in the document, `QBuff` from
the quote buffer. -/
def SearchStep (d d' : Doc8) : Prop :=
  d'.sBuff = searchText d ∧ d'.state = .doc

/-- `SuccDownSch_Doc` (and, through `searchText`, `SuccDownSch_Quote ≙
CopyQBuffSBuff ; SuccDownSch_Doc`):
```
SearchOp ; State = State_Doc ; # Right_Char ≥ # SBuff ; SBuff matches Right_Char′
¬(∃ S in n .. m ↿ (Left_Char ⁀ Right_Char) • SBuff matches S)
where n, m = (# Left_Char + 2), (# Left_Char′ + matchedlength (SBuff, Right_Char′) − 1)
```
with `SearchOp ≙ [ Ξ_Cont Doc1 ; ΞSearchBuffer ; ΔDocState | SBuff ≠ ⟨⟩ ; State′ = State_Doc ]`. -/
def SuccDownSch (sb l r l' r' : List Char) : Prop :=
  l ++ r = l' ++ r' ∧ sb ≠ [] ∧ r.length ≥ sb.length ∧ «matches» R sb r' ∧
  ¬ segIn (extract (l.length + 2) (l'.length + R.matchedlength sb r' - 1) (l ++ r)) («matches» R sb)

/-- `SuccUpSch_Doc`: as above with `# Left_Char ≥ # SBuff` and
`n, m = (# Left_Char′ + 2), (# Left_Char + matchedlength (SBuff, Right_Char′) − 1)`. -/
def SuccUpSch (sb l r l' r' : List Char) : Prop :=
  l ++ r = l' ++ r' ∧ sb ≠ [] ∧ l.length ≥ sb.length ∧ «matches» R sb r' ∧
  ¬ segIn (extract (l'.length + 2) (l.length + R.matchedlength sb r' - 1) (l ++ r)) («matches» R sb)

/-- `UnSuccDownSch_Doc`: `ΞDoc1`, `SBuff ≠ ⟨⟩`, `¬(∃ S in (tail Right_Char) • SBuff matches S)`. -/
def UnSuccDownSch (sb l r l' r' : List Char) : Prop :=
  l' = l ∧ r' = r ∧ sb ≠ [] ∧ ¬ segIn r.tail («matches» R sb)

/-- `UnSuccUpSch_Doc`: `¬(∃ S in (front Left_Char) • SBuff matches S)`. -/
def UnSuccUpSch (sb l r l' r' : List Char) : Prop :=
  l' = l ∧ r' = r ∧ sb ≠ [] ∧ ¬ segIn l.dropLast («matches» R sb)

/-- `ErrorSBuffEmpty ≙ ErrorSBuffEmpty_Doc ∨ ErrorSBuffEmpty_Quote`: the search
text is empty; nothing changes except, from the quote buffer, the state and the
(now empty) search buffer. -/
def ErrorSBuffEmpty (d d' : Doc8) (rep : Report) : Prop :=
  searchText d = [] ∧ rep = "Search buffer empty" ∧
  (if d.state = .doc then d' = d
   else d'.toDoc6 = d.toDoc6 ∧ d'.sBuff = [] ∧ d'.state = .doc ∧ d'.rBuff = d.rBuff ∧
     d'.toQuoteBuffer = d.toQuoteBuffer ∧ d'.name = d.name)

/-- ```
┌─ PromoteSearch ───────────────
│ ΔDoc8 ; Ξ_Cont Doc1 ; ΔMarkedText ; ΞPasteBuffer
│ ΞQuoteBuffer ; ΞDocName ; ΞReplaceBuffer
└───────────────────────────────
```
Checked against the scan: `Ξ_Cont Doc1` is there, although the prose says that
a search may change the content by removing whitespace. -/
def PromoteSearch (d d' : Doc8) : Prop :=
  d.leftChar ++ d.rightChar = d'.leftChar ++ d'.rightChar ∧ d'.pBuff = d.pBuff ∧
  d'.toQuoteBuffer = d.toQuoteBuffer ∧ d'.name = d.name ∧ d'.rBuff = d.rBuff

/-- `PromoteSearchUnMark ≙ [ PromoteSearch | MarkSeq = MarkedSeq′ = ⟨⟩ ]`.
Checked against the scan: `MarkSeq` has no prime, so this requires that the
mark sequence be empty *before* the search. -/
def PromoteSearchUnMark (d d' : Doc8) : Prop :=
  PromoteSearch d d' ∧ d.markSeq = [] ∧ d'.markedSeq = []

def PromoteSearchLeaveMark (d d' : Doc8) : Prop :=
  PromoteSearch d d' ∧ d'.markSeq = d.markSeq ∧ d'.markedSeq = d.markedSeq

/-- A search operation as a whole: the successful search (on the characters),
then `RemTrailWS ; RemTrailNL`, under `PromoteSearchUnMark`; or the
unsuccessful one; or the empty-buffer error. -/
def SearchOp8 (succ unsucc : List Char → List Char → List Char → List Char → List Char → Prop)
    (d d' : Doc8) (rep : Report) : Prop :=
  (∃ (m : Doc8) (m₂ : Doc2), succ (searchText d) d.leftChar d.rightChar m.leftChar m.rightChar ∧
      SearchStep d m ∧ RemTrailWS (FlagPrevCursor d.toDoc2) m.toDoc2 m₂ ∧
      RemTrailNL m₂ d'.toDoc2 ∧ SearchStep d d' ∧ PromoteSearchUnMark d d' ∧ rep = "OK") ∨
  (unsucc (searchText d) d.leftChar d.rightChar d'.leftChar d'.rightChar ∧ SearchStep d d' ∧
      PromoteSearchLeaveMark d d' ∧ rep = "String not found") ∨
  ErrorSBuffEmpty d d' rep

def DownSearch_Doc8 : Doc8 → Doc8 → Report → Prop := SearchOp8 (SuccDownSch R) (UnSuccDownSch R)
def UpSearch_Doc8 : Doc8 → Doc8 → Report → Prop := SearchOp8 (SuccUpSch R) (UnSuccUpSch R)

/-! ## §7.5 Replace -/

/-- `SuccRpl_Doc ≙ RemMatchedText ; InsRBuffText` on the characters: the text
matched by the search buffer is removed (`matchedlength` characters of it) and
the replace buffer is put in its place. -/
def SuccRpl (sb rb l r l' r' : List Char) : Prop :=
  «matches» R sb r ∧ l' = l ∧ r' = rb ++ r.drop (R.matchedlength sb r)

/-- The replace buffer after a Replace: unchanged in the document, `QBuff` from
the quote buffer (`CopyQBuffRBuff ≙ CopyQBuffSBuff[ReplaceBuffer \ SearchBuffer]`,
a renaming written with schema names where variable names are needed). -/
def replaceText (d : Doc8) : List Char := if d.state = .doc then d.rBuff else d.qBuff

def ReplaceStep (d d' : Doc8) : Prop := d'.rBuff = replaceText d ∧ d'.state = .doc

/-- ```
┌─ PromoteReplace ──────────────
│ ΔDoc8 ; Ξ_Cont Doc1 ; ΔMarkedText ; ΞPasteBuffer
│ ΞQuoteBuffer ; ΞDocName ; ΞSearchBuffer
└───────────────────────────────
```
Checked against the scan: `Ξ_Cont Doc1` is there. The prose says "only the
replace buffer, document state and document content may change". -/
def PromoteReplace (d d' : Doc8) : Prop :=
  d.leftChar ++ d.rightChar = d'.leftChar ++ d'.rightChar ∧ d'.pBuff = d.pBuff ∧
  d'.toQuoteBuffer = d.toQuoteBuffer ∧ d'.name = d.name ∧ d'.sBuff = d.sBuff

/-- `PromoteReplaceUnMark ≙ [ PromoteReplace | MarkSeq = MarkedSeq′ = ⟨⟩ ]` -/
def PromoteReplaceUnMark (d d' : Doc8) : Prop :=
  PromoteReplace d d' ∧ d.markSeq = [] ∧ d'.markedSeq = []

def PromoteReplaceLeaveMark (d d' : Doc8) : Prop :=
  PromoteReplace d d' ∧ d'.markSeq = d.markSeq ∧ d'.markedSeq = d.markedSeq

/-- `ErrorReplaceFull ≙ ErrorReplaceFull_Doc ∨ ErrorReplaceFull_Quote` (its
`rep!` is not declared). -/
def ErrorReplaceFull (d d' : Doc8) (rep : Report) : Prop :=
  rep = "Editor full" ∧
  (if d.state = .doc then d' = d
   else d'.toDoc6 = d.toDoc6 ∧ d'.rBuff = d.qBuff ∧ d'.state = .doc ∧ d'.sBuff = d.sBuff ∧
     d'.toQuoteBuffer = d.toQuoteBuffer ∧ d'.name = d.name)

/-- ```
Replace_Doc8 ≙ FlagPrevCursor ; SuccReplace ; RemTrailWS ; RemTrailNL ∧
                   PromoteReplaceUnMark ∧ Success
             ∨ UnSuccReplace ∧ PromoteReplaceLeaveMark ∧ RepNoMatchSBuff
             ∨ ErrorReplaceFull
``` -/
def Replace_Doc8 (d d' : Doc8) (rep : Report) : Prop :=
  (∃ (m : Doc8) (m₂ : Doc2),
      SuccRpl R d.sBuff (replaceText d) d.leftChar d.rightChar m.leftChar m.rightChar ∧
      ReplaceStep d m ∧ RemTrailWS (FlagPrevCursor d.toDoc2) m.toDoc2 m₂ ∧
      RemTrailNL m₂ d'.toDoc2 ∧ ReplaceStep d d' ∧ PromoteReplaceUnMark d d' ∧ rep = "OK") ∨
  (¬ «matches» R d.sBuff d.rightChar ∧ d'.leftChar = d.leftChar ∧ d'.rightChar = d.rightChar ∧
      ReplaceStep d d' ∧ PromoteReplaceLeaveMark d d' ∧ rep = "No match with search buffer") ∨
  ErrorReplaceFull d d' rep

/-! ## §7.6 Promotion of the Doc7 operations -/

/-- `∀ OP : EditOps4 • OP_Doc8 ≙ OP_Doc7 ∧ ΞSearchBuffer ∧ ΞReplaceBuffer` -/
def promote8 (op7 : Doc7 → Doc7 → Report → Prop) (d d' : Doc8) (rep : Report) : Prop :=
  op7 d.toDoc7 d'.toDoc7 rep ∧ d'.sBuff = d.sBuff ∧ d'.rBuff = d.rBuff

/-! ## Findings -/

/-- **A successful Replace leaves the document exactly as it was.**
`PromoteReplace` contains `Ξ_Cont Doc1`. So the "OK" outcome of Replace can
only arise when the replacement, after tidying, gives back the original text;
in general Replace at a match can only answer "Editor full". -/
theorem replace_ok_unchanged {d d' : Doc8} {rep : Report} (h : Replace_Doc8 R d d' rep)
    (hok : rep = "OK") : d'.leftChar ++ d'.rightChar = d.leftChar ++ d.rightChar := by
  rcases h with ⟨m, m₂, -, -, -, -, -, hp, -⟩ | h | ⟨h, -⟩
  · exact hp.1.1.symm
  · rw [hok] at h; simp at h
  · rw [hok] at h; simp at h

/-- **Searching while a mark is set has no outcome when the text is found.**
`PromoteSearchUnMark` requires `MarkSeq = ⟨⟩` before the search; the "not found"
case needs the text to be absent; the empty-buffer error needs an empty buffer. -/
theorem downSearch_marked_stuck {d : Doc8} (hstate : d.state = .doc) (hs : d.sBuff ≠ [])
    (hm : d.markSeq ≠ []) (hfound : segIn d.rightChar.tail («matches» R d.sBuff)) :
    ¬ ∃ d' rep, DownSearch_Doc8 R d d' rep := by
  have ht : searchText d = d.sBuff := by simp [searchText, hstate]
  rintro ⟨d', rep, ⟨_, _, _, _, _, _, _, ⟨_, hm', _⟩, _⟩ | ⟨⟨_, _, _, hnf⟩, _⟩ | ⟨he, _⟩⟩
  · exact hm hm'
  · rw [ht] at hnf; exact hnf hfound
  · rw [ht] at he; exact hs he

/-- The same for Replace: at a match, with a mark set, only "Editor full". -/
theorem replace_marked_full {d d' : Doc8} {rep : Report} (hm : d.markSeq ≠ [])
    (hmatch : «matches» R d.sBuff d.rightChar) (h : Replace_Doc8 R d d' rep) :
    rep = "Editor full" := by
  rcases h with ⟨_, _, _, _, _, _, _, ⟨_, hm', _⟩, _⟩ | ⟨hn, _⟩ | ⟨h, _⟩
  · exact absurd hm' hm
  · exact absurd hmatch hn
  · exact h

/-- **A down search may move the cursor up.** The rule that the match found be
the first one after the cursor is written as "no match in positions
`#Left_Char + 2 .. #Left_Char′ + matchedlength − 1`"; nothing requires the
cursor to move forward, and for an earlier match that range is empty. In
"a|xa", searching down for the plain text "a" may go back to "|axa". -/
theorem downSearch_may_go_up (hplain : ¬ R.isRegExp ['a'])
    (hml : R.matchedlength ['a'] ['a', 'x', 'a'] = 1) :
    SuccDownSch R ['a'] ['a'] ['x', 'a'] [] ['a', 'x', 'a'] := by
  refine ⟨rfl, by simp, by simp, ⟨fun h => absurd h hplain, fun _ => ⟨['x', 'a'], rfl⟩⟩, ?_⟩
  rw [hml]
  rintro ⟨u, S, v, huv, hS⟩
  simp [extract] at huv
  obtain ⟨-, rfl, -⟩ := huv
  exact absurd (List.prefix_nil.mp (hS.2 hplain)) (by simp)

/-- **Search fails from a line ending in a space.** In a Doc3 state, a move that
keeps the content (as `PromoteSearch` requires) and puts the cursor on another
line leaves the old cursor line as an ordinary line, so it must be visible.
After typing a space at the end of a line, any search that finds its text on
another line therefore has no outcome (the tidying that would remove the space
is a change of content). -/
theorem xiCont_other_line_visible {d d' : Doc3}
    (hc : d.leftChar ++ d.rightChar = d'.leftChar ++ d'.rightChar)
    (hy : d'.udCurY ≠ d.udCurY) : visible d.udCurLine := by
  have hl : d'.udLines = d.udLines := by rw [d'.udLines_eq, d.udLines_eq, hc]
  have hy1 := d.udCurY_pos
  have hy2 := d.udCurY_le
  have hi : d.udCurY - 1 < d'.udLines.length := by rw [hl]; omega
  have := d'.lines_visible (d.udCurY - 1) hi (by omega)
  have hcur : d'.udLines[d.udCurY - 1] = d.udCurLine := by
    have := d.udCurLine_eq
    simp only [hl]
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  rwa [hcur] at this

end ZEditor
