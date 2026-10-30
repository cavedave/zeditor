import ZEditor.Spec.Doc5

/-!
# Doc6: lift, cut and paste (Part Three, §5.2)

Printed pp.88–91 (PDF pp.91–94). A paste buffer is added; `Lift` copies the
marked text into it, `Cut` copies and removes it, `Paste` inserts the buffer at
the cursor and marks the pasted text.
-/

namespace ZEditor

/-- `PasteBuffer ≙ [ PBuff : seq Char ]`, `Doc6 ≙ Doc5 ∧ PasteBuffer` -/
structure Doc6 extends Doc5 where
  pBuff : List Char

/-- `Initialize_Doc6 ≙ [ Initialize_Doc5 ∧ ΔDoc6 | PBuff′ = ⟨⟩ ]` -/
def Initialize_Doc6 (d' : Doc6) : Prop := Initialize_Doc5 d'.toDoc5 ∧ d'.pBuff = []

theorem Initialize_Doc6_exists : ∃ d' : Doc6, Initialize_Doc6 d' := by
  obtain ⟨d, h⟩ := Initialize_Doc5_exists
  exact ⟨{ toDoc5 := d, pBuff := [] }, h, rfl⟩

/-- `ErrorNoTextMarked`: `ΞDoc6`, `MarkedSeq = ⟨⟩`. -/
def ErrorNoTextMarked (d d' : Doc6) (rep : Report) : Prop :=
  d' = d ∧ d.markedSeq = [] ∧ rep = "No text marked"

/-! ## Lift -/

/-- `CopyMTextPBuff`: `PBuff′ = MarkedSeq ≠ ⟨⟩`, and
`Lift_Doc6 ≙ CopyMTextPBuff ∧ ΞDoc5 ∧ ΔDoc6 ∧ Success ∨ ErrorNoTextMarked`. -/
def Lift_Doc6 (d d' : Doc6) (rep : Report) : Prop :=
  (d'.pBuff = d.markedSeq ∧ d.markedSeq ≠ [] ∧ d'.toDoc5 = d.toDoc5 ∧ Success rep) ∨
  ErrorNoTextMarked d d' rep

theorem Lift_Doc6_total (d : Doc6) : ∃ d' rep, Lift_Doc6 d d' rep := by
  by_cases h : d.markedSeq = []
  · exact ⟨d, _, .inr ⟨rfl, h, rfl⟩⟩
  · exact ⟨{ d with pBuff := d.markedSeq }, _, .inl ⟨rfl, h, rfl, rfl⟩⟩

/-! ## Cut -/

/-- ```
┌─ RemMText ───────────────────────────
│ ΔPair_Char
│ ΔMarkedText
├──────────────────────────────────────
│ MarkSeq′ = MarkedSeq′ = ⟨⟩
│ MarkSeq ⁀ MarkedSeq = Left_Char ⇒ Left_Char′ = MarkSeq
│                                   Right_Char′ = Right_Char
│ MarkedSeq ⁀ MarkSeq = Left_Char ⇒ Right_Char′ = MarkSeq
│                                   Left_Char′ = Left_Char
└──────────────────────────────────────
```
The second implication is printed with `Left_Char` in its premise (checked
against the scan, [?313]); `Right_Char` is meant. -/
def RemMText (l r ms md l' r' ms' md' : List Char) : Prop :=
  ms' = [] ∧ md' = [] ∧
  (ms ++ md = l → l' = ms ∧ r' = r) ∧
  (md ++ ms = l → r' = ms ∧ l' = l)

/-- `RemMText` as intended, and as the C (`RemMText`, Appendix C p.ix) does it. -/
def RemMTextC (l r ms md l' r' ms' md' : List Char) : Prop :=
  ms' = [] ∧ md' = [] ∧
  (ms ++ md = l → l' = ms ∧ r' = r) ∧
  (md ++ ms = r → r' = ms ∧ l' = l)

/-- ```
Cut_Doc6 ≙ FlagPrevCursor ; CopyMTextPBuff ; RemMText ;
               RemTrailWS ; RemTrailNL ∧ Success
           ∨ ErrorNoTextMarked
``` -/
def Cut_Doc6 (d d' : Doc6) (rep : Report) : Prop :=
  (∃ m₁ m₂ : Doc2, d.markedSeq ≠ [] ∧ d'.pBuff = d.markedSeq ∧
      RemMText d.leftChar d.rightChar d.markSeq d.markedSeq
        m₁.leftChar m₁.rightChar d'.markSeq d'.markedSeq ∧
      RemTrailWS (FlagPrevCursor d.toDoc2) m₁ m₂ ∧ RemTrailNL m₂ d'.toDoc2 ∧ Success rep) ∨
  ErrorNoTextMarked d d' rep

/-- **With the mark below the cursor, `RemMText` allows any document.** In "a|bc"
with the mark after "b", neither premise holds, so `Left_Char′` and
`Right_Char′` are unconstrained: Cut may replace the whole document. -/
theorem remMText_mark_below_unconstrained (l' r' : List Char) :
    RemMText ['a'] ['b', 'c'] ['c'] ['b'] l' r' [] [] := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro h <;> simp at h

/-- **When both premises hold, `RemMText` has no outcome.** In "aa|" with the
mark between the two a's, `MarkSeq ⁀ MarkedSeq` and `MarkedSeq ⁀ MarkSeq` both
equal `Left_Char`, and the two implications demand `Left_Char′ = ⟨a⟩` and
`Left_Char′ = ⟨a, a⟩`. -/
theorem remMText_both_premises (r l' r' ms' md' : List Char) :
    ¬ RemMText ['a', 'a'] r ['a'] ['a'] l' r' ms' md' := by
  rintro ⟨-, -, h1, h2⟩
  have e1 := (h1 rfl).1
  have e2 := (h2 rfl).2
  rw [e1] at e2; simp at e2

/-- **Cut can have no outcome at all.** From "aa|" with the mark between the two
a's, `RemMText` is impossible and `ErrorNoTextMarked` does not apply (text is
marked), so `Cut_Doc6` has no outcome, not even an error. The book calls
`RemMText` "a total operation". -/
theorem cut_no_outcome {d : Doc6} (hl : d.leftChar = ['a', 'a']) (hms : d.markSeq = ['a'])
    (hmd : d.markedSeq = ['a']) : ¬ ∃ d' rep, Cut_Doc6 d d' rep := by
  rintro ⟨d', rep, ⟨m₁, m₂, -, -, hrem, -⟩ | ⟨-, h, -⟩⟩
  · rw [hl, hms, hmd] at hrem
    exact remMText_both_premises _ _ _ _ _ hrem
  · rw [hmd] at h; simp at h

/-! ## Paste -/

/-- ```
┌─ Pst ────────────────────────────────
│ ΔPair_Char
│ ΔMarkedText
│ PasteBuffer
├──────────────────────────────────────
│ PBuff ≠ ⟨⟩
│ Left_Char′ = Left_Char ⁀ PBuff
│ Right_Char′ = Right_Char
│ MarkSeq′ = Left_Char
│ MarkedSeq′ = ⟨⟩
└──────────────────────────────────────
```
`ΔMarkedText` includes the `MarkedText` invariant on the after-state. -/
def Pst (pb l r l' r' ms' md' : List Char) : Prop :=
  pb ≠ [] ∧ l' = l ++ pb ∧ r' = r ∧ ms' = l ∧ md' = [] ∧ MarkedTextInv ms' md' l' r'

/-- **`Pst` contradicts the `MarkedText` invariant.** The prose says "the pasted
text becomes marked text": the mark goes at the old cursor position, so
`MarkedSeq′` should be `PBuff`. As printed, `MarkSeq′ ⁀ MarkedSeq′ = Left_Char`,
which is not `Left_Char′ = Left_Char ⁀ PBuff`; so `Pst` has an outcome only when
the cursor is at the top (or, by coincidence, `Left_Char = Right_Char`). -/
theorem pst_impossible {pb l r l' r' ms' md' : List Char} (hl : l ≠ []) (hlr : l ≠ r) :
    ¬ Pst pb l r l' r' ms' md' := by
  rintro ⟨hpb, rfl, rfl, rfl, rfl, hinv⟩
  rcases hinv with ⟨h, -⟩ | h | h
  · exact hl h
  · simp at h; exact hpb h
  · simp at h; exact hlr h

/-- `Pst` as intended, and as the C (`Paste_Doc6`, `MP=CP` before inserting) does it. -/
def PstC (pb l r l' r' ms' md' : List Char) : Prop :=
  pb ≠ [] ∧ l' = l ++ pb ∧ r' = r ∧ ms' = l ∧ md' = pb

/-- ```
Paste_Doc6 ≙ FlagPrevCursor ; Pst ; RemTrailWS ; RemTrailNL ∧ ΔDoc6 ∧ Success
           ∨ ΞDoc6 ∧ ErrorFull
           ∨ ErrorPBuffEmpty
``` -/
def Paste_Doc6 (d d' : Doc6) (rep : Report) : Prop :=
  (∃ m₁ m₂ : Doc2, Pst d.pBuff d.leftChar d.rightChar m₁.leftChar m₁.rightChar
        d'.markSeq d'.markedSeq ∧
      RemTrailWS (FlagPrevCursor d.toDoc2) m₁ m₂ ∧ RemTrailNL m₂ d'.toDoc2 ∧
      d'.pBuff = d.pBuff ∧ Success rep) ∨
  (d' = d ∧ rep = "Editor full") ∨
  (d' = d ∧ d.pBuff = [] ∧ rep = "Paste buffer empty")

/-- **Away from the top of the document, Paste can only report "Editor full"**
(or "Paste buffer empty" when the buffer is empty). -/
theorem paste_only_full {d d' : Doc6} {rep : Report} (hl : d.leftChar ≠ [])
    (hlr : d.leftChar ≠ d.rightChar) (hpb : d.pBuff ≠ []) (h : Paste_Doc6 d d' rep) :
    rep = "Editor full" := by
  rcases h with ⟨m₁, m₂, hpst, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩
  · exact absurd hpst (pst_impossible hl hlr)
  · exact h
  · exact absurd h hpb

/-! ## §5.2.1 Promotion of the Doc5 operations -/

/-- `EditOps2 ≙ CursorOps ∪ NonCursorOps ∪ {Mark}` and
`∀ OP : EditOps2 • OP_Doc6 ≙ OP_Doc5 ∧ ΞPasteBuffer`. -/
inductive EditOp6 where
  | op5 (op : EditOp5)
  | mark

def EditOp6.doc6 (pageHeight : Nat) (op : EditOp6) (d d' : Doc6) (rep : Report) : Prop :=
  d'.pBuff = d.pBuff ∧
  match op with
  | .op5 op => op.doc5 pageHeight d.toDoc5 d'.toDoc5 rep
  | .mark => SetMark_Doc5 d.toDoc5 d'.toDoc5 rep

end ZEditor
