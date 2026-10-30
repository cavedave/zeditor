import ZEditor.Spec.Doc4

/-!
# Doc5: marked text (Part Three, §5.1)

Printed pp.86–88 (PDF pp.89–91). The mark is a position in the document; the
marked text lies between the mark and the cursor. It is represented by two
sequences: `MarkSeq`, from the far end of the document to the mark, and
`MarkedSeq`, from the mark to the cursor.
-/

namespace ZEditor

/-! ## The MarkedText state -/

/-- ```
┌─ MarkedText ─────────────────────
│ MarkSeq, MarkedSeq : seq Char
│ Pair_Char
├──────────────────────────────────
│     MarkSeq = MarkedSeq = ⟨⟩
│ ∨
│     MarkSeq ⁀ MarkedSeq = Left_Char
│ ∨
│     MarkedSeq ⁀ MarkSeq = Right_Char
└──────────────────────────────────
```
The first case is "no mark", the second a mark above the cursor, the third a
mark below it. -/
def MarkedTextInv (markSeq markedSeq leftChar rightChar : List Char) : Prop :=
  (markSeq = [] ∧ markedSeq = []) ∨ markSeq ++ markedSeq = leftChar ∨
    markedSeq ++ markSeq = rightChar

/-- `Doc5 ≙ Doc4 ∧ MarkedText` -/
structure Doc5 extends Doc4 where
  markSeq   : List Char
  markedSeq : List Char
  marked_inv : MarkedTextInv markSeq markedSeq leftChar rightChar

/-- `Initialize_Doc5 ≙ [ Initialize_Doc4 ∧ ΔDoc5 | MarkSeq = MarkedSeq = ⟨⟩ ]` -/
def Initialize_Doc5 (d' : Doc5) : Prop :=
  Initialize_Doc4 d'.toDoc4 ∧ d'.markSeq = [] ∧ d'.markedSeq = []

/-- A Doc4 state with no mark. -/
def Doc4.toDoc5 (d : Doc4) : Doc5 :=
  { toDoc4 := d, markSeq := [], markedSeq := [], marked_inv := .inl ⟨rfl, rfl⟩ }

/-- **PO 0 for Doc5.** -/
theorem Initialize_Doc5_exists : ∃ d' : Doc5, Initialize_Doc5 d' := by
  obtain ⟨d, h⟩ := Initialize_Doc4_exists
  exact ⟨d.toDoc5, h, rfl, rfl⟩

/-! ## Setting the mark -/

/-- `SetMk`: `MarkSeq′ = Left_Char`, `MarkedSeq′ = ⟨⟩`, and
`SetMark_Doc5 ≙ SetMk ∧ ΞDoc4 ∧ ΔDoc5 ∧ Success`. -/
def SetMark_Doc5 (d d' : Doc5) (rep : Report) : Prop :=
  d'.toDoc4 = d.toDoc4 ∧ d'.markSeq = d.leftChar ∧ d'.markedSeq = [] ∧ Success rep

/-- The mark counts as set when `MarkSeq ⁀ MarkedSeq ≠ ⟨⟩` (§5.1.1). -/
def Doc5.markSet (d : Doc5) : Prop := d.markSeq ++ d.markedSeq ≠ []

/-- **Setting the mark at the top of the document does not set it.** With the
cursor at the top, `SetMk` gives `MarkSeq′ = MarkedSeq′ = ⟨⟩`, which is the
representation of "no mark". The C keeps the mark as a position `MP`, with
`MP = −1` for "no mark", so it can mark text from the top. -/
theorem setMark_at_top {d d' : Doc5} {rep : Report} (htop : d.leftChar = [])
    (h : SetMark_Doc5 d d' rep) : ¬ d'.markSet := by
  obtain ⟨-, hms, hmd, -⟩ := h
  simp [Doc5.markSet, hms, hmd, htop]

/-! ## §5.1.1 Promotion of the Doc4 operations -/

/-- The Doc4 operations by name: the edit operations of §2.3 and the QP cursor
operations of §4.2.2. -/
inductive EditOp5 where
  | edit (op : EditOp1)
  | qp (op : QPCursorOp)

def EditOp5.doc4 (pageHeight : Nat) : EditOp5 → Doc4 → Doc4 → Report → Prop
  | .edit op => op.doc4
  | .qp op => op.doc4 pageHeight

/-- `CursorOps ≙ MoveOps ∪ QPCursorOps − NonCursorOps`, with
`NonCursorOps ≙ DeleteOps ∪ InsertOp`. -/
def EditOp5.isCursorOp : EditOp5 → Bool
  | .edit .rightMoveChar | .edit .leftMoveChar | .edit .rightMoveWord | .edit .leftMoveWord
  | .edit .rightMoveLine | .edit .leftMoveLine | .edit .moveToTop | .edit .moveToBot => true
  | .qp _ => true
  | _ => false

/-- As printed:
```
CursorOps_NoMarkSet ≙ CursorOps | MarkSeq′ = MarkedSeq′ = ⟨⟩
CursorOps_MarkSet   ≙ CursorOps | MarkSeq′ ⁀ MarkedSeq′ ≠ ⟨⟩

∀ OP : NonCursorOps        • OP_Doc5 ≙ OP_Doc4 ∧ ResetMark
∀ OP : CursorOps_NoMarkSet • OP_Doc5 ≙ OP_Doc4 ∧ ΞMarkedText
∀ OP : CursorOps_MarkSet   • OP_Doc5 ≙ OP_Doc4 ∧ ΔMarkedText
```
The conditions that split `CursorOps` are on the *after*-state (primed). -/
def EditOp5.doc5 (pageHeight : Nat) (op : EditOp5) (d d' : Doc5) (rep : Report) : Prop :=
  op.doc4 pageHeight d.toDoc4 d'.toDoc4 rep ∧
  if op.isCursorOp then
    (d'.markSeq = [] ∧ d'.markedSeq = [] ∧ d'.markSeq = d.markSeq ∧ d'.markedSeq = d.markedSeq) ∨
    d'.markSet
  else
    d'.markSeq = [] ∧ d'.markedSeq = []

/-- **As printed, a cursor move can create a mark from nothing.** Because
`CursorOps_MarkSet` is selected by the *after*-state, any outcome of a cursor
operation may carry any mark, even when no mark was set before. Read on the
before-state instead, the problem becomes `setMark_at_top`: a mark set at the
top of the document is lost. Either way, "mark set at the top" and "no mark"
need different representations, as the C has. -/
theorem cursorOp_mark_unconstrained (pageHeight : Nat) {op : EditOp5}
    (hc : op.isCursorOp = true) {d : Doc5} {e : Doc4} {rep : Report}
    (h : op.doc4 pageHeight d.toDoc4 e rep) {ms md : List Char}
    (hinv : MarkedTextInv ms md e.leftChar e.rightChar) (hne : ms ++ md ≠ []) :
    op.doc5 pageHeight d { toDoc4 := e, markSeq := ms, markedSeq := md, marked_inv := hinv } rep :=
  ⟨h, by simp only [hc, if_true]; exact .inr hne⟩

end ZEditor
