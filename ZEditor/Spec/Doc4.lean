import ZEditor.Spec.Doc3

/-!
# QP and Doc4: cursor movement (Part Three, §4)

Printed pp.80–86 (PDF pp.83–89). The QP ("quarter plane") cursor can move
anywhere to the right of and below the top-left corner, including beyond the
text. Doc4 ties it to the display cursor; moving outside the text pads the
document with spaces and empty lines (`PadWSNL`).
-/

namespace ZEditor

/-! ## §4.1 The QP state -/

/-- `QP ≙ [ QPCurX, QPCurY : ℕ₁ ]` -/
structure QP where
  qpCurX : Nat
  qpCurY : Nat
  qpCurX_pos : 1 ≤ qpCurX
  qpCurY_pos : 1 ≤ qpCurY

abbrev QPOp := QP → QP → Prop
abbrev QPTotalOp := QP → QP → Report → Prop

/-- `QPHorizMove ≙ [ ΔQP | QPCurY′ = QPCurY ]` -/
def QPHorizMove : QPOp := fun q q' => q'.qpCurY = q.qpCurY

/-- `QPVertMove ≙ [ ΔQP ; y : ℕ₁ | QPCurX′ = QPCurX ]` -/
def QPVertMove : QPOp := fun q q' => q'.qpCurX = q.qpCurX

/-- `QPCurUp`: `QPCurY − y > 0`, `QPCurY′ = QPCurY − y`. -/
def QPCurUp (y : Nat) : QPOp := fun q q' =>
  QPVertMove q q' ∧ y < q.qpCurY ∧ q'.qpCurY = q.qpCurY - y

/-- `QPCurDown`: `QPCurY′ = QPCurY + y`. -/
def QPCurDown (y : Nat) : QPOp := fun q q' =>
  QPVertMove q q' ∧ q'.qpCurY = q.qpCurY + y

/-- `QPCurLeft`: `QPCurX > 1`, `QPCurX′ = QPCurX − 1`. -/
def QPCurLeft : QPOp := fun q q' =>
  QPHorizMove q q' ∧ q.qpCurX > 1 ∧ q'.qpCurX = q.qpCurX - 1

/-- `QPCurRight`: `QPCurX′ = QPCurX + 1`. -/
def QPCurRight : QPOp := fun q q' =>
  QPHorizMove q q' ∧ q'.qpCurX = q.qpCurX + 1

/-- `ErrorAtTopPage`: `QPCurY − y ≤ 0`. -/
def ErrorAtTopPage (y : Nat) : QPTotalOp := fun q q' rep =>
  q' = q ∧ q.qpCurY ≤ y ∧ rep = "At top page of document"

/-- `ErrorQPAtTop`: `QPCurX = QPCurY = 1`. -/
def ErrorQPAtTop : QPTotalOp := fun q q' rep =>
  q' = q ∧ q.qpCurX = 1 ∧ q.qpCurY = 1 ∧ rep = "At top of document"

/-- `QPCurToPrevLine`: at the left edge, move up a line; the new `QPCurX` is
left open. -/
def QPCurToPrevLine : QPOp := fun q q' =>
  q.qpCurX = 1 ∧ q.qpCurY > 1 ∧ q'.qpCurY = q.qpCurY - 1

/-- `CursorUp ≙ QPCurUp ∧ Success ∨ ErrorAtTopPage` -/
def CursorUp (y : Nat) : QPTotalOp := fun q q' rep =>
  (QPCurUp y q q' ∧ Success rep) ∨ ErrorAtTopPage y q q' rep

/-- `CursorDown ≙ QPCurDown ∧ Success` -/
def CursorDown (y : Nat) : QPTotalOp := fun q q' rep => QPCurDown y q q' ∧ Success rep

/-- `CursorLeft ≙ QPCurLeft ∧ Success ∨ QPCurToPrevLine ∧ Success ∨ ErrorQPTop`
(the schema is defined as `ErrorQPAtTop` and used as `ErrorQPTop`). -/
def CursorLeft : QPTotalOp := fun q q' rep =>
  (QPCurLeft q q' ∧ Success rep) ∨ (QPCurToPrevLine q q' ∧ Success rep) ∨ ErrorQPAtTop q q' rep

/-- `CursorRight ≙ QPCurRight ∧ Success` -/
def CursorRight : QPTotalOp := fun q q' rep => QPCurRight q q' ∧ Success rep

/-- "each of which clearly preserves the state invariant": the four QP
operations always have an outcome. -/
theorem CursorUp_total (y : Nat) (q : QP) : ∃ q' rep, CursorUp y q q' rep := by
  by_cases h : y < q.qpCurY
  · exact ⟨⟨q.qpCurX, q.qpCurY - y, q.qpCurX_pos, by omega⟩, _, .inl ⟨⟨rfl, h, rfl⟩, rfl⟩⟩
  · exact ⟨q, _, .inr ⟨rfl, by omega, rfl⟩⟩

theorem CursorDown_total (y : Nat) (q : QP) : ∃ q' rep, CursorDown y q q' rep :=
  ⟨⟨q.qpCurX, q.qpCurY + y, q.qpCurX_pos, by have := q.qpCurY_pos; omega⟩, _, ⟨rfl, rfl⟩, rfl⟩

theorem CursorLeft_total (q : QP) : ∃ q' rep, CursorLeft q q' rep := by
  have := q.qpCurX_pos
  have := q.qpCurY_pos
  by_cases hx : q.qpCurX > 1
  · exact ⟨⟨q.qpCurX - 1, q.qpCurY, by omega, q.qpCurY_pos⟩, _, .inl ⟨⟨rfl, hx, rfl⟩, rfl⟩⟩
  · by_cases hy : q.qpCurY > 1
    · exact ⟨⟨1, q.qpCurY - 1, by omega, by omega⟩, _,
        .inr (.inl ⟨⟨by omega, hy, rfl⟩, rfl⟩)⟩
    · exact ⟨q, _, .inr (.inr ⟨rfl, by omega, by omega, rfl⟩)⟩

theorem CursorRight_total (q : QP) : ∃ q' rep, CursorRight q q' rep :=
  ⟨⟨q.qpCurX + 1, q.qpCurY, by omega, q.qpCurY_pos⟩, _, ⟨rfl, rfl⟩, rfl⟩

/-- `QPCursorOps ≙ { CursorUpChar, CursorDownChar, CursorUpPage, CursorDownPage,
CursorLeftChar, CursorRightChar }` -/
inductive QPCursorOp where
  | cursorUpChar | cursorDownChar | cursorUpPage | cursorDownPage
  | cursorLeftChar | cursorRightChar

/-- `CursorUpChar_QP ≙ [ QPCursorUp | y = 1 ]`, `CursorUpPage_QP ≙ [ QPCursorUp | y = PageHeight ]`,
etc. (written `QPCursorUp` but defined as `CursorUp`). `PageHeight : ℕ₁` with
`PageHeight < WindowHeight` is a parameter; `WindowHeight` comes in §8. -/
def QPCursorOp.qp (pageHeight : Nat) : QPCursorOp → QPTotalOp
  | .cursorUpChar => CursorUp 1
  | .cursorUpPage => CursorUp pageHeight
  | .cursorDownChar => CursorDown 1
  | .cursorDownPage => CursorDown pageHeight
  | .cursorLeftChar => CursorLeft
  | .cursorRightChar => CursorRight

/-! ## §4.2 The Doc4 state -/

/-- `Doc4 ≙ [ Doc3 ∧ QP | UDCurX = QPCurX ∧ UDCurY = QPCurY ]` -/
structure Doc4 extends Doc3, QP where
  udCurX_qp : udCurX = qpCurX
  udCurY_qp : udCurY = qpCurY

/-- `Initialize_Doc4 ≙ Initialize_Doc3 ∧ ΔDoc4` -/
def Initialize_Doc4 (d' : Doc4) : Prop := Initialize_Doc3 d'.toDoc3

/-- **Lemma 3:4.2a.** Initially the QP cursor is at (1, 1). -/
theorem Initialize_Doc4_qp {d' : Doc4} (h : Initialize_Doc4 d') :
    d'.qpCurX = 1 ∧ d'.qpCurY = 1 := by
  obtain ⟨-, -, hx, hy⟩ := Initialize_Doc2_display h
  exact ⟨d'.udCurX_qp ▸ hx, d'.udCurY_qp ▸ hy⟩

/-- A Doc3 state with its QP cursor equated to its display cursor
(`EquateQPWithUD`). -/
def Doc3.toDoc4 (d : Doc3) : Doc4 :=
  { toDoc3 := d, qpCurX := d.udCurX, qpCurY := d.udCurY,
    qpCurX_pos := d.udCurX_pos, qpCurY_pos := d.udCurY_pos,
    udCurX_qp := rfl, udCurY_qp := rfl }

/-- **PO 0 for Doc4.** -/
theorem Initialize_Doc4_exists : ∃ d' : Doc4, Initialize_Doc4 d' := by
  obtain ⟨d, h⟩ := Initialize_Doc3_exists
  exact ⟨d.toDoc4, h⟩

/-! ### §4.2.1 Promotion of the Doc3 operations -/

/-- `∀ OP : EditOps1 • OP_Doc4 ≙ (OP_Doc3 ; EquateQPWithUD) ∧ ΔDoc4`. The QP
cursor of a Doc4 state always equals the display cursor, so `EquateQPWithUD`
is built into the type. -/
def EditOp1.doc4 (op : EditOp1) (d d' : Doc4) (rep : Report) : Prop :=
  op.doc3 d.toDoc3 d'.toDoc3 rep

/-! ### §4.2.2 Promotion of the QP operations -/

/-- ```
┌─ PadWSNL ────────────────────────────
│ ΔUD
│ EquateUDWithQP
├──────────────────────────────────────
│     QPCurY ≤ # UDLines
│     {QPCurY} ⩤ UDLines′ = {QPCurY} ⩤ UDLines
│     UDLines QPCurY visible_prefix UDCurLine′
│ ∨
│     QPCurY > # UDLines
│     # UDLines′ = QPCurY
│     UDLines prefix UDLines′
│     ∀ i : # UDLines + 1 .. QPCurY − 1 • UDLines′ i = ⟨⟩
│     rng (UDCurLine′) ⊆ {sp}
└──────────────────────────────────────
```
`EquateUDWithQP`: `UDCurX′, UDCurY′ = QPCurX, QPCurY`. As with `RemTrailWS`,
the schema is declared on `ΔUD` and used on Doc2 states. -/
def PadWSNL (q : QP) (d d' : Doc2) : Prop :=
  d'.udCurX = q.qpCurX ∧ d'.udCurY = q.qpCurY ∧
  ((q.qpCurY ≤ d.udLines.length ∧
      (∀ i, i + 1 ≠ q.qpCurY → d'.udLines[i]? = d.udLines[i]?) ∧
      ∃ l, d.udLines[q.qpCurY - 1]? = some l ∧ visiblePrefix l d'.udCurLine) ∨
   (q.qpCurY > d.udLines.length ∧ d'.udLines.length = q.qpCurY ∧ d.udLines <+: d'.udLines ∧
      (∀ i, d.udLines.length ≤ i → i + 1 < q.qpCurY → d'.udLines[i]? = some []) ∧
      ∀ c ∈ d'.udCurLine, c = sp))

/-- `CursorLeftChar_Doc4 ≙ LeftMoveChar_Doc3 ∧ ΔDoc4`, and for the others
```
OP_Doc4 ≙ FlagPrevCursor ; SuccOP_QP ; PadWSNL ; RemTrailWS ; RemTrailNL ∧ ΔDoc4
        ∨ UnSuccOP_QP ∧ ΞDoc4
        ∨ ErrorFull ∧ ΞDoc4
```
with `SuccOP_QP ≙ [ OP_QP | rep! = "OK" ]` and `UnSuccOP_QP ≙ [ OP_QP | rep! ≠ "OK" ]`. -/
def QPCursorOp.doc4 (pageHeight : Nat) (op : QPCursorOp) (d d' : Doc4) (rep : Report) : Prop :=
  match op with
  | .cursorLeftChar => EditOp1.leftMoveChar.doc4 d d' rep
  | op =>
    (∃ q' m₁ m₂, op.qp pageHeight d.toQP q' rep ∧ rep = "OK" ∧
        PadWSNL q' d.toDoc2 m₁ ∧ RemTrailWS (FlagPrevCursor d.toDoc2) m₁ m₂ ∧
        RemTrailNL m₂ d'.toDoc2) ∨
    (∃ q', op.qp pageHeight d.toQP q' rep ∧ rep ≠ "OK" ∧ d' = d) ∨
    (d' = d ∧ rep = "Editor full")

/-! ## Moving right after a trailing space

`PadWSNL` requires the old cursor line to be a `visible_prefix` of the new one,
and a `visible_prefix` must itself be visible (no trailing space). The cursor
line is the one line allowed to end in spaces, and only when the cursor is at
its end, which is exactly where you are after typing a space at the end of a
line. From there the first disjunct of `PadWSNL` is impossible and the second
does not apply, so `CursorRightChar_Doc4` can only answer "Editor full".

The C (`CursorRightChar_Doc4`, Appendix C p.vii) inserts a space and moves on. -/

/-- The document "a␣|": one line, "a" and a space, cursor at the end. -/
def aSp : Doc4 :=
  (show Doc3 from
    { toDoc2 := Doc2.ofDoc1 (Doc1.ofChars ['a', ' '] [])
      lines_visible := by
        intro i hi hne
        have hl : (Doc2.ofDoc1 (Doc1.ofChars ['a', ' '] [])).udLines = [['a', ' ']] := by
          decide
        have hy : (Doc2.ofDoc1 (Doc1.ofChars ['a', ' '] [])).udCurY = 1 := by decide
        simp only [hl, hy] at hi hne ⊢
        have : i = 0 := by simpa using hi
        omega
      cur_visible := by decide
      after_visible := by decide }).toDoc4

theorem aSp_lines : aSp.udLines = [['a', ' ']] := by decide

/-- **`CursorRightChar_Doc4` after a trailing space can only report "Editor full".** -/
theorem cursorRight_after_space (pageHeight : Nat) :
    ∀ d' rep, QPCursorOp.cursorRightChar.doc4 pageHeight aSp d' rep → rep = "Editor full" := by
  intro d' rep h
  rcases h with ⟨q', m₁, m₂, hq, -, hpad, -⟩ | ⟨q', hq, hne, -⟩ | ⟨-, h⟩
  · exfalso
    obtain ⟨⟨hqy, -⟩, -⟩ := hq
    obtain ⟨-, -, ⟨-, -, l, hl, hvp⟩ | ⟨hgt, -⟩⟩ := hpad
    · have hy : aSp.toQP.qpCurY = 1 := by decide
      rw [hqy, hy, aSp_lines] at hl
      simp at hl; subst hl
      exact hvp.1 (by simp) (by decide)
    · have hy : aSp.toQP.qpCurY = 1 := by decide
      rw [hqy, hy, aSp_lines] at hgt
      simp at hgt
  · exact absurd hq.2 hne
  · exact h

/-- `PadWSNL` as the C implements it: the old line is a prefix of the new one
and only spaces are added, with no requirement that the old line be visible. -/
def PadWSNLC (q : QP) (d d' : Doc2) : Prop :=
  d'.udCurX = q.qpCurX ∧ d'.udCurY = q.qpCurY ∧
  ((q.qpCurY ≤ d.udLines.length ∧
      (∀ i, i + 1 ≠ q.qpCurY → d'.udLines[i]? = d.udLines[i]?) ∧
      ∃ l, d.udLines[q.qpCurY - 1]? = some l ∧ l <+: d'.udCurLine ∧
        ∀ c ∈ d'.udCurLine.drop l.length, c = sp) ∨
   (q.qpCurY > d.udLines.length ∧ d'.udLines.length = q.qpCurY ∧ d.udLines <+: d'.udLines ∧
      (∀ i, d.udLines.length ≤ i → i + 1 < q.qpCurY → d'.udLines[i]? = some []) ∧
      ∀ c ∈ d'.udCurLine, c = sp))

end ZEditor
