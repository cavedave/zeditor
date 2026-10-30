import ZEditor.Spec.Doc8

/-!
# Doc9: a window onto the display (Part Three, §8)

Printed pp.115–123 (PDF pp.118–126). The terminal shows a fixed-size window
onto the unbounded display, positioned by two offsets. Doc9 is the complete
editor: every Doc8 operation is followed by a window policy that moves the
window, if necessary, to keep the cursor in view.
-/

namespace ZEditor

/-! ## §8.1 The window state -/

/-- `WinWidth, WinHeight : ℕ₁` -/
structure WinParams where
  winWidth  : Nat
  winHeight : Nat
  winWidth_pos  : 1 ≤ winWidth
  winHeight_pos : 1 ≤ winHeight

variable (P : WinParams)

/-- `WindowLines = (WinMaskLines after OffsetY) for WinHeight`, where
`WinMaskLines y = ((UDLines y) after OffsetX) for WinWidth`. -/
def winLinesOf (L : List (List Char)) (ox oy : Nat) : List (List Char) :=
  ((L.map fun l => (l.drop ox).take P.winWidth).drop oy).take P.winHeight

/-- ```
┌─ Doc9 ───────────────────────────────
│ Doc8
│ Window
├──────────────────────────────────────
│ WinCurX, WinCurY = UDCurX − OffsetX, UDCurY − OffsetY
│ WindowLines = (WinMaskLines after OffsetY) for WinHeight
│ where ...
└──────────────────────────────────────
```
with `Window` (`WindowLines : seq₁ DispLine`, `# WindowLines ≤ WinHeight`, each
line at most `WinWidth` long; written `# WinLines` in the book),
`WindowOffset ≙ [ OffsetX, OffsetY : ℕ ]` and `WindowCursor` (`1 ≤ WinCurX ≤
WinWidth`, `1 ≤ WinCurY ≤ WinHeight`). -/
structure Doc9 extends Doc8 where
  offsetX : Nat
  offsetY : Nat
  winCurX : Nat
  winCurY : Nat
  windowLines : List (List Char)
  winCurX_eq : winCurX = udCurX - offsetX
  winCurY_eq : winCurY = udCurY - offsetY
  winCurX_range : 1 ≤ winCurX ∧ winCurX ≤ P.winWidth
  winCurY_range : 1 ≤ winCurY ∧ winCurY ≤ P.winHeight
  windowLines_eq : windowLines = winLinesOf P udLines offsetX offsetY
  windowLines_ne : windowLines ≠ []
  windowLines_disp : ∀ l ∈ windowLines, IsDispLine l
  windowLines_len : windowLines.length ≤ P.winHeight
  windowLines_width : ∀ l ∈ windowLines, l.length ≤ P.winWidth

/-- The cursor is in the window placed at offsets `(ox, oy)`. -/
def InWindow (d : Doc8) (ox oy : Nat) : Prop :=
  ox < d.udCurX ∧ d.udCurX ≤ ox + P.winWidth ∧ oy < d.udCurY ∧ d.udCurY ≤ oy + P.winHeight

/-- The Doc9 state with Doc8 part `d` and offsets `(ox, oy)`: `Doc8` and the
offsets determine Doc9 (printed p.118). -/
def Doc9.make (d : Doc8) (ox oy : Nat) (h : InWindow P d ox oy) : Doc9 P where
  toDoc8 := d
  offsetX := ox
  offsetY := oy
  winCurX := d.udCurX - ox
  winCurY := d.udCurY - oy
  windowLines := winLinesOf P d.udLines ox oy
  winCurX_eq := rfl
  winCurY_eq := rfl
  winCurX_range := by have := P.winWidth_pos; unfold InWindow at h; omega
  winCurY_range := by have := P.winHeight_pos; unfold InWindow at h; omega
  windowLines_eq := rfl
  windowLines_ne := by
    have := P.winHeight_pos
    have := d.udCurY_le
    unfold InWindow at h
    intro e
    have hl := congrArg List.length e
    simp [winLinesOf] at hl
    omega
  windowLines_disp := by
    intro l hl
    simp only [winLinesOf] at hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take hl))
    exact fun hn => d.udLines_disp m hm (List.mem_of_mem_drop (List.mem_of_mem_take hn))
  windowLines_len := by simp [winLinesOf]; omega
  windowLines_width := by
    intro l hl
    simp only [winLinesOf] at hl
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take hl))
    simp; omega

theorem Doc9.inWindow (d : Doc9 P) : InWindow P d.toDoc8 d.offsetX d.offsetY := by
  have := d.winCurX_eq; have := d.winCurY_eq
  have := d.winCurX_range; have := d.winCurY_range
  unfold InWindow; omega

theorem Doc9.eq_make (d : Doc9 P) : d = Doc9.make P d.toDoc8 d.offsetX d.offsetY d.inWindow := by
  obtain ⟨d8, dx, dy, dcx, dcy, dw, h1, h2, _, _, h3, _, _, _, _⟩ := d
  subst h1 h2 h3
  rfl

/-- Doc8 and the offsets determine Doc9. -/
theorem Doc9.ext {d e : Doc9 P} (h8 : d.toDoc8 = e.toDoc8) (hx : d.offsetX = e.offsetX)
    (hy : d.offsetY = e.offsetY) : d = e := by
  rw [d.eq_make P, e.eq_make P]
  congr

/-- **Lemma 3:8.2a**, in the form that is true. The book states
`(WindowLines WinCurY) WinCurX = (UDLines UDCurY) UDCurX`, but when the cursor
is just after the last character of its line (always, in the empty document)
neither side is defined. With partial indexing both sides are "nothing" there,
and the equation holds everywhere. (Step 8 of the book's proof has `WinHeight`
for `WinWidth`.) -/
theorem Doc9.char_at_cursor (d : Doc9 P) :
    (d.windowLines[d.winCurY - 1]?).bind (·[d.winCurX - 1]?) =
      (d.udLines[d.udCurY - 1]?).bind (·[d.udCurX - 1]?) := by
  have hw := d.inWindow
  unfold InWindow at hw
  rw [d.windowLines_eq, d.winCurX_eq, d.winCurY_eq]
  simp only [winLinesOf]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, List.getElem?_map]
  have : d.offsetY + (d.udCurY - d.offsetY - 1) = d.udCurY - 1 := by omega
  rw [this]
  cases d.udLines[d.udCurY - 1]? with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Option.bind_some]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    have : d.offsetX + (d.udCurX - d.offsetX - 1) = d.udCurX - 1 := by omega
    rw [this]

/-- `Initialize_Doc9 ≙ Initialize_Doc8 ∧ ΔDoc9` -/
def Initialize_Doc9 (filename : List Char) (d' : Doc9 P) : Prop :=
  Initialize_Doc8 filename d'.toDoc8

/-- **Lemmas 3:8.2b and 3:8.2c.** Initially the offsets are 0, the window cursor
is (1, 1) and the window shows one empty line. (Step 6 of the proof of 8.2c
has `WinWidth` for `WinHeight`.) -/
theorem Initialize_Doc9_window {fn : List Char} {d' : Doc9 P} (h : Initialize_Doc9 P fn d') :
    d'.offsetX = 0 ∧ d'.offsetY = 0 ∧ d'.winCurX = 1 ∧ d'.winCurY = 1 ∧
      d'.windowLines = [[]] := by
  obtain ⟨hl, -, hx, hy⟩ := Initialize_Doc2_display h.1.1.1.1
  have := d'.winCurX_eq; have := d'.winCurY_eq
  have := d'.winCurX_range; have := d'.winCurY_range
  have hox : d'.offsetX = 0 := by omega
  have hoy : d'.offsetY = 0 := by omega
  refine ⟨hox, hoy, by omega, by omega, ?_⟩
  rw [d'.windowLines_eq, hl, hox, hoy]
  obtain ⟨k, hk⟩ : ∃ k, P.winHeight = k + 1 := ⟨P.winHeight - 1, by have := P.winHeight_pos; omega⟩
  simp [winLinesOf, hk]

/-! ## §8.2.1 Centring the window -/

/-- `HalfWinHeight : ℕ | HalfWinHeight = WinHeight / 2`. The book says its
minimum value is 1; for `WinHeight = 1` it is 0. -/
def HalfWinHeight : Nat := P.winHeight / 2

/-- `CenWin`: `ΞDoc8`, `UDCurY ≥ HalfWinHeight`, `OffsetX′ = OffsetX`,
`OffsetY′ = UDCurY − HalfWinHeight`. -/
def CenWin (d d' : Doc9 P) : Prop :=
  d'.toDoc8 = d.toDoc8 ∧ d.udCurY ≥ HalfWinHeight P ∧ d'.offsetX = d.offsetX ∧
  d'.offsetY = d.udCurY - HalfWinHeight P

/-- `ErrorTooNearTop`: `ΞDoc9`, `UDCurY < HalfWinHeight`. -/
def ErrorTooNearTop (d d' : Doc9 P) (rep : Report) : Prop :=
  d' = d ∧ d.udCurY < HalfWinHeight P ∧ rep = "Too near top of document"

/-- `CentreWindow_Doc9 ≙ (CenWin ∧ Success) ∨ ErrorTooNearTop` -/
def CentreWindow_Doc9 (d d' : Doc9 P) (rep : Report) : Prop :=
  (CenWin P d d' ∧ Success rep) ∨ ErrorTooNearTop P d d' rep

/-- For a window at least two lines high, centring always has an outcome. -/
theorem CentreWindow_Doc9_total (h2 : 2 ≤ P.winHeight) (d : Doc9 P) :
    ∃ d' rep, CentreWindow_Doc9 P d d' rep := by
  by_cases hy : d.udCurY < HalfWinHeight P
  · exact ⟨d, _, .inr ⟨rfl, hy, rfl⟩⟩
  · have hw := d.inWindow
    unfold InWindow at hw
    have hh : 1 ≤ HalfWinHeight P ∧ HalfWinHeight P ≤ P.winHeight := by
      unfold HalfWinHeight; omega
    have hin : InWindow P d.toDoc8 d.offsetX (d.udCurY - HalfWinHeight P) := by
      unfold InWindow; omega
    exact ⟨Doc9.make P d.toDoc8 _ _ hin, _, .inl ⟨⟨rfl, by omega, rfl, rfl⟩, rfl⟩⟩

/-- **With a one-line window, centring has no outcome.** `HalfWinHeight = 0`, so
`CenWin` would put the cursor on window line 0, and `ErrorTooNearTop` needs
`UDCurY < 0`. -/
theorem centreWindow_height_one (h1 : P.winHeight = 1) (d : Doc9 P) :
    ¬ ∃ d' rep, CentreWindow_Doc9 P d d' rep := by
  have h0 : HalfWinHeight P = 0 := by simp [HalfWinHeight, h1]
  rintro ⟨d', rep, ⟨⟨h8, -, -, hoy⟩, -⟩ | ⟨-, hlt, -⟩⟩
  · have := d'.winCurY_eq
    have := d'.winCurY_range
    have hy : d'.udCurY = d.udCurY := by rw [h8]
    omega
  · omega

/-! ## §8.2.2 The window policy -/

/-- The four window operations of the policy, on the Doc8 state `d` that an
operation has produced, the old offsets `(ox, oy)` and the new state `e`:
```
CursorInWindow : cursor in the old window; any new window containing it
Scroll         : only vertically out;   OffsetX′ = OffsetX
Pan            : only horizontally out; OffsetY′ = OffsetY
ScrollAndPan   : out both ways
WindowPolicy ≙ (CursorInWindow ∨ Scroll ∨ Pan ∨ ScrollAndPan) ∧ Doc9′
```
Each has `ΞDoc8` and requires the cursor to be in the new window, which is part
of `Doc9′`. -/
def WindowPolicy (d : Doc8) (ox oy : Nat) (e : Doc9 P) : Prop :=
  let inX := ox < d.udCurX ∧ d.udCurX ≤ ox + P.winWidth
  let inY := oy < d.udCurY ∧ d.udCurY ≤ oy + P.winHeight
  e.toDoc8 = d ∧
  ((inX ∧ inY) ∨
   (inX ∧ ¬ inY ∧ e.offsetX = ox) ∨
   (¬ inX ∧ inY ∧ e.offsetY = oy) ∨
   (¬ inX ∧ ¬ inY))

/-- "The pre-conditions of the four disjunctions form a partition … and so the
promotion operation is total." -/
theorem WindowPolicy_total (d : Doc8) (ox oy : Nat) : ∃ e, WindowPolicy P d ox oy e := by
  have := P.winWidth_pos; have := P.winHeight_pos
  have := d.udCurX_pos; have := d.udCurY_pos
  -- keep each offset if it already works, otherwise put the cursor in the first column/row
  let ox' := if ox < d.udCurX ∧ d.udCurX ≤ ox + P.winWidth then ox else d.udCurX - 1
  let oy' := if oy < d.udCurY ∧ d.udCurY ≤ oy + P.winHeight then oy else d.udCurY - 1
  have hin : InWindow P d ox' oy' := by
    unfold InWindow
    simp only [ox', oy']
    split <;> split <;> omega
  refine ⟨Doc9.make P d ox' oy' hin, rfl, ?_⟩
  simp only [Doc9.make, ox', oy']
  by_cases hx : ox < d.udCurX ∧ d.udCurX ≤ ox + P.winWidth <;>
    by_cases hy : oy < d.udCurY ∧ d.udCurY ≤ oy + P.winHeight <;> simp_all

/-- `∀ OP : EditOps5 • OP_Doc9 ≙ OP_Doc8 ; WindowPolicy` -/
def promote9 (op8 : Doc8 → Doc8 → Report → Prop) (d d' : Doc9 P) (rep : Report) : Prop :=
  ∃ m, op8 d.toDoc8 m rep ∧ WindowPolicy P m d.offsetX d.offsetY d'

/-- "We thus discharge PO 1 for each Doc8 operation": every Doc8 operation that
has an outcome has one in Doc9. (The Doc8 operations shown above to have no
outcome have none in Doc9 either.) -/
theorem promote9_total {op8 : Doc8 → Doc8 → Report → Prop} {d : Doc9 P}
    (h : ∃ m rep, op8 d.toDoc8 m rep) : ∃ d' rep, promote9 P op8 d d' rep := by
  obtain ⟨m, rep, hm⟩ := h
  obtain ⟨e, he⟩ := WindowPolicy_total P m d.offsetX d.offsetY
  exact ⟨e, rep, m, hm, he⟩

end ZEditor
