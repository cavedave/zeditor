import ZEditor.Spec.Total

/-!
# Doc2: the unbounded display (Part Three, §2)

Printed pp.69–75 (PDF pp.72–78). The document is shown in full as a sequence
of display lines, with a screen cursor `(UDCurX, UDCurY)` counted from `(1, 1)`.
Doc2 adds this display to Doc1. Every display component is determined by the
Doc1 characters (`Doc2.ofDoc1`, `Doc2.ext`), which is the consistency argument
the book gives on printed pp.73–74, made formal.
-/

namespace ZEditor

/-! ## §2.1 The unbounded display model -/

/-- `DispLine == seq (Char − {nl})`: unlike the lines of Doc1, a display line
may be empty and never contains a newline. -/
abbrev IsDispLine (l : List Char) : Prop := nl ∉ l

/-- ```
┌─ UD ───────────────────────────────
│ UDLines : seq₁ DispLine
│ UDCurX, UDCurY : ℕ₁
│ UDCurLine : DispLine
├────────────────────────────────────
│ UDCurY ≤ # UDLines
│ UDCurLine = UDLines UDCurY
│ UDCurX ≤ # UDCurLine + 1
└────────────────────────────────────
```
Z sequences are indexed from 1, Lean lists from 0: `UDLines UDCurY` is
`udLines[udCurY - 1]`. -/
structure UD where
  udLines   : List (List Char)
  udCurX    : Nat
  udCurY    : Nat
  udCurLine : List Char
  udLines_ne   : udLines ≠ []
  udLines_disp : ∀ l ∈ udLines, IsDispLine l
  udCurLine_disp : IsDispLine udCurLine
  udCurX_pos : 1 ≤ udCurX
  udCurY_pos : 1 ≤ udCurY
  udCurY_le  : udCurY ≤ udLines.length
  udCurLine_eq : udLines[udCurY - 1]? = some udCurLine
  udCurX_le  : udCurX ≤ udCurLine.length + 1

/-- **Lemma 3:2.1a.** The display with one empty line has the cursor at (1, 1). -/
theorem UD.single_empty (u : UD) (h : u.udLines = [[]]) :
    u.udCurY = 1 ∧ u.udCurLine = [] ∧ u.udCurX = 1 := by
  have hy1 := u.udCurY_pos
  have hy2 := u.udCurY_le
  rw [h] at hy2; simp at hy2
  have hy : u.udCurY = 1 := by omega
  have hl := u.udCurLine_eq
  rw [h, hy] at hl; simp at hl
  have hx1 := u.udCurX_pos
  have hx2 := u.udCurX_le
  rw [hl] at hx2; simp at hx2
  exact ⟨hy, hl, by omega⟩

/-! ## §2.2 FDL: flattening display lines -/

/-- `FDL : seq₁ DispLine ⤖ seq Char` puts a newline between adjacent lines.
(The book defines it by the two equations proved as `FDL_single` and
`FDL_append`; on `⟨⟩`, outside its domain, we return `⟨⟩`.) -/
def FDL : List (List Char) → List Char
  | [] => []
  | [l] => l
  | l :: L => l ++ nl :: FDL L

/-- `FDL⁻¹`: cut a character sequence at its newlines. -/
def FDLinv : List Char → List (List Char)
  | [] => [[]]
  | c :: t =>
    match FDLinv t with
    | l :: R => if c = nl then [] :: l :: R else (c :: l) :: R
    | [] => [[c]]

theorem FDL_single (l : List Char) : FDL [l] = l := rfl

theorem FDL_cons_cons (l m : List Char) (L : List (List Char)) :
    FDL (l :: m :: L) = l ++ nl :: FDL (m :: L) := rfl

/-- The book's defining equation `FDL (L1 ⁀ L2) = (FDL L1) ⁀ ⟨nl⟩ ⁀ (FDL L2)`. -/
theorem FDL_append (L₁ L₂ : List (List Char)) (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ []) :
    FDL (L₁ ++ L₂) = FDL L₁ ++ nl :: FDL L₂ := by
  induction L₁ with
  | nil => exact absurd rfl h₁
  | cons l L ih =>
    cases L with
    | nil =>
      cases L₂ with
      | nil => exact absurd rfl h₂
      | cons m M => simp [FDL_cons_cons, FDL_single]
    | cons l' L' =>
      rw [List.cons_append, List.cons_append, FDL_cons_cons, ← List.cons_append,
        ih (List.cons_ne_nil _ _), FDL_cons_cons]
      simp

theorem FDLinv_ne (C : List Char) : FDLinv C ≠ [] := by
  cases C with
  | nil => simp [FDLinv]
  | cons c t =>
    simp only [FDLinv]
    split
    · split <;> simp
    · simp

theorem FDLinv_eq_cons (t : List Char) : ∃ l R, FDLinv t = l :: R := by
  cases h : FDLinv t with
  | nil => exact absurd h (FDLinv_ne t)
  | cons l R => exact ⟨l, R, rfl⟩

/-- One step of `FDL⁻¹`: a newline starts a new line, any other character joins
the first line. -/
theorem FDLinv_cons_of {c : Char} {t l : List Char} {R : List (List Char)}
    (h : FDLinv t = l :: R) :
    FDLinv (c :: t) = if c = nl then [] :: l :: R else (c :: l) :: R := by
  simp [FDLinv, h]

theorem snoc_inj {α : Type} {A B : List α} {a b : α} (h : A ++ [a] = B ++ [b]) :
    A = B ∧ a = b := by
  have := List.append_inj' h rfl
  simpa using this

theorem FDLinv_disp (C : List Char) : ∀ l ∈ FDLinv C, IsDispLine l := by
  induction C with
  | nil => simp [FDLinv, IsDispLine]
  | cons c t ih =>
    obtain ⟨l, R, h⟩ := FDLinv_eq_cons t
    rw [FDLinv_cons_of h]
    rw [h] at ih
    split
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [IsDispLine]
      · exact ih k hk
    · rename_i hc
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · have := ih l (List.mem_cons_self ..)
        simp only [IsDispLine, List.mem_cons, not_or] at this ⊢
        exact ⟨fun e => hc e.symm, this⟩
      · exact ih k (List.mem_cons_of_mem _ hk)

theorem FDL_FDLinv (C : List Char) : FDL (FDLinv C) = C := by
  induction C with
  | nil => rfl
  | cons c t ih =>
    obtain ⟨l, R, h⟩ := FDLinv_eq_cons t
    rw [FDLinv_cons_of h]
    rw [h] at ih
    split
    · rename_i hc
      simp [FDL_cons_cons, ih, hc]
    · cases R with
      | nil => simp [FDL_single] at ih ⊢; exact ih
      | cons m M => simp [FDL_cons_cons] at ih ⊢; exact ih

/-- The key property of `FDL⁻¹`: cutting `l ⁀ r` at newlines joins the last
line of `l` to the first line of `r`. (Steps 1–7 of the book's argument on
printed p.73.) -/
theorem FDLinv_append {l r : List Char} {P T : List (List Char)} {x h : List Char}
    (hl : FDLinv l = P ++ [x]) (hr : FDLinv r = h :: T) :
    FDLinv (l ++ r) = P ++ (x ++ h) :: T := by
  induction l generalizing P x with
  | nil =>
    obtain ⟨hP, hx⟩ := snoc_inj (show [] ++ [[]] = P ++ [x] from hl)
    subst hP hx; simpa using hr
  | cons c t ih =>
    obtain ⟨P', x', ht⟩ : ∃ P' x', FDLinv t = P' ++ [x'] :=
      ⟨_, _, (List.dropLast_concat_getLast (FDLinv_ne t)).symm⟩
    have ih' := ih ht
    obtain ⟨l0, R0, h0⟩ := FDLinv_eq_cons t
    obtain ⟨l1, R1, h1⟩ := FDLinv_eq_cons (t ++ r)
    rw [FDLinv_cons_of h0] at hl
    rw [List.cons_append, FDLinv_cons_of h1]
    rw [ht] at h0
    rw [h1] at ih'
    split
    · rename_i hc
      rw [if_pos hc, ← h0] at hl
      obtain ⟨hP, hx⟩ := snoc_inj (show ([] :: P') ++ [x'] = P ++ [x] by simpa using hl)
      subst hP hx
      rw [ih']; simp
    · rename_i hc
      rw [if_neg hc] at hl
      cases P' with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h0
        obtain ⟨hl0, hR0⟩ := h0
        rw [← hl0, ← hR0] at hl
        obtain ⟨hP, hx⟩ := snoc_inj (show [] ++ [c :: x'] = P ++ [x] by simpa using hl)
        subst hP hx
        simp only [List.nil_append, List.cons.injEq] at ih'
        obtain ⟨hl1, hR1⟩ := ih'
        rw [hl1, hR1]; simp
      | cons p P'' =>
        simp only [List.cons_append, List.cons.injEq] at h0
        obtain ⟨hl0, hR0⟩ := h0
        rw [← hl0, ← hR0] at hl
        obtain ⟨hP, hx⟩ := snoc_inj
          (show ((c :: p) :: P'') ++ [x'] = P ++ [x] by simpa using hl)
        subst hP hx
        simp only [List.cons_append, List.cons.injEq] at ih'
        obtain ⟨hl1, hR1⟩ := ih'
        rw [hl1, hR1]; simp

theorem FDLinv_FDL {L : List (List Char)} (hne : L ≠ []) (hd : ∀ l ∈ L, IsDispLine l) :
    FDLinv (FDL L) = L := by
  induction L with
  | nil => exact absurd rfl hne
  | cons l L ih =>
    -- FDL⁻¹ of a single display line is that line
    have single : ∀ m : List Char, IsDispLine m → FDLinv m = [m] := by
      intro m hm
      induction m with
      | nil => rfl
      | cons c t ih' =>
        simp only [IsDispLine, List.mem_cons, not_or] at hm
        rw [FDLinv_cons_of (ih' hm.2), if_neg (fun e => hm.1 e.symm)]
    cases L with
    | nil => exact single l (hd l (List.mem_cons_self ..))
    | cons m M =>
      rw [FDL_cons_cons]
      have hlD := hd l (List.mem_cons_self ..)
      have hrest := ih (List.cons_ne_nil _ _) (fun k hk => hd k (List.mem_cons_of_mem _ hk))
      have hnl : FDLinv (nl :: FDL (m :: M)) = [] :: m :: M := by
        rw [FDLinv_cons_of hrest, if_pos rfl]
      have := FDLinv_append (l := l) (P := []) (x := l) (by simpa using single l hlD) hnl
      simpa using this

/-- **Lemma 3:2.2a.** `FDL⁻¹ ⟨⟩ = ⟨⟨⟩⟩` -/
theorem FDLinv_nil : FDLinv [] = [[]] := rfl

/-- **Lemma 3:2.2b.** The characters of `L` contain `# L − 1` newlines. -/
theorem count_nl_FDL {L : List (List Char)} (hd : ∀ l ∈ L, IsDispLine l) :
    (FDL L).count nl = L.length - 1 := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    have hl : l.count nl = 0 := List.count_eq_zero.mpr (hd l (List.mem_cons_self ..))
    cases L with
    | nil => simpa [FDL_single] using hl
    | cons m M =>
      rw [FDL_cons_cons, List.count_append, List.count_cons,
        ih (fun k hk => hd k (List.mem_cons_of_mem _ hk))]
      simp [hl]

/-- **Lemma 3:2.2c.** If the last of two or more display lines is empty, the
characters end with a newline. -/
theorem last_FDL_nl {L : List (List Char)} (hlen : L.length ≥ 2) (hlast : L.getLast? = some []) :
    (FDL L).getLast? = some nl := by
  obtain ⟨L₁, hL⟩ : ∃ L₁, L = L₁ ++ [[]] := by
    have hne : L ≠ [] := by intro e; simp [e] at hlen
    refine ⟨L.dropLast, ?_⟩
    have := List.dropLast_concat_getLast hne
    rw [List.getLast?_eq_some_getLast hne] at hlast
    simp at hlast; rw [hlast] at this; exact this.symm
  subst hL
  have h₁ : L₁ ≠ [] := by intro e; simp [e] at hlen
  rw [FDL_append _ _ h₁ (by simp), FDL_single]
  simp

/-! ## The Doc2 state -/

/-- ```
┌─ Doc2 ───────────────────────────────────────────────
│ Doc1
│ UD
├──────────────────────────────────────────────────────
│ UDLines = FDL⁻¹ (Left_Char ⁀ Right_Char)
│ UDCurLine = last (FDL⁻¹ Left_Char) ⁀ first (FDL⁻¹ Right_Char)
│ UDCurY = #(FDL⁻¹ Left_Char)
│ UDCurX = #(last FDL⁻¹ Left_Char) + 1
└──────────────────────────────────────────────────────
``` -/
structure Doc2 extends Doc1, UD where
  udLines_eq : udLines = FDLinv (leftChar ++ rightChar)
  udCurLine_eq' : udCurLine =
    (FDLinv leftChar).getLast (FDLinv_ne _) ++ (FDLinv rightChar).head (FDLinv_ne _)
  udCurY_eq : udCurY = (FDLinv leftChar).length
  udCurX_eq : udCurX = ((FDLinv leftChar).getLast (FDLinv_ne _)).length + 1

/-- The display line sequence around the cursor: the lines before the cursor
line, the cursor line, and the lines after it. -/
theorem FDLinv_split (l r : List Char) :
    FDLinv (l ++ r) = (FDLinv l).dropLast ++
      ((FDLinv l).getLast (FDLinv_ne _) ++ (FDLinv r).head (FDLinv_ne _)) :: (FDLinv r).tail :=
  FDLinv_append (List.dropLast_concat_getLast (FDLinv_ne l)).symm
    (List.cons_head_tail (FDLinv_ne r)).symm

/-- **Doc2 and UD are consistent** (printed pp.73–74): every Doc1 state extends
to a Doc2 state. -/
def Doc2.ofDoc1 (d : Doc1) : Doc2 :=
  have hsplit := FDLinv_split d.leftChar d.rightChar
  have hlenL : (FDLinv d.leftChar).length ≥ 1 := by
    obtain ⟨l, R, h⟩ := FDLinv_eq_cons d.leftChar
    rw [h]; simp
  { toDoc1 := d
    udLines := FDLinv (d.leftChar ++ d.rightChar)
    udCurX := ((FDLinv d.leftChar).getLast (FDLinv_ne _)).length + 1
    udCurY := (FDLinv d.leftChar).length
    udCurLine := (FDLinv d.leftChar).getLast (FDLinv_ne _) ++
      (FDLinv d.rightChar).head (FDLinv_ne _)
    udLines_ne := FDLinv_ne _
    udLines_disp := FDLinv_disp _
    udCurLine_disp := by
      have h := FDLinv_disp (d.leftChar ++ d.rightChar)
      rw [hsplit] at h
      exact h _ (List.mem_append_right _ (List.mem_cons_self ..))
    udCurX_pos := by omega
    udCurY_pos := hlenL
    udCurY_le := by
      rw [hsplit]; simp; omega
    udCurLine_eq := by
      rw [hsplit, List.getElem?_append_right (by simp)]
      simp
    udCurX_le := by simp
    udLines_eq := rfl
    udCurLine_eq' := rfl
    udCurY_eq := rfl
    udCurX_eq := rfl }

/-- A Doc2 state is determined by its Doc1 part: the display components are
redundant (printed p.75). -/
theorem Doc2.ext {d e : Doc2} (h : d.toDoc1 = e.toDoc1) : d = e := by
  obtain ⟨d1, ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩, h1, h2, h3, h4⟩ := d
  obtain ⟨e1, ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩, g1, g2, g3, g4⟩ := e
  simp only at h
  subst h
  simp only at h1 h2 h3 h4 g1 g2 g3 g4
  subst h1 h2 h3 h4 g1 g2 g3 g4
  rfl

theorem Doc2.eq_ofDoc1 (d : Doc2) : d = Doc2.ofDoc1 d.toDoc1 := Doc2.ext rfl

/-! ## Initialisation -/

/-- `Initialize_Doc2 ≙ Initialize_Doc1 ∧ ΔDoc2` -/
def Initialize_Doc2 (d' : Doc2) : Prop := Initialize_Doc1 d'.toDoc1

/-- **Lemma 3:2.2d.** Initially the display is one empty line with the cursor
at (1, 1). (The book cites "Lemmas 3:1.3a and 3:2.1b", which do not exist,
[?208]; the result follows from Lemma 3:2.2a.) -/
theorem Initialize_Doc2_display {d' : Doc2} (h : Initialize_Doc2 d') :
    d'.udLines = [[]] ∧ d'.udCurLine = [] ∧ d'.udCurX = 1 ∧ d'.udCurY = 1 := by
  obtain ⟨hl, hr⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [d'.udLines_eq, hl, hr]; rfl
  · rw [d'.udCurLine_eq']; simp [hl, hr, FDLinv]
  · rw [d'.udCurX_eq]; simp [hl, FDLinv]
  · rw [d'.udCurY_eq]; simp [hl, FDLinv]

/-! ## §2.3 Promotion of the Doc1 operations -/

/-- The operations of §1.6, by name: `EditOps1 ≙ MoveOps ∪ DeleteOps ∪ InsertOp`.
(The book's `MoveOps` lists "MoveTopDoc, MoveBotDoc"; the operations are named
`MoveToTop`, `MoveToBot` in §1.6.) -/
inductive EditOp1 where
  | rightMoveChar | leftMoveChar | rightMoveWord | leftMoveWord
  | rightMoveLine | leftMoveLine | moveToTop | moveToBot
  | rightDeleteChar | leftDeleteChar | rightDeleteWord | leftDeleteWord
  | rightDeleteLine | leftDeleteLine
  | insertChar (x : Char)

/-- `OP_Doc1` for each name. The word and line moves are the corrected versions
(`…C_Doc1`, see `Doc1.lean`): as printed they are not total. -/
def EditOp1.doc1 : EditOp1 → TotalOp
  | .rightMoveChar => RightMoveChar_Doc1
  | .leftMoveChar => LeftMoveChar_Doc1
  | .rightMoveWord => RightMoveWordC_Doc1
  | .leftMoveWord => LeftMoveWordC_Doc1
  | .rightMoveLine => RightMoveLineC_Doc1
  | .leftMoveLine => LeftMoveLineC_Doc1
  | .moveToTop => MoveToTop_Doc1
  | .moveToBot => MoveToBot_Doc1
  | .rightDeleteChar => RightDeleteChar_Doc1
  | .leftDeleteChar => LeftDeleteChar_Doc1
  | .rightDeleteWord => RightDeleteWord_Doc1
  | .leftDeleteWord => LeftDeleteWord_Doc1
  | .rightDeleteLine => RightDeleteLine_Doc1
  | .leftDeleteLine => LeftDeleteLine_Doc1
  | .insertChar x => InsertChar_Doc1 x

theorem EditOp1.doc1_total : ∀ (op : EditOp1) (d : Doc1), ∃ d' rep, op.doc1 d d' rep
  | .rightMoveChar => RightMoveChar_Doc1_total
  | .leftMoveChar => LeftMoveChar_Doc1_total
  | .rightMoveWord => RightMoveWordC_Doc1_total
  | .leftMoveWord => LeftMoveWordC_Doc1_total
  | .rightMoveLine => RightMoveLineC_Doc1_total
  | .leftMoveLine => LeftMoveLineC_Doc1_total
  | .moveToTop => MoveToTop_Doc1_total
  | .moveToBot => MoveToBot_Doc1_total
  | .rightDeleteChar => RightDeleteChar_Doc1_total
  | .leftDeleteChar => LeftDeleteChar_Doc1_total
  | .rightDeleteWord => RightDeleteWord_Doc1_total
  | .leftDeleteWord => LeftDeleteWord_Doc1_total
  | .rightDeleteLine => RightDeleteLine_Doc1_total
  | .leftDeleteLine => LeftDeleteLine_Doc1_total
  | .insertChar x => InsertChar_Doc1_total x

/-- An operation on `ΔDoc2` with output `rep!`. -/
abbrev TotalOp2 := Doc2 → Doc2 → Report → Prop

/-- `∀ OP : EditOps1 • OP_Doc2 ≙ OP_Doc1 ∧ ΔDoc2` -/
def EditOp1.doc2 (op : EditOp1) : TotalOp2 := fun d d' rep => op.doc1 d.toDoc1 d'.toDoc1 rep

theorem EditOp1.doc2_total (op : EditOp1) (d : Doc2) : ∃ d' rep, op.doc2 d d' rep := by
  obtain ⟨d', rep, h⟩ := op.doc1_total d.toDoc1
  exact ⟨Doc2.ofDoc1 d', rep, h⟩

end ZEditor
