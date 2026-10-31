import ZEditor.Spec.Doc2

/-!
# Doc3: invariants on the unbounded display (Part Three, §3)

Printed pp.75–80 (PDF pp.78–83). Trailing spaces and trailing empty lines cannot
be seen on a terminal, so Doc3 forbids them (except around the cursor), and
promotes each Doc2 operation by following it with two tidying operations,
`RemTrailWS` and `RemTrailNL`.
-/

namespace ZEditor

/-! ## §3.1 The Doc3 state -/

/-- `visible l ⇔ (l ≠ ⟨⟩ ⇒ last l ≠ sp)`: no trailing space. -/
abbrev visible (l : List Char) : Prop := l ≠ [] → l.getLast? ≠ some sp

/-- `visibleseq L ⇔ (L ≠ ⟨⟨⟩⟩ ⇒ last L ≠ ⟨⟩)`: no trailing empty line.

Doc3 applies this to the lines *below* the cursor line, which may be `⟨⟩`,
where `last` is undefined. The book says the empty sequence "comprises a
visibleseq" (printed p.76), which is what `getLast?` gives here.

Note that the exemption for `⟨⟨⟩⟩` was written for the whole display (the
empty document, Lemma 3:3.1a). Applied to the lines below the cursor it allows
one invisible empty line to remain at the end of the document, contrary to the
stated reason for the invariant. The C (`RemTrailNL`, Appendix C p.v) removes it.

Decision D4 (`FINDINGS.md`) changes the rule to "at most one empty line at the end", so
that a file keeps its final newline; this file still states the printed rule. -/
abbrev visibleseq (L : List (List Char)) : Prop := L ≠ [[]] → L.getLast? ≠ some []

/-- `S after N = sucᴺ ; (1 .. N ⩤ S)`: drop the first `N` elements. -/
abbrev after (S : List α) (n : Nat) : List α := S.drop n

/-- `S for N`: the first `N` elements. -/
abbrev upto (S : List α) (n : Nat) : List α := S.take n

/-- ```
┌─ Doc3 ──────────────────────────────────────────────
│ Doc2
├─────────────────────────────────────────────────────
│ ∀ i : 1 .. # UDLines − {UDCurY} • visible (UDLines i)
│ visible (UDCurLine after UDCurX − 1)
│ visibleseq (UDLines after UDCurY)
└─────────────────────────────────────────────────────
``` -/
structure Doc3 extends Doc2 where
  lines_visible : ∀ (i : Nat) (h : i < udLines.length), i + 1 ≠ udCurY → visible udLines[i]
  cur_visible   : visible (after udCurLine (udCurX - 1))
  after_visible : visibleseq (after udLines udCurY)

/-- `Initialize_Doc3 ≙ Initialize_Doc2` -/
def Initialize_Doc3 (d' : Doc3) : Prop := Initialize_Doc2 d'.toDoc2

/-- **PO 0 for Doc3**: the initial state satisfies the Doc3 invariant. -/
theorem Initialize_Doc3_exists : ∃ d' : Doc3, Initialize_Doc3 d' := by
  let d2 := Doc2.ofDoc1 (Doc1.ofChars [] [])
  have hinit : Initialize_Doc2 d2 := ⟨rfl, rfl⟩
  obtain ⟨hl, hc, hx, hy⟩ := Initialize_Doc2_display hinit
  refine ⟨{ toDoc2 := d2, lines_visible := ?_, cur_visible := ?_, after_visible := ?_ }, hinit⟩
  · intro i hi hne
    simp only [hl] at hi ⊢
    have : i = 0 := by simpa using hi
    subst this; simp
    exact fun h => absurd rfl h
  · rw [hc]; exact fun h => absurd rfl h
  · rw [hl, hy]; simp

/-! ## §3.2 Two relations that tidy the display -/

/-- `L′ visible_prefix L ⇔ visible L′ ∧ rng (L − L′) ⊆ {sp}`, i.e. `L′` is `L`
without its trailing spaces. -/
def visiblePrefix (l' l : List Char) : Prop :=
  visible l' ∧ l' <+: l ∧ ∀ c ∈ l.drop l'.length, c = sp

/-- `L′ visibleseq_prefix L ⇔ visibleseq L′ ∧ rng (L − L′) ⊆ {⟨⟩}`.
(Declared on `seq₁ DispLine` but applied to the possibly empty lines below the
cursor.) -/
def visibleseqPrefix (L' L : List (List Char)) : Prop :=
  visibleseq L' ∧ L' <+: L ∧ ∀ m ∈ L.drop L'.length, m = []

/-- **Lemma 3:3.2a.** `visible_prefix` is reflexive on visible lines. -/
theorem visiblePrefix_refl {l : List Char} (h : visible l) : visiblePrefix l l :=
  ⟨h, List.prefix_refl l, by simp⟩

/-- **Lemma 3:3.2c.** `visibleseq_prefix` is reflexive on visibleseqs. -/
theorem visibleseqPrefix_refl {L : List (List Char)} (h : visibleseq L) :
    visibleseqPrefix L L :=
  ⟨h, List.prefix_refl L, by simp⟩

/-! ### Stripping a trailing run -/

theorem mem_takeWhile_p {p : α → Bool} : ∀ {l : List α} {x : α},
    x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    cases hpa : p a <;> simp [List.takeWhile, hpa] at h
    rcases h with rfl | h
    · exact hpa
    · exact mem_takeWhile_p h

/-- Remove the trailing elements satisfying `p`. -/
def stripEnd (p : α → Bool) (l : List α) : List α := (l.reverse.dropWhile p).reverse

theorem stripEnd_append (p : α → Bool) (l : List α) :
    l = stripEnd p l ++ (l.reverse.takeWhile p).reverse := by
  have h : l = (l.reverse.takeWhile p ++ l.reverse.dropWhile p).reverse := by
    rw [List.takeWhile_append_dropWhile, List.reverse_reverse]
  rw [List.reverse_append] at h
  exact h

theorem stripEnd_prefix (p : α → Bool) (l : List α) : stripEnd p l <+: l :=
  ⟨_, (stripEnd_append p l).symm⟩

theorem stripEnd_rest (p : α → Bool) (l : List α) :
    ∀ c ∈ l.drop (stripEnd p l).length, p c = true := by
  have ht : ∀ c ∈ (l.reverse.takeWhile p).reverse, p c = true :=
    fun c hc => mem_takeWhile_p (List.mem_reverse.mp hc)
  have h := stripEnd_append p l
  generalize stripEnd p l = s at h ⊢
  generalize (l.reverse.takeWhile p).reverse = t at h ht
  subst h
  simpa using ht

theorem stripEnd_last (p : α → Bool) (l : List α) :
    ∀ c, (stripEnd p l).getLast? = some c → p c = false := by
  intro c hc
  simp only [stripEnd, List.getLast?_reverse] at hc
  have := List.head?_dropWhile_not p l.reverse
  rw [hc] at this; simpa using this

def isSp (c : Char) : Bool := c == sp
def isNull (l : List Char) : Bool := l.isEmpty

/-- Strip trailing spaces from a line. -/
abbrev stripSp (l : List Char) : List Char := stripEnd isSp l

theorem visiblePrefix_stripSp (l : List Char) : visiblePrefix (stripSp l) l := by
  refine ⟨fun _ h => ?_, stripEnd_prefix _ l, fun c hc => ?_⟩
  · have := stripEnd_last isSp l sp h
    simp [isSp] at this
  · have := stripEnd_rest isSp l c hc
    simpa [isSp] using this

/-- Strip trailing empty lines. -/
abbrev stripNull (L : List (List Char)) : List (List Char) := stripEnd isNull L

theorem visibleseqPrefix_stripNull (L : List (List Char)) :
    visibleseqPrefix (stripNull L) L := by
  refine ⟨fun _ h => ?_, stripEnd_prefix _ L, fun m hm => ?_⟩
  · have := stripEnd_last isNull L [] h
    simp [isNull] at this
  · have := stripEnd_rest isNull L m hm
    simpa [isNull] using this

theorem stripSp_disp {l : List Char} (h : IsDispLine l) : IsDispLine (stripSp l) :=
  fun hm => h ((stripEnd_prefix _ l).subset hm)

/-! ### Building a Doc2 state from its display -/

/-- The Doc2 state with display lines `L` and cursor `(x, y)`. -/
def Doc2.ofDisplay (L : List (List Char)) (x y : Nat) : Doc2 :=
  let cur := L.getD (y - 1) []
  Doc2.ofDoc1 (Doc1.ofChars (FDL (L.take (y - 1) ++ [cur.take (x - 1)]))
    (FDL (cur.drop (x - 1) :: L.drop y)))

theorem FDLinv_FDL_snoc {A : List (List Char)} {a : List Char}
    (hA : ∀ l ∈ A, IsDispLine l) (ha : IsDispLine a) :
    FDLinv (FDL (A ++ [a])) = A ++ [a] :=
  FDLinv_FDL (by simp) (by
    intro l hl; rcases List.mem_append.mp hl with hl | hl
    · exact hA l hl
    · simp at hl; rw [hl]; exact ha)

/-- `ofDisplay` has the given display and cursor, when they satisfy `UD`. -/
theorem Doc2.ofDisplay_spec {L : List (List Char)} {x y : Nat}
    (hd : ∀ l ∈ L, IsDispLine l) (hy1 : 1 ≤ y) (hy2 : y ≤ L.length)
    (hx1 : 1 ≤ x) (hx2 : x ≤ (L.getD (y - 1) []).length + 1) :
    (Doc2.ofDisplay L x y).udLines = L ∧
    (Doc2.ofDisplay L x y).udCurX = x ∧ (Doc2.ofDisplay L x y).udCurY = y := by
  have hy' : y - 1 < L.length := by omega
  have hcur : L.getD (y - 1) [] = L[y - 1] := by simp [List.getD_eq_getElem?_getD, hy']
  have hcurD : IsDispLine L[y - 1] := hd _ (List.getElem_mem hy')
  have hA : ∀ l ∈ L.take (y - 1), IsDispLine l := fun l hl => hd l (List.mem_of_mem_take hl)
  have hB : ∀ l ∈ L.drop y, IsDispLine l := fun l hl => hd l (List.mem_of_mem_drop hl)
  have htake : IsDispLine (L[y - 1].take (x - 1)) :=
    fun hm => hcurD (List.mem_of_mem_take hm)
  have hdrop : IsDispLine (L[y - 1].drop (x - 1)) :=
    fun hm => hcurD (List.mem_of_mem_drop hm)
  have hleft := FDLinv_FDL_snoc hA htake
  have hright : FDLinv (FDL (L[y - 1].drop (x - 1) :: L.drop y)) =
      L[y - 1].drop (x - 1) :: L.drop y :=
    FDLinv_FDL (by simp) (by
      intro l hl; rcases List.mem_cons.mp hl with rfl | hl
      · exact hdrop
      · exact hB l hl)
  simp only [Doc2.ofDisplay, Doc2.ofDoc1, Doc1.ofChars, hcur]
  refine ⟨?_, ?_, ?_⟩
  · rw [FDLinv_append hleft hright, List.take_append_drop]
    conv => rhs; rw [← List.take_append_drop (y - 1) L]
    rw [List.drop_eq_getElem_cons hy']
    have : y - 1 + 1 = y := by omega
    rw [this]
  · simp [hleft]
    rw [hcur] at hx2; omega
  · simp only [hleft, List.length_append, List.length_take, List.length_singleton]; omega

/-! ### The tidying operations -/

/-- `FlagPrevCursor ≙ [ Left_Char : seq Char ; prevCP! : ℕ | prevCP! = # Left_Char ]` -/
def FlagPrevCursor (d : Doc2) : Nat := d.leftChar.length

/-- `prevUDCurY = #(FDL⁻¹((Left_Char ⁀ Right_Char) for prevCP?))`: the line that
held the cursor before the operation, found in the content after it. -/
def prevUDCurY (d : Doc2) (prevCP : Nat) : Nat :=
  (FDLinv (upto (d.leftChar ++ d.rightChar) prevCP)).length

/-- ```
┌─ RemTrailWS ─────────────────────────
│ ΔUD
│ prevCP? : ℕ
├──────────────────────────────────────
│ UDCurX′, UDCurY′ = UDCurX, UDCurY
│ {prevUDCurY} ⩤ UDLines′ = {prevUDCurY} ⩤ UDLines
│     prevUDCurY = UDCurY
│     UDCurLine′ for UDCurX − 1 = UDCurLine for UDCurX − 1
│     (UDCurLine′ after UDCurX − 1) visible_prefix (UDCurLine after UDCurX − 1)
│ ∨
│     prevUDCurY ≠ UDCurY
│     (UDLines′ prevUDCurY) visible_prefix (UDLines prevUDCurY)
│ where
│     prevUDCurY = #(FDL⁻¹((Left_Char ⁀ Right_Char) for prevCP?))
└──────────────────────────────────────
```
The schema is declared on `ΔUD`, but its `where` clause uses `Left_Char` and
`Right_Char`, which are not part of `UD`. It is used on Doc2 states (§3.3),
so we define it on `ΔDoc2`. -/
def RemTrailWS (prevCP : Nat) (d d' : Doc2) : Prop :=
  let p := prevUDCurY d prevCP
  d'.udCurX = d.udCurX ∧ d'.udCurY = d.udCurY ∧
  (∀ i, i + 1 ≠ p → d'.udLines[i]? = d.udLines[i]?) ∧
  ((p = d.udCurY ∧
      upto d'.udCurLine (d.udCurX - 1) = upto d.udCurLine (d.udCurX - 1) ∧
      visiblePrefix (after d'.udCurLine (d.udCurX - 1)) (after d.udCurLine (d.udCurX - 1))) ∨
   (p ≠ d.udCurY ∧ ∃ l' l, d'.udLines[p - 1]? = some l' ∧ d.udLines[p - 1]? = some l ∧
      visiblePrefix l' l))

/-- ```
┌─ RemTrailNL ─────────────────────────
│ ΔUD
├──────────────────────────────────────
│ UDCurX′, UDCurY′ = UDCurX, UDCurY
│ UDLines′ for UDCurY = UDLines for UDCurY
│ (UDLines′ after UDCurY) visibleseq_prefix (UDLines after UDCurY)
└──────────────────────────────────────
``` -/
def RemTrailNL (d d' : Doc2) : Prop :=
  d'.udCurX = d.udCurX ∧ d'.udCurY = d.udCurY ∧
  upto d'.udLines d.udCurY = upto d.udLines d.udCurY ∧
  visibleseqPrefix (after d'.udLines d.udCurY) (after d.udLines d.udCurY)

/-! ### The tidying operations are total

"We note that each *Rem* operation is total" (printed p.80). -/

theorem udCurLine_eq_getD (d : Doc2) : d.udCurLine = d.udLines.getD (d.udCurY - 1) [] := by
  have := d.udCurLine_eq
  simp [List.getD_eq_getElem?_getD, this]

theorem RemTrailNL_total (d : Doc2) : ∃ d', RemTrailNL d d' := by
  have hy1 := d.udCurY_pos
  have hy2 := d.udCurY_le
  obtain ⟨A, hA⟩ : ∃ A, A = d.udLines.take d.udCurY := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = d.udLines.drop d.udCurY := ⟨_, rfl⟩
  have hlenA : A.length = d.udCurY := by rw [hA]; simp; omega
  have hAB : d.udLines = A ++ B := by rw [hA, hB, List.take_append_drop]
  obtain ⟨L', hL'⟩ : ∃ L', L' = A ++ stripNull B := ⟨_, rfl⟩
  have hd : ∀ l ∈ L', IsDispLine l := by
    intro l hl
    rw [hL'] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact d.udLines_disp l (by rw [hAB]; exact List.mem_append_left _ hl)
    · exact d.udLines_disp l (by
        rw [hAB]; exact List.mem_append_right _ ((stripEnd_prefix _ B).subset hl))
  have hgetD : L'.getD (d.udCurY - 1) [] = d.udCurLine := by
    rw [udCurLine_eq_getD, hL', hAB, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  have hL'len : d.udCurY ≤ L'.length := by rw [hL']; simp; omega
  obtain ⟨hl, hx, hy⟩ := Doc2.ofDisplay_spec (L := L') (x := d.udCurX) hd hy1 hL'len
    d.udCurX_pos (by rw [hgetD]; exact d.udCurX_le)
  refine ⟨Doc2.ofDisplay L' d.udCurX d.udCurY, hx, hy, ?_, ?_⟩
  · rw [hl, hL', hAB]
    simp only [upto]
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
      ← hlenA, List.take_length]
  · rw [hl, hL', hAB]
    simp only [after]
    rw [← hlenA, List.drop_left, List.drop_left]
    exact visibleseqPrefix_stripNull B

/-- The number of lines of a prefix is at most the number of lines. -/
theorem FDLinv_length_take (C : List Char) (n : Nat) :
    (FDLinv (C.take n)).length ≤ (FDLinv C).length := by
  have h1 := count_nl_FDL (FDLinv_disp (C.take n))
  have h2 := count_nl_FDL (FDLinv_disp C)
  rw [FDL_FDLinv] at h1 h2
  have h3 : (C.take n).count nl ≤ C.count nl := (List.take_sublist n C).count_le _
  have p1 : (FDLinv (C.take n)).length ≥ 1 := by
    obtain ⟨_, _, h⟩ := FDLinv_eq_cons (C.take n); rw [h]; simp
  have p2 : (FDLinv C).length ≥ 1 := by
    obtain ⟨_, _, h⟩ := FDLinv_eq_cons C; rw [h]; simp
  omega

/-- Replacing one line leaves the others unchanged. -/
theorem getElem?_set_other {L : List (List Char)} {j : Nat} {m : List Char} {i : Nat}
    (h : i ≠ j) : (L.set j m)[i]? = L[i]? := by
  rw [List.getElem?_set]; split
  · omega
  · rfl

theorem set_disp {L : List (List Char)} {j : Nat} {m : List Char}
    (hL : ∀ l ∈ L, IsDispLine l) (hm : IsDispLine m) : ∀ l ∈ L.set j m, IsDispLine l := by
  intro l hl
  rcases List.mem_or_eq_of_mem_set hl with hl | rfl
  · exact hL l hl
  · exact hm

theorem RemTrailWS_total (prevCP : Nat) (d : Doc2) : ∃ d', RemTrailWS prevCP d d' := by
  have hy1 := d.udCurY_pos
  have hy2 := d.udCurY_le
  have hx1 := d.udCurX_pos
  have hx2 := d.udCurX_le
  obtain ⟨p, hp⟩ : ∃ p, p = prevUDCurY d prevCP := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    obtain ⟨_, _, h⟩ := FDLinv_eq_cons (upto (d.leftChar ++ d.rightChar) prevCP)
    rw [hp, prevUDCurY, h]; simp
  have hp2 : p ≤ d.udLines.length := by
    rw [hp, d.udLines_eq]; exact FDLinv_length_take _ _
  have hcur := udCurLine_eq_getD d
  have hcurD : IsDispLine d.udCurLine := d.udCurLine_disp
  simp only [RemTrailWS, ← hp]
  by_cases hpy : p = d.udCurY
  · -- the cursor stayed on its line: strip the spaces right of the cursor
    obtain ⟨cur', hcur'⟩ : ∃ c, c = upto d.udCurLine (d.udCurX - 1) ++
        stripSp (after d.udCurLine (d.udCurX - 1)) := ⟨_, rfl⟩
    have htakelen : (upto d.udCurLine (d.udCurX - 1)).length = d.udCurX - 1 := by
      simp [upto]; omega
    have hcur'D : IsDispLine cur' := by
      intro hm; rw [hcur'] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hcurD (List.mem_of_mem_take hm)
      · exact stripSp_disp (fun h => hcurD (List.mem_of_mem_drop h)) hm
    have hcur'len : d.udCurX - 1 ≤ cur'.length := by rw [hcur']; simp; omega
    obtain ⟨L', hL'⟩ : ∃ L', L' = d.udLines.set (d.udCurY - 1) cur' := ⟨_, rfl⟩
    have hd : ∀ l ∈ L', IsDispLine l := hL' ▸ set_disp d.udLines_disp hcur'D
    have hgetD : L'.getD (d.udCurY - 1) [] = cur' := by
      rw [hL', List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
    obtain ⟨hl, hx, hy⟩ := Doc2.ofDisplay_spec (L := L') (x := d.udCurX) (y := d.udCurY) hd hy1
      (by rw [hL', List.length_set]; omega) hx1 (by rw [hgetD]; omega)
    have hcl : (Doc2.ofDisplay L' d.udCurX d.udCurY).udCurLine = cur' := by
      rw [udCurLine_eq_getD, hl, hy, hgetD]
    refine ⟨Doc2.ofDisplay L' d.udCurX d.udCurY, hx, hy, ?_, .inl ⟨hpy, ?_, ?_⟩⟩
    · intro i hi
      rw [hl, hL', getElem?_set_other (by omega)]
    · rw [hcl, hcur']
      simp only [upto] at htakelen ⊢
      rw [List.take_append_of_le_length (by omega), List.take_take]
      simp
    · rw [hcl]
      have : after cur' (d.udCurX - 1) = stripSp (after d.udCurLine (d.udCurX - 1)) := by
        rw [hcur']
        simp only [upto, after] at htakelen ⊢
        rw [List.drop_append_of_le_length (by omega)]
        simp
      rw [this]; exact visiblePrefix_stripSp _
  · -- the cursor left its line: strip the trailing spaces of the previous cursor line
    have hp' : p - 1 < d.udLines.length := by omega
    obtain ⟨old, hold⟩ : ∃ o, o = d.udLines[p - 1] := ⟨_, rfl⟩
    obtain ⟨L', hL'⟩ : ∃ L', L' = d.udLines.set (p - 1) (stripSp old) := ⟨_, rfl⟩
    have hd : ∀ l ∈ L', IsDispLine l := hL' ▸ set_disp d.udLines_disp
      (stripSp_disp (hold ▸ d.udLines_disp _ (List.getElem_mem hp')))
    have hgetD : L'.getD (d.udCurY - 1) [] = d.udCurLine := by
      rw [hcur, hL', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        getElem?_set_other (by omega)]
    obtain ⟨hl, hx, hy⟩ := Doc2.ofDisplay_spec (L := L') (x := d.udCurX) (y := d.udCurY) hd hy1
      (by rw [hL', List.length_set]; omega) hx1 (by rw [hgetD]; exact hx2)
    refine ⟨Doc2.ofDisplay L' d.udCurX d.udCurY, hx, hy, ?_,
      .inr ⟨hpy, stripSp old, old, ?_, ?_, visiblePrefix_stripSp old⟩⟩
    · intro i hi
      rw [hl, hL', getElem?_set_other (by omega)]
    · rw [hl, hL', List.getElem?_set_self hp']
    · rw [hold]; simp [hp']

/-! ## §3.3 Promotion of the Doc2 operations -/

/-- `∀ OP : EditOps1 • OP_Doc3 ≙ FlagPrevCursor ; OP_Doc2 ; RemTrailWS ; RemTrailNL`,
on Doc3 states. -/
def EditOp1.doc3 (op : EditOp1) (d d' : Doc3) (rep : Report) : Prop :=
  ∃ m₁ m₂, op.doc2 d.toDoc2 m₁ rep ∧ RemTrailWS (FlagPrevCursor d.toDoc2) m₁ m₂ ∧
    RemTrailNL m₂ d'.toDoc2

/-- The composition `OP_Doc2 ; RemTrailWS ; RemTrailNL` always has an outcome
as a Doc2 state. (Whether that outcome satisfies the Doc3 invariant, the
book's PO 1 for Doc3, is the next thing to prove.) -/
theorem EditOp1.doc3_composition_total (op : EditOp1) (d : Doc3) :
    ∃ m₁ m₂ m₃ rep, op.doc2 d.toDoc2 m₁ rep ∧
      RemTrailWS (FlagPrevCursor d.toDoc2) m₁ m₂ ∧ RemTrailNL m₂ m₃ := by
  obtain ⟨m₁, rep, h₁⟩ := op.doc2_total d.toDoc2
  obtain ⟨m₂, h₂⟩ := RemTrailWS_total (FlagPrevCursor d.toDoc2) m₁
  obtain ⟨m₃, h₃⟩ := RemTrailNL_total m₂
  exact ⟨m₁, m₂, m₃, rep, h₁, h₂, h₃⟩

end ZEditor
