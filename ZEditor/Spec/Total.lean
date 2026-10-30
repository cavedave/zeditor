import ZEditor.Spec.Unique

/-!
# Every document has word and line views, and the operations are total

`FW` and `FL` are declared as bijections (`⤖`) in the book; `Unique.lean` proves
they are one-to-one. Here we prove they are onto: every character sequence has a
word view and a line view (`words`, `lines`), so every pair of character
sequences is a `Doc1` state (`Doc1.ofChars`).

With that we prove that the corrected operations of §1.6 are total: for every
state there is an outcome. Together with `leftMoveWord_Doc1_stuck` this shows
that the word and line moves, as printed, are exactly where the book's claim of
totality fails.
-/

namespace ZEditor

/-! ## Cutting a list into blocks -/

section cut

variable {α β : Type} (cls : α → β) (single : β → Prop)

/-- Add `a` to the front of a block cutting, joining the first block when the
classes match and the class is not `single`. -/
def push [DecidableEq β] [DecidablePred single] (a : α) : List (List α) → List (List α)
  | (b :: v) :: R =>
    if cls a = cls b ∧ ¬ single (cls a) then (a :: b :: v) :: R
    else [a] :: (b :: v) :: R
  | R => [a] :: R

/-- Cut a list into maximal blocks. This is `FW⁻¹` / `FL⁻¹`. -/
def cut [DecidableEq β] [DecidablePred single] : List α → List (List α)
  | [] => []
  | a :: t => push cls single a (cut t)

variable {cls single}

theorem flatten_push [DecidableEq β] [DecidablePred single] (a : α) (W : List (List α)) :
    (push cls single a W).flatten = a :: W.flatten := by
  unfold push
  split
  · split <;> simp
  · simp

theorem flatten_cut [DecidableEq β] [DecidablePred single] (C : List α) :
    (cut cls single C).flatten = C := by
  induction C with
  | nil => rfl
  | cons a t ih => simp [cut, flatten_push, ih]

theorem adjacent_cons_cons (x y : α) (R : List α) :
    adjacent (x :: y :: R) = (x, y) :: adjacent (y :: R) := by
  simp [adjacent]

theorem adjacent_single (x : α) : adjacent [x] = [] := by
  simp [adjacent]

theorem mem_of_adjacent {S : List α} {p : α × α} (hp : p ∈ adjacent S) :
    p.1 ∈ S ∧ p.2 ∈ S :=
  ⟨(List.of_mem_zip hp).1, List.mem_of_mem_tail (List.of_mem_zip hp).2⟩

theorem adjacent_append_left {A B : List α} {p : α × α} (hp : p ∈ adjacent A) :
    p ∈ adjacent (A ++ B) := by
  induction A with
  | nil => simp [adjacent] at hp
  | cons x A ih =>
    cases A with
    | nil => simp [adjacent_single] at hp
    | cons y A =>
      rw [adjacent_cons_cons] at hp
      rw [List.cons_append, List.cons_append, adjacent_cons_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (by simpa using ih hp)

/-- A prefix of a block cutting is a block cutting. -/
theorem Blocks.of_append_left {A B : List (List α)}
    (h : Blocks cls single (A ++ B)) : Blocks cls single A where
  ne w hw := h.ne w (List.mem_append_left _ hw)
  homog w hw := h.homog w (List.mem_append_left _ hw)
  singleLen w hw := h.singleLen w (List.mem_append_left _ hw)
  adj p hp := h.adj p (adjacent_append_left hp)

theorem Blocks.dropLast {W : List (List α)} (h : Blocks cls single W) :
    Blocks cls single W.dropLast := by
  cases W with
  | nil => exact h
  | cons w R =>
    apply Blocks.of_append_left (B := [(w :: R).getLast (by simp)])
    rw [List.dropLast_concat_getLast]; exact h

/-- The new first block `[a]` or `a :: b :: v` is a good block. -/
theorem Blocks.push [DecidableEq β] [DecidablePred single] (a : α) {W : List (List α)}
    (h : Blocks cls single W) :
    Blocks cls single (push cls single a W) := by
  match W, h with
  | [], _ =>
    simp only [ZEditor.push]
    exact {
      ne := by simp
      homog := by simp
      singleLen := by simp
      adj := by simp [adjacent_single] }
  | [] :: R, h => exact absurd rfl (h.ne [] (List.mem_cons_self ..))
  | (b :: v) :: R, h =>
    have hbv : b :: v ∈ (b :: v) :: R := List.mem_cons_self ..
    have hb : b ∈ b :: v := List.mem_cons_self ..
    simp only [ZEditor.push]
    split
    · -- join: a goes into the first block
      rename_i hjoin
      obtain ⟨hab, hns⟩ := hjoin
      have hcls : ∀ x ∈ a :: b :: v, cls x = cls b := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hab
        · exact h.homog _ hbv x hx b hb
      exact {
        ne := by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · simp
          · exact h.ne w (List.mem_cons_of_mem _ hw)
        homog := by
          intro w hw x hx y hy
          rcases List.mem_cons.mp hw with rfl | hw
          · rw [hcls x hx, hcls y hy]
          · exact h.homog w (List.mem_cons_of_mem _ hw) x hx y hy
        singleLen := by
          intro w hw x hx hs
          rcases List.mem_cons.mp hw with rfl | hw
          · rw [hcls x hx, ← hab] at hs; exact absurd hs hns
          · exact h.singleLen w (List.mem_cons_of_mem _ hw) x hx hs
        adj := by
          intro p hp x hx y hy hxy
          cases R with
          | nil => simp [adjacent_single] at hp
          | cons r R =>
            rw [adjacent_cons_cons] at hp
            rcases List.mem_cons.mp hp with rfl | hp
            · rw [hcls x hx] at hxy ⊢
              exact h.adj (b :: v, r) (by simp [adjacent]) b hb y hy hxy
            · exact h.adj p (by rw [adjacent_cons_cons]; exact List.mem_cons_of_mem _ hp)
                x hx y hy hxy }
    · -- new block [a]
      rename_i hnew
      exact {
        ne := by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · simp
          · exact h.ne w hw
        homog := by
          intro w hw x hx y hy
          rcases List.mem_cons.mp hw with rfl | hw
          · simp at hx hy; rw [hx, hy]
          · exact h.homog w hw x hx y hy
        singleLen := by
          intro w hw x hx hs
          rcases List.mem_cons.mp hw with rfl | hw
          · rfl
          · exact h.singleLen w hw x hx hs
        adj := by
          intro p hp x hx y hy hxy
          rw [adjacent_cons_cons] at hp
          rcases List.mem_cons.mp hp with rfl | hp
          · simp at hx; subst hx
            have : cls x = cls b := hxy.trans (h.homog _ hbv y hy b hb)
            exact Decidable.byContradiction fun hns => hnew ⟨this, hns⟩
          · exact h.adj p hp x hx y hy hxy }

theorem Blocks.cut [DecidableEq β] [DecidablePred single] (C : List α) :
    Blocks cls single (ZEditor.cut cls single C) := by
  induction C with
  | nil => exact ⟨by simp [ZEditor.cut], by simp [ZEditor.cut], by simp [ZEditor.cut],
      by simp [ZEditor.cut, adjacent]⟩
  | cons a t ih => exact ih.push a

end cut

/-! ## Words and lines from characters -/

theorem wcls_zero {c : Char} : wcls c = 0 ↔ c = sp := by
  unfold wcls; split <;> (try split) <;> simp_all

theorem wcls_one {c : Char} : wcls c = 1 ↔ NonWhiteSpace c := by
  unfold wcls; split <;> (try split) <;> simp_all [NonWhiteSpace]

theorem wcls_two {c : Char} : wcls c = 2 ↔ c = nl := by
  unfold wcls; split <;> (try split) <;> simp_all [sp_ne_nl]

theorem wcls_lt (c : Char) : wcls c < 3 := by
  unfold wcls; split <;> (try split) <;> simp

theorem Blocks.docWordSeq {W : List (List Char)} (h : Blocks wcls (· = 2) W) :
    DocWordSeq W := by
  have isWord : ∀ w ∈ W, IsWord w := by
    intro w hw
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w (h.ne w hw)
    have hall : ∀ c ∈ w, wcls c = wcls a := fun c hc => h.homog w hw c hc a ha
    have := wcls_lt a
    match hk : wcls a with
    | 0 => exact .inl ⟨h.ne w hw, fun c hc => wcls_zero.mp ((hall c hc).trans hk)⟩
    | 1 => exact .inr (.inl ⟨h.ne w hw, fun c hc => wcls_one.mp ((hall c hc).trans hk)⟩)
    | 2 =>
      have hlen := h.singleLen w hw a ha hk
      match w, hlen with
      | [x], _ =>
        simp at ha; subst ha
        exact .inr (.inr (by rw [wcls_two.mp hk]))
    | k + 3 => omega
  refine ⟨isWord, fun p hp => ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩⟩
  all_goals
    obtain ⟨hp1, hp2⟩ := mem_of_adjacent hp
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (h.ne _ hp1)
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (h.ne _ hp2)
  · have hs := h.adj p hp a ha b hb (by rw [wcls_zero.mpr (h1 a ha), wcls_zero.mpr (h2 b hb)])
    rw [wcls_zero.mpr (h1 a ha)] at hs; simp at hs
  · have hs := h.adj p hp a ha b hb (by rw [wcls_one.mpr (h1 a ha), wcls_one.mpr (h2 b hb)])
    rw [wcls_one.mpr (h1 a ha)] at hs; simp at hs

theorem lcls_one {c : Char} : lcls c = 1 ↔ c = nl := by
  unfold lcls; split <;> simp_all

theorem lcls_zero {c : Char} : lcls c = 0 ↔ c ≠ nl := by
  unfold lcls; split <;> simp_all

theorem Blocks.docLineSeq {L : List (List Char)} (h : Blocks lcls (· = 1) L) :
    DocLineSeq L := by
  -- a block containing a newline is exactly ⟨nl⟩
  have nlBlock : ∀ l ∈ L, ∀ a ∈ l, a = nl → l = [nl] := by
    intro l hl a ha hanl
    have hlen := h.singleLen l hl a ha (lcls_one.mpr hanl)
    match l, hlen with
    | [x], _ => simp at ha; rw [← ha, hanl]
  have isLine : ∀ l ∈ L, IsLine l := by
    intro l hl
    by_cases hnl : nl ∈ l
    · exact .inr (nlBlock l hl nl hnl rfl)
    · exact .inl ⟨h.ne l hl, hnl⟩
  refine ⟨isLine, fun p hp hp1 => ?_⟩
  obtain ⟨hm1, hm2⟩ := mem_of_adjacent hp
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (h.ne _ hm1)
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (h.ne _ hm2)
  have hanl : a ≠ nl := fun e => hp1 (nlBlock _ hm1 a ha e)
  by_cases hbnl : b = nl
  · exact nlBlock _ hm2 b hb hbnl
  · have hs := h.adj p hp a ha b hb (by rw [lcls_zero.mpr hanl, lcls_zero.mpr hbnl])
    rw [lcls_zero.mpr hanl] at hs; simp at hs

/-- `FW⁻¹`: the word view of a character sequence. -/
def words (C : List Char) : List (List Char) := cut wcls (· = 2) C

/-- `FL⁻¹`: the line view of a character sequence. -/
def lines (C : List Char) : List (List Char) := cut lcls (· = 1) C

theorem words_ok (C : List Char) : DocWordSeq (words C) := (Blocks.cut C).docWordSeq
theorem lines_ok (C : List Char) : DocLineSeq (lines C) := (Blocks.cut C).docLineSeq
theorem FW_words (C : List Char) : FW (words C) = C := flatten_cut C
theorem FL_lines (C : List Char) : FL (lines C) = C := flatten_cut C

/-- `FW⁻¹ (FW W) = W` for every word sequence. -/
theorem words_FW {W : List (List Char)} (h : DocWordSeq W) : words (FW W) = W :=
  DocWordSeq.unique (words_ok _) h (FW_words _)

theorem lines_FL {L : List (List Char)} (h : DocLineSeq L) : lines (FL L) = L :=
  DocLineSeq.unique (lines_ok _) h (FL_lines _)

/-- The `Doc1` state with the given characters left and right of the cursor. -/
def Doc1.ofChars (l r : List Char) : Doc1 where
  leftChar  := l
  rightChar := r
  leftWord  := ZEditor.words l
  rightWord := ZEditor.words r
  leftLine  := ZEditor.lines l
  rightLine := ZEditor.lines r
  leftWord_ok  := words_ok l
  rightWord_ok := words_ok r
  leftLine_ok  := lines_ok l
  rightLine_ok := lines_ok r
  left_inv  := ⟨(FW_words l).symm, by rw [FW_words, FL_lines]⟩
  right_inv := ⟨(FW_words r).symm, by rw [FW_words, FL_lines]⟩

theorem Doc1.eq_ofChars (d : Doc1) : d = Doc1.ofChars d.leftChar d.rightChar :=
  Doc1.ext_chars rfl

/-! ## Mirror -/

/-- The mirror image of a state. -/
def Doc1.mirror (d : Doc1) : Doc1 := Doc1.ofChars d.rightChar.reverse d.leftChar.reverse

theorem mirror_mirror_self (d : Doc1) : Mirror d d.mirror := ⟨rfl, rfl⟩

/-- **`Mirror ; Mirror ≙ ΞDoc1`**, in full. -/
theorem mirror_mirror_iff {d d' : Doc1} : (Mirror ⨾ Mirror) d d' ↔ d' = d := by
  constructor
  · exact mirror_mirror
  · intro h
    rw [h]
    exact ⟨d.mirror, mirror_mirror_self d, by simp [Mirror, Doc1.mirror, Doc1.ofChars]⟩

/-- A `Right` operation has an outcome whenever the operation has one on the
mirrored state. -/
theorem Right_exists {op : Op} {d : Doc1} (h : ∃ m', op d.mirror m') :
    ∃ d', Right op d d' := by
  obtain ⟨m', hm⟩ := h
  exact ⟨m'.mirror, m', ⟨d.mirror, mirror_mirror_self d, hm⟩, mirror_mirror_self m'⟩

/-! ## The basic operations have outcomes -/

theorem leftChar_ne_nil_word {d : Doc1} (h : d.leftChar ≠ []) : d.leftWord ≠ [] := by
  intro e; apply h; rw [d.left_inv.1, e]; rfl

theorem leftChar_ne_nil_line {d : Doc1} (h : d.leftChar ≠ []) : d.leftLine ≠ [] := by
  intro e; apply h; rw [d.left_inv.1, d.left_inv.2, e]; rfl

theorem FW_dropLast {W : List (List Char)} (h : W ≠ []) :
    FW W = FW W.dropLast ++ W.getLast h := by
  conv => lhs; rw [← List.dropLast_concat_getLast h]
  simp [FW]

theorem FL_dropLast {L : List (List Char)} (h : L ≠ []) :
    FL L = FL L.dropLast ++ L.getLast h := by
  conv => lhs; rw [← List.dropLast_concat_getLast h]
  simp [FL]

theorem MvChar_exists {d : Doc1} (h : d.leftChar ≠ []) : ∃ d', MvChar d d' := by
  refine ⟨Doc1.ofChars d.leftChar.dropLast (d.leftChar.getLast h :: d.rightChar),
    ?_, h, rfl⟩
  simp only [XiCont, Doc1.chars, Doc1.ofChars]
  conv => lhs; rw [← List.dropLast_concat_getLast h]
  simp

theorem MvWordC_exists {d : Doc1} (h : d.leftChar ≠ []) : ∃ d', MvWordC d d' := by
  have hw := leftChar_ne_nil_word h
  refine ⟨Doc1.ofChars (FW d.leftWord.dropLast) (d.leftWord.getLast hw ++ d.rightChar),
    ?_, hw, ?_⟩
  · simp only [XiContDoc1, XiCont, Doc1.chars, Doc1.ofChars]
    rw [d.left_inv.1, FW_dropLast hw, List.append_assoc]
  · exact words_FW (Blocks.dropLast d.leftWord_ok.blocks).docWordSeq

theorem MvLineC_exists {d : Doc1} (h : d.leftChar ≠ []) : ∃ d', MvLineC d d' := by
  have hl := leftChar_ne_nil_line h
  refine ⟨Doc1.ofChars (FL d.leftLine.dropLast) (d.leftLine.getLast hl ++ d.rightChar),
    ?_, hl, ?_⟩
  · simp only [XiContDoc1, XiCont, Doc1.chars, Doc1.ofChars]
    rw [d.left_inv.1, d.left_inv.2, FL_dropLast hl, List.append_assoc]
  · exact lines_FL (Blocks.dropLast d.leftLine_ok.blocks).docLineSeq

theorem DelChar_exists {d : Doc1} (h : d.leftChar ≠ []) : ∃ d', DelChar d d' :=
  ⟨Doc1.ofChars d.leftChar.dropLast d.rightChar, h, rfl, rfl⟩

theorem DelWord_exists {d : Doc1} (h : d.leftChar ≠ []) : ∃ d', DelWord d d' := by
  have hw := leftChar_ne_nil_word h
  refine ⟨Doc1.ofChars (FW d.leftWord.dropLast) d.rightChar, hw, ?_, ?_⟩
  · exact words_FW (Blocks.dropLast d.leftWord_ok.blocks).docWordSeq
  · show words d.rightChar = d.rightWord
    rw [d.right_inv.1]; exact words_FW d.rightWord_ok

theorem DelLine_exists {d : Doc1} (h : d.leftChar ≠ []) : ∃ d', DelLine d d' := by
  have hl := leftChar_ne_nil_line h
  refine ⟨Doc1.ofChars (FL d.leftLine.dropLast) d.rightChar, hl, ?_, ?_⟩
  · exact lines_FL (Blocks.dropLast d.leftLine_ok.blocks).docLineSeq
  · show lines d.rightChar = d.rightLine
    rw [d.right_inv.1, d.right_inv.2]; exact lines_FL d.rightLine_ok

theorem MvBottom_exists {d : Doc1} (h : d.rightChar ≠ []) : ∃ d', MvBottom d d' :=
  ⟨Doc1.ofChars (d.leftChar ++ d.rightChar) [], by simp [XiCont, Doc1.chars, Doc1.ofChars],
    h, rfl⟩

/-! ## The total operations are total -/

/-- An operation with outcome whenever the document is not empty on the left,
combined with `ErrorTopOfDoc`, always has an outcome. -/
theorem orError_top_total {op : Op} (h : ∀ d : Doc1, d.leftChar ≠ [] → ∃ d', op d d')
    (d : Doc1) : ∃ d' rep, orError op ErrorTopOfDoc d d' rep := by
  by_cases hl : d.leftChar = []
  · exact ⟨d, _, .inr ⟨rfl, hl, rfl⟩⟩
  · obtain ⟨d', hd'⟩ := h d hl
    exact ⟨d', _, .inl ⟨hd', rfl⟩⟩

theorem orError_bot_total {op : Op} (h : ∀ d : Doc1, d.rightChar ≠ [] → ∃ d', op d d')
    (d : Doc1) : ∃ d' rep, orError op ErrorBotOfDoc d d' rep := by
  by_cases hr : d.rightChar = []
  · exact ⟨d, _, .inr ⟨rfl, hr, rfl⟩⟩
  · obtain ⟨d', hd'⟩ := h d hr
    exact ⟨d', _, .inl ⟨hd', rfl⟩⟩

/-- Mirroring turns "not empty on the right" into "not empty on the left". -/
theorem Right_of_left {op : Op} (h : ∀ d : Doc1, d.leftChar ≠ [] → ∃ d', op d d')
    (d : Doc1) (hr : d.rightChar ≠ []) : ∃ d', Right op d d' :=
  Right_exists (h d.mirror (by simpa [Doc1.mirror, Doc1.ofChars] using hr))

theorem LeftMoveChar_Doc1_total : ∀ d, ∃ d' rep, LeftMoveChar_Doc1 d d' rep :=
  orError_top_total  @MvChar_exists
theorem RightMoveChar_Doc1_total : ∀ d, ∃ d' rep, RightMoveChar_Doc1 d d' rep :=
  orError_bot_total (Right_of_left @MvChar_exists)
theorem LeftDeleteChar_Doc1_total : ∀ d, ∃ d' rep, LeftDeleteChar_Doc1 d d' rep :=
  orError_top_total @DelChar_exists
theorem RightDeleteChar_Doc1_total : ∀ d, ∃ d' rep, RightDeleteChar_Doc1 d d' rep :=
  orError_bot_total (Right_of_left @DelChar_exists)
theorem LeftDeleteWord_Doc1_total : ∀ d, ∃ d' rep, LeftDeleteWord_Doc1 d d' rep :=
  orError_top_total @DelWord_exists
theorem RightDeleteWord_Doc1_total : ∀ d, ∃ d' rep, RightDeleteWord_Doc1 d d' rep :=
  orError_bot_total (Right_of_left @DelWord_exists)
theorem LeftDeleteLine_Doc1_total : ∀ d, ∃ d' rep, LeftDeleteLine_Doc1 d d' rep :=
  orError_top_total @DelLine_exists
theorem RightDeleteLine_Doc1_total : ∀ d, ∃ d' rep, RightDeleteLine_Doc1 d d' rep :=
  orError_bot_total (Right_of_left @DelLine_exists)

/-- The word and line moves are total in the reading the C implements. -/
theorem LeftMoveWordC_Doc1_total : ∀ d, ∃ d' rep, LeftMoveWordC_Doc1 d d' rep :=
  orError_top_total @MvWordC_exists
theorem RightMoveWordC_Doc1_total : ∀ d, ∃ d' rep, RightMoveWordC_Doc1 d d' rep :=
  orError_bot_total (Right_of_left @MvWordC_exists)
theorem LeftMoveLineC_Doc1_total : ∀ d, ∃ d' rep, LeftMoveLineC_Doc1 d d' rep :=
  orError_top_total @MvLineC_exists
theorem RightMoveLineC_Doc1_total : ∀ d, ∃ d' rep, RightMoveLineC_Doc1 d d' rep :=
  orError_bot_total (Right_of_left @MvLineC_exists)

theorem MoveToBot_Doc1_total : ∀ d, ∃ d' rep, MoveToBot_Doc1 d d' rep :=
  orError_bot_total @MvBottom_exists

theorem MoveToTop_Doc1_total : ∀ d, ∃ d' rep, MoveToTop_Doc1 d d' rep :=
  orError_top_total fun d hl =>
    Right_exists (MvBottom_exists (by simpa [Doc1.mirror, Doc1.ofChars] using hl))

/-- Insertion is total because `ErrorFull` has no precondition. -/
theorem InsertChar_Doc1_total (x : Char) (d : Doc1) :
    ∃ d' rep, InsertChar_Doc1 x d d' rep :=
  ⟨d, _, .inr ⟨rfl, rfl⟩⟩

end ZEditor
