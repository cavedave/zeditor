import ZEditor.Spec.Doc1

/-!
# Uniqueness of the word and line views (Corollaries 3:1.2a and 3:1.2c)

The book claims that two word sequences (or line sequences) with the same
characters are equal, "as a direct consequence of" the definitions of
`DocWordSeq` and `DocLineSeq`. Both definitions have the same shape: a list is
cut into non-empty blocks, each of one character class, and two adjacent blocks
may share a class only if it is a class whose blocks are single characters
(the newline). We prove uniqueness once for that shape (`Blocks.unique`) and
then apply it to words and lines.
-/

namespace ZEditor

/-- `W` cuts a list into blocks of one class each. Blocks of a `single` class have
length one, and adjacent blocks may share a class only if it is `single`. -/
structure Blocks {α β : Type} (cls : α → β) (single : β → Prop)
    (W : List (List α)) : Prop where
  ne        : ∀ w ∈ W, w ≠ []
  homog     : ∀ w ∈ W, ∀ a ∈ w, ∀ b ∈ w, cls a = cls b
  singleLen : ∀ w ∈ W, ∀ a ∈ w, single (cls a) → w.length = 1
  adj       : ∀ p ∈ adjacent W, ∀ a ∈ p.1, ∀ b ∈ p.2, cls a = cls b → single (cls a)

namespace Blocks

variable {α β : Type} {cls : α → β} {single : β → Prop}

theorem tail {w : List α} {W : List (List α)} (h : Blocks cls single (w :: W)) :
    Blocks cls single W where
  ne w hw := h.ne w (List.mem_cons_of_mem _ hw)
  homog w hw := h.homog w (List.mem_cons_of_mem _ hw)
  singleLen w hw := h.singleLen w (List.mem_cons_of_mem _ hw)
  adj p hp := by
    cases W with
    | nil => simp [adjacent] at hp
    | cons v W =>
      apply h.adj p
      simp only [adjacent, List.tail_cons, List.zip_cons_cons] at hp ⊢
      exact List.mem_cons_of_mem _ hp

/-- The first character of a flattened block list lies in the first block. -/
theorem head_mem {W : List (List α)} {x : α} {t : List α}
    (h : Blocks cls single W) (hf : W.flatten = x :: t) :
    ∃ v R, W = v :: R ∧ x ∈ v := by
  cases W with
  | nil => simp at hf
  | cons v R =>
    refine ⟨v, R, rfl, ?_⟩
    cases v with
    | nil => exact absurd rfl (h.ne [] (List.mem_cons_self ..))
    | cons y v =>
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
      rw [hf.1]; exact List.mem_cons_self ..

/-- The first block of one cutting cannot be shorter than the first block of
another cutting of the same list. -/
theorem not_shorter {w₁ w₂ : List α} {R₁ R₂ : List (List α)}
    (h₁ : Blocks cls single (w₁ :: R₁)) (h₂ : Blocks cls single (w₂ :: R₂))
    (heq : w₁ ++ R₁.flatten = w₂ ++ R₂.flatten) : ¬ w₁.length < w₂.length := by
  intro hlt
  rcases List.append_eq_append_iff.mp heq with ⟨s, hw₂, hR₁⟩ | ⟨s, hw₁, _⟩
  · -- w₂ = w₁ ++ s, and s continues into the next block of the first cutting
    cases s with
    | nil => simp [hw₂] at hlt
    | cons x s =>
      obtain ⟨v, R, rfl, hxv⟩ := h₁.tail.head_mem hR₁
      have hw₁ne := h₁.ne w₁ (List.mem_cons_self ..)
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w₁ hw₁ne
      have haw₂ : a ∈ w₂ := by rw [hw₂]; exact List.mem_append_left _ ha
      have hxw₂ : x ∈ w₂ := by rw [hw₂]; simp
      have hcls : cls a = cls x := h₂.homog w₂ (List.mem_cons_self ..) a haw₂ x hxw₂
      have hsingle : single (cls a) :=
        h₁.adj (w₁, v) (by simp [adjacent]) a ha x hxv hcls
      have hlen := h₂.singleLen w₂ (List.mem_cons_self ..) a haw₂ hsingle
      have : w₁.length ≥ 1 := by
        cases w₁ with
        | nil => exact absurd rfl hw₁ne
        | cons _ _ => simp
      omega
  · -- w₁ = w₂ ++ s makes w₁ at least as long as w₂
    rw [hw₁] at hlt; simp at hlt; omega

/-- **Uniqueness.** Two block cuttings of the same list are equal. -/
theorem unique {W₁ W₂ : List (List α)}
    (h₁ : Blocks cls single W₁) (h₂ : Blocks cls single W₂)
    (heq : W₁.flatten = W₂.flatten) : W₁ = W₂ := by
  induction W₁ generalizing W₂ with
  | nil =>
    cases W₂ with
    | nil => rfl
    | cons w R =>
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil w (h₂.ne w (List.mem_cons_self ..))
      have : x ∈ (w :: R).flatten := List.mem_flatten.mpr ⟨w, List.mem_cons_self .., hx⟩
      simp [← heq] at this
  | cons w₁ R₁ ih =>
    cases W₂ with
    | nil =>
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil w₁ (h₁.ne w₁ (List.mem_cons_self ..))
      have : x ∈ (w₁ :: R₁).flatten := List.mem_flatten.mpr ⟨w₁, List.mem_cons_self .., hx⟩
      simp [heq] at this
    | cons w₂ R₂ =>
      simp only [List.flatten_cons] at heq
      have hlen : w₁.length = w₂.length := by
        have := not_shorter h₁ h₂ heq
        have := not_shorter h₂ h₁ heq.symm
        omega
      obtain ⟨hw, hR⟩ := List.append_inj heq hlen
      rw [hw, ih h₁.tail h₂.tail hR]

end Blocks

/-! ## Words -/

/-- The three character classes of a word: space, other, newline. -/
def wcls (c : Char) : Nat := if c = sp then 0 else if c = nl then 2 else 1

theorem sp_ne_nl : sp ≠ nl := by decide

/-- In a word, every character has the class of any other. -/
theorem IsWord.cls {w : List Char} (hw : IsWord w) {a : Char} (ha : a ∈ w) :
    (wcls a = 0 ∧ ∀ c ∈ w, WhiteSpace c) ∨
    (wcls a = 1 ∧ ∀ c ∈ w, NonWhiteSpace c) ∨
    (wcls a = 2 ∧ w = [nl]) := by
  rcases hw with ⟨-, h⟩ | ⟨-, h⟩ | rfl
  · exact .inl ⟨by simp [wcls, h a ha], h⟩
  · have := h a ha
    exact .inr (.inl ⟨by simp [wcls, this.1, this.2], h⟩)
  · simp at ha; subst ha
    exact .inr (.inr ⟨by simp [wcls, sp_ne_nl.symm], rfl⟩)

theorem DocWordSeq.blocks {W : List (List Char)} (h : DocWordSeq W) :
    Blocks wcls (· = 2) W where
  ne w hw := by
    rcases h.1 w hw with ⟨hne, -⟩ | ⟨hne, -⟩ | rfl
    · exact hne
    · exact hne
    · simp
  homog w hw a ha b hb := by
    rcases (h.1 w hw).cls ha with ⟨ha', hall⟩ | ⟨ha', hall⟩ | ⟨ha', rfl⟩
    · rw [ha']; simp [wcls, hall b hb]
    · rw [ha']; have := hall b hb; simp [wcls, this.1, this.2]
    · rw [ha']; simp at hb; subst hb; simp [wcls, sp_ne_nl.symm]
  singleLen w hw a ha hs := by
    rcases (h.1 w hw).cls ha with ⟨ha', -⟩ | ⟨ha', -⟩ | ⟨-, rfl⟩
    · simp [ha'] at hs
    · simp [ha'] at hs
    · rfl
  adj p hp a ha b hb hab := by
    have hmem : ∀ q ∈ adjacent W, q.1 ∈ W ∧ q.2 ∈ W := by
      intro q hq
      exact ⟨List.of_mem_zip hq |>.1, List.mem_of_mem_tail (List.of_mem_zip hq).2⟩
    obtain ⟨h1, h2⟩ := hmem p hp
    obtain ⟨rws, rnws⟩ := h.2 p hp
    rcases (h.1 _ h1).cls ha with ⟨ha', hall1⟩ | ⟨ha', hall1⟩ | ⟨ha', -⟩
    · rcases (h.1 _ h2).cls hb with ⟨-, hall2⟩ | ⟨hb', -⟩ | ⟨hb', -⟩
      · exact absurd hall2 (rws hall1)
      · omega
      · omega
    · rcases (h.1 _ h2).cls hb with ⟨hb', -⟩ | ⟨-, hall2⟩ | ⟨hb', -⟩
      · omega
      · exact absurd hall2 (rnws hall1)
      · omega
    · exact ha'

/-- **Corollary 3:1.2a.** Word sequences with the same characters are equal. -/
theorem DocWordSeq.unique {W₁ W₂ : List (List Char)}
    (h₁ : DocWordSeq W₁) (h₂ : DocWordSeq W₂) (h : FW W₁ = FW W₂) : W₁ = W₂ :=
  Blocks.unique h₁.blocks h₂.blocks h

/-! ## Lines -/

/-- The two character classes of a line: newline, other. -/
def lcls (c : Char) : Nat := if c = nl then 1 else 0

theorem DocLineSeq.blocks {L : List (List Char)} (h : DocLineSeq L) :
    Blocks lcls (· = 1) L where
  ne l hl := by
    rcases h.1 l hl with ⟨hne, -⟩ | rfl
    · exact hne
    · simp
  homog l hl a ha b hb := by
    rcases h.1 l hl with ⟨-, hnl⟩ | rfl
    · have ha' : a ≠ nl := fun e => hnl (e ▸ ha)
      have hb' : b ≠ nl := fun e => hnl (e ▸ hb)
      simp [lcls, ha', hb']
    · simp at ha hb; simp [ha, hb]
  singleLen l hl a ha hs := by
    rcases h.1 l hl with ⟨-, hnl⟩ | rfl
    · have : a = nl := by simp only [lcls] at hs; split at hs <;> simp_all
      exact absurd (this ▸ ha) hnl
    · rfl
  adj p hp a ha b hb hab := by
    by_cases hanl : a = nl
    · simp [lcls, hanl]
    · have hp1 : p.1 ≠ [nl] := by
        intro e; rw [e] at ha; simp at ha; exact hanl ha
      have := h.2 p hp hp1
      rw [this] at hb; simp at hb
      simp [lcls, hanl, hb] at hab

/-- **Corollary 3:1.2c.** Line sequences with the same characters are equal. -/
theorem DocLineSeq.unique {L₁ L₂ : List (List Char)}
    (h₁ : DocLineSeq L₁) (h₂ : DocLineSeq L₂) (h : FL L₁ = FL L₂) : L₁ = L₂ :=
  Blocks.unique h₁.blocks h₂.blocks h

/-! ## Consequences for Doc1 -/

/-- A `Doc1` state is determined by its characters: the word and line views
follow from them. -/
theorem Doc1.ext_chars {d d' : Doc1} (h : d.chars = d'.chars) : d = d' := by
  have hl : d.leftChar = d'.leftChar := congrArg Pair.left h
  have hr : d.rightChar = d'.rightChar := congrArg Pair.right h
  have hlw : d.leftWord = d'.leftWord :=
    DocWordSeq.unique d.leftWord_ok d'.leftWord_ok
      (by rw [← d.left_inv.1, ← d'.left_inv.1, hl])
  have hrw : d.rightWord = d'.rightWord :=
    DocWordSeq.unique d.rightWord_ok d'.rightWord_ok
      (by rw [← d.right_inv.1, ← d'.right_inv.1, hr])
  have hll : d.leftLine = d'.leftLine :=
    DocLineSeq.unique d.leftLine_ok d'.leftLine_ok
      (by rw [← d.left_inv.2, ← d'.left_inv.2, hlw])
  have hrl : d.rightLine = d'.rightLine :=
    DocLineSeq.unique d.rightLine_ok d'.rightLine_ok
      (by rw [← d.right_inv.2, ← d'.right_inv.2, hrw])
  cases d; cases d'
  simp_all

/-- `Mirror ; Mirror` changes nothing (one half of `Mirror ; Mirror ≙ ΞDoc1`;
the other half needs every character sequence to have a word and line view,
which is the next step). -/
theorem mirror_mirror {d d' : Doc1} (h : (Mirror ⨾ Mirror) d d') : d' = d :=
  Doc1.ext_chars (mirror_mirror_chars h)

end ZEditor
