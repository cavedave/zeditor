import ZEditor.Spec.Doc8
import ZEditor.Impl.Editor

/-!
# Claims the monograph never made

The monograph states structural claims (invariants hold, operations have
outcomes) but almost no behavioural ones: round trips, progress, "errors change
nothing", "no data is lost". Stating such a claim and checking it is the
antidote to slip risk: a slip that no claim depends on survives unnoticed.

## Claim: Cut then Paste gives the document back

Cut the marked text, then Paste it straight back at the cursor: the text should
be what it was. We check this claim against three versions of Cut and Paste.
-/

namespace ZEditor.Claims

open ZEditor

/-! ### 1. The printed specification: the claim fails

After a Cut the cursor is not at the top, and the printed `Pst` has no outcome
there (`pst_impossible`), so the Paste half cannot happen at all. -/

/-- In "x[ab]|y" (the mark after `x`, the cursor after `b`), the printed Cut
removes "ab", leaving "x|y"; the printed Paste of "ab" is then impossible. -/
theorem printed_cut_paste_fails :
    RemMText ['x', 'a', 'b'] ['y'] ['x'] ['a', 'b'] ['x'] ['y'] [] [] ∧
    ∀ l' r' ms' md', ¬ Pst ['a', 'b'] ['x'] ['y'] l' r' ms' md' := by
  refine ⟨⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h => by simp at h⟩, ?_⟩
  intro l' r' ms' md'
  exact pst_impossible (by simp) (by simp)

/-! ### 2. Our first fix (the C's reading of the schemas): the claim fails too

`RemMTextC` repairs the `Left`/`Right` slip (finding 6b), but trying to prove the
claim for it turns up something new. The `MarkedText` state records the mark as
two sequences, and they do not always say which side of the cursor the mark is
on. In "ab|ba" with `MarkSeq = ⟨a⟩` and `MarkedSeq = ⟨b⟩`, both
`MarkSeq ⁀ MarkedSeq = Left_Char` (mark one place back, "b" marked before the
cursor) and `MarkedSeq ⁀ MarkSeq = Right_Char` (mark one place on, "b" marked
after the cursor) hold. Cut must then remove the "b" on both sides at once,
which is impossible: it has no outcome. -/

/-- The state is valid: the `MarkedText` invariant holds, both ways at once. -/
theorem mark_side_ambiguous :
    (['a'] ++ ['b'] = ['a', 'b']) ∧ (['b'] ++ ['a'] = ['b', 'a']) := ⟨rfl, rfl⟩

/-- And the corrected Cut has no outcome there. -/
theorem remMTextC_no_outcome (l' r' : List Char) :
    ¬ RemMTextC ['a', 'b'] ['b', 'a'] ['a'] ['b'] l' r' [] [] := by
  rintro ⟨-, -, h1, h2⟩
  have e1 := (h1 rfl).1
  have e2 := (h2 rfl).2
  rw [e1] at e2; simp at e2

/-! ### 3. The mark as a position, as in the C: the claim holds

The C keeps the mark as a position `MP` in the text (`MP = −1` for no mark).
With the mark as a position there is no doubt which side it is on, and the
claim can be proved for every document. -/

/-- A document as one text with a cursor position and a mark position. -/
structure MDoc where
  text   : List Char
  cursor : Nat
  mark   : Nat
  deriving DecidableEq

/-- Cut: remove the text between the cursor and the mark, whichever comes first,
and put it in the paste buffer (as the C's `CopyMTextPBuff` and `RemMText`). -/
def cut (d : MDoc) : MDoc × List Char :=
  let lo := min d.cursor d.mark
  let hi := max d.cursor d.mark
  (⟨d.text.take lo ++ d.text.drop hi, lo, lo⟩, (d.text.drop lo).take (hi - lo))

/-- Paste: insert the buffer at the cursor, mark the pasted text (as the C's
`Paste_Doc6`: the mark at the old cursor, the cursor after the pasted text). -/
def paste (d : MDoc) (buf : List Char) : MDoc :=
  ⟨d.text.take d.cursor ++ buf ++ d.text.drop d.cursor, d.cursor + buf.length, d.cursor⟩

/-- **Cut then Paste gives the text back, for every document.** -/
theorem cut_then_paste (d : MDoc) (hc : d.cursor ≤ d.text.length)
    (hm : d.mark ≤ d.text.length) :
    (paste (cut d).1 (cut d).2).text = d.text := by
  simp only [cut, paste]
  have hlo : min d.cursor d.mark ≤ max d.cursor d.mark := by omega
  have hhi : max d.cursor d.mark ≤ d.text.length := by omega
  generalize min d.cursor d.mark = lo at hlo
  generalize max d.cursor d.mark = hi at hlo hhi
  have hlen : (d.text.take lo).length = lo := by simp; omega
  have h1 : (d.text.take lo ++ d.text.drop hi).take lo = d.text.take lo := by
    rw [List.take_append_of_le_length (Nat.le_of_eq hlen.symm), List.take_take, Nat.min_self]
  have h2 : (d.text.take lo ++ d.text.drop hi).drop lo = d.text.drop hi := by
    rw [List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append]
  have h3 : d.text.drop hi = (d.text.drop lo).drop (hi - lo) := by
    rw [List.drop_drop]; congr 1; omega
  rw [h1, h2, h3, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- And the cursor ends up after the pasted text, with the pasted text marked. -/
example : paste (cut ⟨"xaby".toList, 3, 1⟩).1 (cut ⟨"xaby".toList, 3, 1⟩).2 =
    ⟨"xaby".toList, 3, 1⟩ := by decide

/-! ## Claim: an editor that refuses every insertion does not meet the specification

It does. `ErrorFull` has no precondition, so "Editor full" is always a permitted
answer to an insertion, to Paste, and to every QP cursor move. A program that
never inserts anything, and never moves the cursor up or down, meets those
parts of the specification. Nothing states when the editor must succeed. -/

theorem insert_may_always_refuse (x : Char) (d : Doc1) :
    InsertChar_Doc1 x d d "Editor full" := .inr ⟨rfl, rfl⟩

theorem cursorDown_may_always_refuse (pageHeight : Nat) (d : Doc4) :
    QPCursorOp.cursorDownChar.doc4 pageHeight d d "Editor full" := .inr (.inr ⟨rfl, rfl⟩)

theorem paste_may_always_refuse (d : Doc6) : Paste_Doc6 d d "Editor full" :=
  .inr (.inl ⟨rfl, rfl⟩)

/-! ## Claim: an error changes nothing

True for the document operations: every error case of Doc1 is `Doc1Unchanged`.
False for the operating-system operations of Doc7 (finding 7e): see
`input_error_any_document`, `writeToStore_cannot_open_any`, `save_any_store`. -/

theorem doc1_errors_change_nothing {d d' : Doc1} {rep : Report}
    (h : ErrorTopOfDoc d d' rep ∨ ErrorBotOfDoc d d' rep ∨ ErrorFull d d' rep) : d' = d := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact h

/-! ## Claim: Quit never discards unsaved changes

False. Whenever Quit can run at all (finding 7a), it may answer "Document not
changed" and exit, writing nothing, whatever has been typed (finding 7f). -/

theorem quit_may_discard (os : OS) {w : World os} (hstate : w.doc.state = .quote)
    (hq : w.doc.qBuff = ['q']) (hm : w.doc.markedSeq = w.doc.leftChar ++ w.doc.rightChar) :
    ∃ w', Quit_Quote os w w' "Document not changed" ∧ w'.exited = true ∧
      w'.store = w.store := by
  let d' : Doc7 := { w.doc with state := .doc }
  exact ⟨⟨d', w.store, true⟩, ⟨w.doc.markedSeq,
    ⟨⟨⟨hstate, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, hq, hm⟩, .inr (.inl ⟨rfl, rfl⟩)⟩, rfl, rfl⟩

/-! ## Claim: reading a file gives back what was written to it

False. Even at the same pointer, straight after a successful write, a successful
read may return any text (finding 7d); and nothing links a file name to a
pointer (finding 7h). -/

theorem write_then_read_any (os : OS) {s s' : Store os} {p : os.Ptr} {ws : List Char}
    (_ : SysWrite os s s' p ws .w true) (rs : List Char) : SysRead os s' p rs true :=
  sysRead_success_any os s' p rs

/-! ## Claim: moving the cursor does not change the text

False, by design: the Doc3 tidying runs after every operation, moves included.
Type "a␣", press ← and the space is deleted, because a line may not end in
spaces to the right of the cursor. So typing "a␣", ←, →, "b" gives "ab", not
"a b". The C does the same (`RemTrailWS`, Appendix C p.v). Shown here on the
runnable editor's operations, which follow the specification's tidying. -/

open ZEditor.Impl in
theorem step_back_deletes_space :
    tidy 2 ((leftMoveChar ("a ".toList, [])).getD ([], [])) = ("a".toList, []) := by
  decide

/-! ## Claim: Enter then Backspace gives back the text

False, by design. In "ab␣|cd", Enter makes "ab␣" a finished line, so its trailing
space is removed; Backspace then joins the lines without it, giving "abcd". A
space between two words is lost. The C does the same. -/

open ZEditor.Impl in
theorem enter_backspace_loses_space :
    let c₀ : Chars := ("ab ".toList, "cd".toList)
    let c₁ := tidy 3 ((insertChar nl c₀).getD c₀)
    tidy c₁.1.length ((leftDeleteChar c₁).getD c₁) = ("ab".toList, "cd".toList) := by
  decide

end ZEditor.Claims
