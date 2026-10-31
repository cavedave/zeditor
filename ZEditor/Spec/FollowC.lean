import ZEditor.Spec.Doc8

/-!
# Decision D9: the "follow the C" readings

For each finding in this batch the printed specification is stuck, unconstrained
or contradictory, and the C program shows what was intended. Following the
project's policy, the printed definitions stay in `Doc4.lean` to `Doc8.lean`
under their own names, and the readings we use are here, with a `C` suffix.
Finding 5's reading, `PadWSNLC`, is in `Doc4.lean`. See `FINDINGS.md`, decision D9.
-/

namespace ZEditor

/-! ## 7a. Quit -/

/-- `RequestQuit` without the line `WriteSeq! = MarkedSeq`: Quit writes the whole
document (`WriteSeq! = Left_Char ⁀ Right_Char`), as the C's `Quit_Quote` does. -/
def RequestQuitC (d d' : Doc7) (ws : List Char) : Prop :=
  QuoteRequestNoChange d d' ∧ d.qBuff = ['q'] ∧ ws = d.leftChar ++ d.rightChar

/-- The printed `RequestQuit` is the corrected one plus `WriteSeq! = MarkedSeq`. -/
theorem requestQuit_iff {d d' : Doc7} {ws : List Char} :
    RequestQuit d d' ws ↔ RequestQuitC d d' ws ∧ ws = d.markedSeq := by
  unfold RequestQuit RequestQuitC
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h3, h4⟩, h2⟩
  · rintro ⟨⟨h1, h3, h4⟩, h2⟩; exact ⟨h1, h2, h3, h4⟩

/-- With the corrected request, Quit can always be requested from `q`. -/
theorem requestQuitC_exists {d : Doc7} (hstate : d.state = .quote) (hq : d.qBuff = ['q']) :
    ∃ d' ws, RequestQuitC d d' ws :=
  ⟨{ d with state := .doc }, _, ⟨⟨⟨hstate, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, hq, rfl⟩⟩

/-! ## 7c. Input while text is marked -/

/-- `QuoteRequestContentChange` with the prime on `MarkedSeq′`: the command
clears the mark (`MarkSeq′ = MarkedSeq′ = ⟨⟩`), as the C's `Update_Doc6` does,
instead of requiring that nothing was marked before it. -/
def QuoteRequestContentChangeC (d d' : Doc7) : Prop :=
  QuoteRequest d d' ∧ d'.markSeq = [] ∧ d'.markedSeq = []

/-- The corrected version places no condition on the mark before the command. -/
theorem quoteRequestContentChangeC_any_mark {d d' : Doc7} (h : QuoteRequest d d')
    (hms : d'.markSeq = []) (hmd : d'.markedSeq = []) : QuoteRequestContentChangeC d d' :=
  ⟨h, hms, hmd⟩

/-! ## 7d. Reading a file -/

/-- `SysRead` without the `¬`: a successful read returns the file's contents. -/
def SysReadC (os : OS) (s : Store os) (p : os.Ptr) (rs : List Char) (ok : Bool) : Prop :=
  ok = true → rs = os.storedseq (s p)

theorem sysReadC_success {os : OS} {s : Store os} {p : os.Ptr} {rs : List Char}
    (h : SysReadC os s p rs true) : rs = os.storedseq (s p) := h rfl

/-! ## 7e. An error changes nothing -/

/-- `WriteToStore` with "nothing else changes" stated in every branch: when the
file cannot be opened, the store is unchanged (the C changes nothing). -/
def WriteToStoreC (os : OS) (s s' : Store os) (ws : List Char) (mode : FileMode)
    (rep : Report) : Prop :=
  ∃ p, (SuccSysGetPtr os p ∧ SysWrite os s s' p ws mode true ∧ rep = "OK") ∨
       (SuccSysGetPtr os p ∧ SysWrite os s s' p ws mode false ∧ rep = "Error writing file") ∨
       (p = os.nullPtr ∧ s' = s ∧ rep = "Cannot open file")

/-- **An error changes nothing**: whenever writing fails, the store is unchanged. -/
theorem writeToStoreC_error_unchanged {os : OS} {s s' : Store os} {ws : List Char}
    {mode : FileMode} {rep : Report} (h : WriteToStoreC os s s' ws mode rep)
    (hrep : rep ≠ "OK") : s' = s := by
  obtain ⟨p, ⟨-, -, hok⟩ | ⟨-, ⟨hw, -⟩, -⟩ | ⟨-, hs, -⟩⟩ := h
  · exact absurd hok hrep
  · exact hw rfl
  · exact hs

/-- `ReadFromStore` with the store unchanged in every branch (reading never
writes), and the corrected `SysReadC`. -/
def ReadFromStoreC (os : OS) (s s' : Store os) (rs : List Char) (rep : Report) : Prop :=
  s' = s ∧
  ∃ p, (SuccSysGetPtr os p ∧ SysReadC os s p rs true ∧ rep = "OK") ∨
       (SuccSysGetPtr os p ∧ rep = "Error reading file") ∨
       (p = os.nullPtr ∧ rep = "Cannot open file") ∨
       (SuccSysGetPtr os p ∧ rep = "Editor full")

theorem readFromStoreC_unchanged {os : OS} {s s' : Store os} {rs : List Char} {rep : Report}
    (h : ReadFromStoreC os s s' rs rep) : s' = s := h.1

/-! ## 7b. Move to line, and the empty command -/

/-- `ValidQBuffText` with a line number required to have at least one digit, as
in the C, where `MoveLineNumberOrError_Quote` turns anything that is not a
command into either a move to a line or an error. -/
def ValidQBuffTextC (q : List Char) : Prop :=
  q ∈ ["abort".toList, ['q'], ['s'], ['!']] ∨
  (∃ s ∈ [['a', ' '], ['i', ' '], ['w', ' '], ['!']], prefix1 s q) ∨
  (q ≠ [] ∧ ∀ c ∈ q, c.isDigit)

instance (q : List Char) : Decidable (ValidQBuffTextC q) := by
  unfold ValidQBuffTextC; infer_instance

def ErrorQuoteErrorC (os : OS) (w w' : World os) (rep : Report) : Prop :=
  QuoteRequestNoChange w.doc w'.doc ∧ ¬ ValidQBuffTextC w.doc.qBuff ∧ rep = "Quote error" ∧
  w'.store = w.store ∧ w'.exited = w.exited

/-- `Quote_StateQuote` with `MoveLineNumber_Quote` included, and the corrected
validity test, so that the empty command is a "Quote error". -/
def Quote_StateQuoteC (os : OS) (convNum : List Char → Nat) (w w' : World os)
    (rep : Report) : Prop :=
  Abort_Quote os w w' rep ∨ Save_Quote os w w' rep ∨ Write_Quote os w w' rep ∨
  Append_Quote os w w' rep ∨ Quit_Quote os w w' rep ∨ Input_Quote os w w' rep ∨
  Escape_Quote os w w' rep ∨ MoveLineNumber_Quote os convNum w w' rep ∨
  ErrorQuoteErrorC os w w' rep

/-- **The empty command now has an outcome**: it is a "Quote error". -/
theorem emptyQuoteC_has_outcome (os : OS) (convNum : List Char → Nat) {w : World os}
    (hstate : w.doc.state = .quote) (hq : w.doc.qBuff = []) :
    ∃ w' rep, Quote_StateQuoteC os convNum w w' rep := by
  refine ⟨⟨{ w.doc with state := .doc }, w.store, w.exited⟩, "Quote error",
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨⟨⟨hstate, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩,
      ?_, rfl, rfl, rfl⟩)))))))⟩
  rw [hq]; decide

/-! ## 8a, 8b, 8c. Search and Replace -/

/-- `PromoteReplace` without `Ξ_Cont Doc1`: Replace may change the text, as the
prose says ("only the replace buffer, document state and document content may
change") and the C does. -/
def PromoteReplaceC (d d' : Doc8) : Prop :=
  d'.pBuff = d.pBuff ∧ d'.toQuoteBuffer = d.toQuoteBuffer ∧ d'.name = d.name ∧
  d'.sBuff = d.sBuff

/-- `PromoteSearch` without `Ξ_Cont Doc1` over the whole operation. The search
step itself keeps the text (`SearchOp` has `Ξ_Cont Doc1`); only the tidying that
follows may change it, by removing spaces or empty lines, as the prose allows and
the C does. -/
def PromoteSearchC (d d' : Doc8) : Prop :=
  d'.pBuff = d.pBuff ∧ d'.toQuoteBuffer = d.toQuoteBuffer ∧ d'.name = d.name ∧
  d'.rBuff = d.rBuff

/-- The `UnMark` schemas with the prime on `MarkSeq′`: the mark is cleared after
the operation, rather than required to be absent before it. -/
def PromoteSearchUnMarkC (d d' : Doc8) : Prop :=
  PromoteSearchC d d' ∧ d'.markSeq = [] ∧ d'.markedSeq = []

def PromoteReplaceUnMarkC (d d' : Doc8) : Prop :=
  PromoteReplaceC d d' ∧ d'.markSeq = [] ∧ d'.markedSeq = []

/-- Every outcome allowed by the printed `PromoteReplace` is allowed by the
corrected one; the corrected one drops only the requirement that the text be
unchanged (which made Replace unable to replace, `replace_ok_unchanged`). -/
theorem promoteReplace_imp_C {d d' : Doc8} (h : PromoteReplace d d') : PromoteReplaceC d d' :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem promoteSearch_imp_C {d d' : Doc8} (h : PromoteSearch d d') : PromoteSearchC d d' :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## 8d. A down search moves forward -/

/-- `SuccDownSch` with the cursor required to move forward, as the C does
(it searches from the character after the cursor). -/
def SuccDownSchC (R : RegExps) (sb l r l' r' : List Char) : Prop :=
  SuccDownSch R sb l r l' r' ∧ l'.length > l.length

/-- `SuccUpSch` with the cursor required to move back. -/
def SuccUpSchC (R : RegExps) (sb l r l' r' : List Char) : Prop :=
  SuccUpSch R sb l r l' r' ∧ l'.length < l.length

theorem downSearchC_forward {R : RegExps} {sb l r l' r' : List Char}
    (h : SuccDownSchC R sb l r l' r') : l'.length > l.length := h.2

/-- The backwards jump of finding 8d is excluded. -/
theorem downSearchC_no_jump_back (R : RegExps) :
    ¬ SuccDownSchC R ['a'] ['a'] ['x', 'a'] [] ['a', 'x', 'a'] := by
  rintro ⟨-, h⟩; simp at h

end ZEditor
