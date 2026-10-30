import ZEditor.Spec.Doc6

/-!
# Doc7: the quote buffer and quoted commands (Part Three, §6)

Printed pp.91–107 (PDF pp.94–110). Commands that need typed arguments (save,
write, append, quit, input, move to line, escape to the shell) are typed into a
small quote buffer and run by pressing the quote key. They talk to the
operating system, which the book specifies only abstractly (§6.2).

The editor state is extended with the quote buffer, an editing state
(document or quote buffer) and the document's name. The file store and
whether the editor has exited are kept beside it in a `World`.
-/

namespace ZEditor

/-! ## §6.1 The quote buffer -/

/-- `QuoteBuffer`: `QBuff = Left_Quote ⁀ Right_Quote` (`QBuff` is redundant and
is computed). -/
structure QuoteBuffer where
  leftQuote  : List Char
  rightQuote : List Char

def QuoteBuffer.qBuff (q : QuoteBuffer) : List Char := q.leftQuote ++ q.rightQuote

abbrev QuoteOp := QuoteBuffer → QuoteBuffer → Report → Prop

def QteInsChar (x : Char) (q q' : QuoteBuffer) : Prop :=
  x ≠ tab ∧ q'.leftQuote = q.leftQuote ++ [x] ∧ q'.rightQuote = q.rightQuote
def QteLeftDelChar (q q' : QuoteBuffer) : Prop :=
  q.leftQuote ≠ [] ∧ q'.leftQuote = q.leftQuote.dropLast ∧ q'.rightQuote = q.rightQuote
def QteRightDelChar (q q' : QuoteBuffer) : Prop :=
  q.rightQuote ≠ [] ∧ q'.leftQuote = q.leftQuote ∧ q'.rightQuote = q.rightQuote.tail
def QteLeftMvChar (q q' : QuoteBuffer) : Prop :=
  q.leftQuote ≠ [] ∧ q'.qBuff = q.qBuff ∧ q'.leftQuote = q.leftQuote.dropLast
def QteRightMvChar (q q' : QuoteBuffer) : Prop :=
  q.rightQuote ≠ [] ∧ q'.qBuff = q.qBuff ∧ q'.rightQuote = q.rightQuote.tail

/-- `ErrorQuote ≙ [ ΞQuoteBuffer ; rep! : Report ]` and the four quote errors. -/
def ErrorIllegalCharacter (x : Char) : QuoteOp := fun q q' rep =>
  q' = q ∧ x = tab ∧ rep = "Illegal quote character"
def ErrorQuoteFull : QuoteOp := fun q q' rep => q' = q ∧ rep = "Quote buffer full"
def ErrorTopQuote : QuoteOp := fun q q' rep =>
  q' = q ∧ q.leftQuote = [] ∧ rep = "At top of quote buffer"
def ErrorBotQuote : QuoteOp := fun q q' rep =>
  q' = q ∧ q.rightQuote = [] ∧ rep = "At bottom of quote buffer"

def InsertChar_Quote (x : Char) : QuoteOp := fun q q' rep =>
  (QteInsChar x q q' ∧ Success rep) ∨ ErrorQuoteFull q q' rep ∨ ErrorIllegalCharacter x q q' rep
def LeftDeleteChar_Quote : QuoteOp := fun q q' rep =>
  (QteLeftDelChar q q' ∧ Success rep) ∨ ErrorTopQuote q q' rep
def RightDeleteChar_Quote : QuoteOp := fun q q' rep =>
  (QteRightDelChar q q' ∧ Success rep) ∨ ErrorBotQuote q q' rep
def LeftMoveChar_Quote : QuoteOp := fun q q' rep =>
  (QteLeftMvChar q q' ∧ Success rep) ∨ ErrorTopQuote q q' rep
def RightMoveChar_Quote : QuoteOp := fun q q' rep =>
  (QteRightMvChar q q' ∧ Success rep) ∨ ErrorBotQuote q q' rep

/-! **PO 2 for the quote buffer** (printed pp.93–94): the edit operations always
have an outcome. -/

theorem InsertChar_Quote_total (x : Char) (q : QuoteBuffer) :
    ∃ q' rep, InsertChar_Quote x q q' rep := ⟨q, _, .inr (.inl ⟨rfl, rfl⟩)⟩

theorem LeftDeleteChar_Quote_total (q : QuoteBuffer) : ∃ q' rep, LeftDeleteChar_Quote q q' rep := by
  by_cases h : q.leftQuote = []
  · exact ⟨q, _, .inr ⟨rfl, h, rfl⟩⟩
  · exact ⟨⟨q.leftQuote.dropLast, q.rightQuote⟩, _, .inl ⟨⟨h, rfl, rfl⟩, rfl⟩⟩

theorem RightDeleteChar_Quote_total (q : QuoteBuffer) : ∃ q' rep, RightDeleteChar_Quote q q' rep := by
  by_cases h : q.rightQuote = []
  · exact ⟨q, _, .inr ⟨rfl, h, rfl⟩⟩
  · exact ⟨⟨q.leftQuote, q.rightQuote.tail⟩, _, .inl ⟨⟨h, rfl, rfl⟩, rfl⟩⟩

theorem LeftMoveChar_Quote_total (q : QuoteBuffer) : ∃ q' rep, LeftMoveChar_Quote q q' rep := by
  by_cases h : q.leftQuote = []
  · exact ⟨q, _, .inr ⟨rfl, h, rfl⟩⟩
  · refine ⟨⟨q.leftQuote.dropLast, q.leftQuote.getLast h :: q.rightQuote⟩, _,
      .inl ⟨⟨h, ?_, rfl⟩, rfl⟩⟩
    simp only [QuoteBuffer.qBuff]
    conv => rhs; rw [← List.dropLast_concat_getLast h]
    simp

theorem RightMoveChar_Quote_total (q : QuoteBuffer) : ∃ q' rep, RightMoveChar_Quote q q' rep := by
  by_cases h : q.rightQuote = []
  · exact ⟨q, _, .inr ⟨rfl, h, rfl⟩⟩
  · refine ⟨⟨q.leftQuote ++ [q.rightQuote.head h], q.rightQuote.tail⟩, _,
      .inl ⟨⟨h, ?_, rfl⟩, rfl⟩⟩
    simp only [QuoteBuffer.qBuff]
    conv => rhs; rw [← List.cons_head_tail h]
    simp

/-! ## §6.2 Operating system I/O -/

/-- `[Ptr]`, `[Cont]`, `NullPtr : Ptr`, `storedseq : Cont → seq Char`: the
operating system is left abstract. -/
structure OS where
  Ptr : Type
  Cont : Type
  nullPtr : Ptr
  storedseq : Cont → List Char

/-- `Store ≙ [ FStore : Ptr → Cont ]` -/
abbrev Store (os : OS) := os.Ptr → os.Cont

inductive FileMode where
  | r | w | a

variable (os : OS)

/-- `SysGetPtr`: returns a pointer for a file name and mode; `NullPtr` on
failure. The pointer is not related to the file name in any way. -/
def SuccSysGetPtr (p : os.Ptr) : Prop := p ≠ os.nullPtr

/-- ```
┌─ SysWrite ───────────────────────────
│ ΔStore
│ Sysptr? : Ptr ; WriteSeq? : seq Char
│ filemode? : {⟨w⟩, ⟨a⟩} ; NoWriteError! : 𝔹
├──────────────────────────────────────
│ ¬ NoWriteError! ⇒ FStore = FStore′
│ NoWriteError! ∧ filemode? = ⟨w⟩ ⇒
│     {Sysptr?} ⩤ FStore′ = {Sysptr?} ⩤ FStore
│     storedseq(FStore′ Sysptr?) = WriteSeq?
│ NoWriteError! ∧ filemode? = ⟨a⟩ ⇒
│     Sysptr? ∈ dom FStore
│     {Sysptr?} ⩤ FStore′ = {Sysptr?} ⩤ FStore
│     storedseq(FStore′ Sysptr?) = storedseq(FStore Sysptr?) ⁀ WriteSeq?
└──────────────────────────────────────
```
(`Sysptr? ∈ dom FStore` holds trivially, `FStore` being total.) -/
def SysWrite (s s' : Store os) (p : os.Ptr) (ws : List Char) (mode : FileMode)
    (ok : Bool) : Prop :=
  (ok = false → s' = s) ∧
  (ok = true → mode = .w → (∀ q, q ≠ p → s' q = s q) ∧ os.storedseq (s' p) = ws) ∧
  (ok = true → mode = .a → (∀ q, q ≠ p → s' q = s q) ∧
    os.storedseq (s' p) = os.storedseq (s p) ++ ws)

/-- ```
┌─ SysRead ────────────────────────────
│ ΞStore
│ Sysptr? : Ptr ; ReadSeq! : seq Char
│ filemode? : {⟨r⟩} ; NoReadError! : 𝔹
├──────────────────────────────────────
│ ¬ NoReadError! ⇒ ReadSeq! = storedseq(FStore Sysptr?)
└──────────────────────────────────────
```
Checked against the scan: the `¬` is printed. The prose says the read text is
returned "in the former case", i.e. on success. -/
def SysRead (s : Store os) (p : os.Ptr) (rs : List Char) (ok : Bool) : Prop :=
  ok = false → rs = os.storedseq (s p)

/-- **A successful read may return any text.** -/
theorem sysRead_success_any (s : Store os) (p : os.Ptr) (rs : List Char) :
    SysRead os s p rs true := by
  intro h; cases h

/-- ```
WriteToStore ≙ SuccSysGetPtr ≫ SuccSysWrite ∧ Success
             ∨ SuccSysGetPtr ≫ UnSuccSysWrite ∧ ErrorWritingFile
             ∨ UnSuccSysGetPtr ∧ ErrorCannotOpenFile
```
In Z, a schema disjunction has the combined signature of its parts, and a
variable a part does not mention is unconstrained in that part. The last part
does not mention the store, so `FStore′` is free there. -/
def WriteToStore (s s' : Store os) (ws : List Char) (mode : FileMode) (rep : Report) : Prop :=
  ∃ p, (SuccSysGetPtr os p ∧ SysWrite os s s' p ws mode true ∧ rep = "OK") ∨
       (SuccSysGetPtr os p ∧ SysWrite os s s' p ws mode false ∧ rep = "Error writing file") ∨
       (p = os.nullPtr ∧ rep = "Cannot open file")

/-- **"Cannot open file" may change the file store arbitrarily.** -/
theorem writeToStore_cannot_open_any (s s' : Store os) (ws : List Char) (mode : FileMode) :
    WriteToStore os s s' ws mode "Cannot open file" :=
  ⟨os.nullPtr, .inr (.inr ⟨rfl, rfl⟩)⟩

/-- ```
ReadFromStore ≙ SuccSysGetPtr ≫ SuccSysRead ∧ Success
              ∨ SuccSysGetPtr ≫ UnSuccSysRead ∧ ErrorReadingFile
              ∨ UnSuccSysGetPtr ∧ ErrorCannotOpenFile
              ∨ SuccGetSysPtr ∧ ErrorReadFull
```
(`SuccGetSysPtr` for `SuccSysGetPtr`.) The store is free in the last two parts. -/
def ReadFromStore (s s' : Store os) (rs : List Char) (rep : Report) : Prop :=
  ∃ p, (SuccSysGetPtr os p ∧ SysRead os s p rs true ∧ s' = s ∧ rep = "OK") ∨
       (SuccSysGetPtr os p ∧ SysRead os s p rs false ∧ s' = s ∧ rep = "Error reading file") ∨
       (p = os.nullPtr ∧ rep = "Cannot open file") ∨
       (SuccSysGetPtr os p ∧ rep = "Editor full")

/-! ## §6.3 The Doc7 state -/

inductive EdState where
  | doc | quote
  deriving DecidableEq

/-- `Doc7 ≙ Doc6 ∧ QuoteBuffer ∧ DocState ∧ DocName` -/
structure Doc7 extends Doc6, QuoteBuffer where
  state : EdState
  name  : List Char

/-- ```
┌─ Initialize_Doc7 ────────────
│ Initialize_Doc6 ; ΔDoc7 ; filename? : seq Char
├──────────────────────────────
│ QBuff′ = ⟨⟩ ; State′ = State_Doc ; Name′ = filename?
└──────────────────────────────
``` -/
def Initialize_Doc7 (filename : List Char) (d' : Doc7) : Prop :=
  Initialize_Doc6 d'.toDoc6 ∧ d'.qBuff = [] ∧ d'.state = .doc ∧ d'.name = filename

/-- The editor together with its environment: the file store, and whether
control has been returned to the operating system (`SysReturnControl`). -/
structure World where
  doc : Doc7
  store : Store os
  exited : Bool

/-! ## §6.4 Quoted operations -/

/-- `Quote_StateDoc`: in the document, the quote key empties the quote buffer and
switches to it. -/
def Quote_StateDoc (w w' : World os) (rep : Report) : Prop :=
  w.doc.state = .doc ∧ w'.doc.toDoc6 = w.doc.toDoc6 ∧ w'.doc.name = w.doc.name ∧
  w'.doc.state = .quote ∧ w'.doc.leftQuote = [] ∧ w'.doc.rightQuote = [] ∧ rep = "OK" ∧
  w'.store = w.store ∧ w'.exited = w.exited

/-- `QuoteRequest`: from the quote buffer back to the document, with name,
paste buffer and quote buffer unchanged. Document content and marks may change. -/
def QuoteRequest (d d' : Doc7) : Prop :=
  d.state = .quote ∧ d'.state = .doc ∧ d'.name = d.name ∧ d'.pBuff = d.pBuff ∧
  d'.leftQuote = d.leftQuote ∧ d'.rightQuote = d.rightQuote

/-- `QuoteRequestContentChange ≙ [ QuoteRequest | MarkSeq′ = MarkedSeq = ⟨⟩ ]`.
Checked against the scan: `MarkedSeq` is unprimed, so this requires that no text
be marked *before* the command. -/
def QuoteRequestContentChange (d d' : Doc7) : Prop :=
  QuoteRequest d d' ∧ d'.markSeq = [] ∧ d.markedSeq = []

/-- `QuoteRequestNoChange ≙ QuoteRequest ∧ ΞDoc5` -/
def QuoteRequestNoChange (d d' : Doc7) : Prop :=
  QuoteRequest d d' ∧ d'.toDoc5 = d.toDoc5

/-- `S prefix₁ T ⇔ S prefix T ∧ S ≠ T` -/
def prefix1 (S T : List Char) : Prop := S.isPrefixOf T = true ∧ S ≠ T

instance (S T : List Char) : Decidable (prefix1 S T) := by unfold prefix1; infer_instance

/-- §6.4.1 `RequestAbort`; `Abort_Quote ≙ RequestAbort ; SysReturnControl`. -/
def Abort_Quote (w w' : World os) (rep : Report) : Prop :=
  QuoteRequestNoChange w.doc w'.doc ∧ w.doc.qBuff = "abort".toList ∧ rep = "OK" ∧
  w'.store = w.store ∧ w'.exited = true

/-- §6.4.2 `RequestSave`: `⟨s⟩ = QBuff`, write the whole document to `Name`. -/
def RequestSave (d d' : Doc7) (ws : List Char) : Prop :=
  QuoteRequestNoChange d d' ∧ d.qBuff = ['s'] ∧ ws = d.leftChar ++ d.rightChar

/-- `Save_Quote ≙ RequestSave ≫ WriteToStore ∨ RequestSave ≫ ErrorDocNotChanged`.
There is no record of whether the document has changed, so the second part has
no condition; and it does not mention the store, which is therefore free. -/
def Save_Quote (w w' : World os) (rep : Report) : Prop :=
  ∃ ws, RequestSave w.doc w'.doc ws ∧ w'.exited = w.exited ∧
    (WriteToStore os w.store w'.store ws .w rep ∨ rep = "Document not changed")

/-- §6.4.3 `RequestWriteMarkedText` / `RequestAppendMarkedText`. -/
def RequestWriteMarkedText (d d' : Doc7) (ws : List Char) : Prop :=
  QuoteRequestNoChange d d' ∧ prefix1 ['w', ' '] d.qBuff ∧ ws = d.markedSeq
def RequestAppendMarkedText (d d' : Doc7) (ws : List Char) : Prop :=
  QuoteRequestNoChange d d' ∧ prefix1 ['a', ' '] d.qBuff ∧ ws = d.markedSeq

def Write_Quote (w w' : World os) (rep : Report) : Prop :=
  ∃ ws, RequestWriteMarkedText w.doc w'.doc ws ∧ w'.exited = w.exited ∧
    ((w.doc.markedSeq ≠ [] ∧ WriteToStore os w.store w'.store ws .w rep) ∨
     (w.doc.markedSeq = [] ∧ rep = "No text marked"))

def Append_Quote (w w' : World os) (rep : Report) : Prop :=
  ∃ ws, RequestAppendMarkedText w.doc w'.doc ws ∧ w'.exited = w.exited ∧
    ((w.doc.markedSeq ≠ [] ∧ WriteToStore os w.store w'.store ws .a rep) ∨
     (w.doc.markedSeq = [] ∧ rep = "No text marked"))

/-- §6.4.4 ```
┌─ RequestQuit ────────────────
│ QuoteRequestNoChange ; WriteSeq! : seq Char
├──────────────────────────────
│ WriteSeq! = MarkedSeq
│ ⟨q⟩ = QBuff
│ filename! = Name
│ filemode! = ⟨w⟩
│ WriteSeq! = Left_Char ⁀ Right_Char
└──────────────────────────────
```
Checked against the scan: both `WriteSeq!` lines are printed. -/
def RequestQuit (d d' : Doc7) (ws : List Char) : Prop :=
  QuoteRequestNoChange d d' ∧ ws = d.markedSeq ∧ d.qBuff = ['q'] ∧
  ws = d.leftChar ++ d.rightChar

/-- ```
Quit_Quote ≙ RequestQuit ≫ SuccWriteToStore ; SysReturnControl
           ∨ RequestQuit ≫ ErrorDocNotChanged ; SysReturnControl
           ∨ RequestQuit ≫ UnSuccWriteToStore
``` -/
def Quit_Quote (w w' : World os) (rep : Report) : Prop :=
  ∃ ws, RequestQuit w.doc w'.doc ws ∧
    ((WriteToStore os w.store w'.store ws .w rep ∧ rep = "OK" ∧ w'.exited = true) ∨
     (rep = "Document not changed" ∧ w'.exited = true) ∨
     (WriteToStore os w.store w'.store ws .w rep ∧ rep ≠ "OK" ∧ w'.exited = w.exited))

/-- §6.4.5 `RequestInput`: `⟨i, sp⟩ prefix₁ QBuff`, read from `QBuff after 2`. -/
def RequestInput (d d' : Doc7) : Prop :=
  QuoteRequestContentChange d d' ∧ prefix1 ['i', ' '] d.qBuff

/-- `InputReadSeq` (declared on `ΔDocI`, read as `ΔDoc1`): append the text read. -/
def InputReadSeq (l r l' r' rs : List Char) : Prop := l' = l ++ rs ∧ r' = r

/-- ```
Input_Quote ≙ FlagPrevCursor ; (RequestInput ≫ SuccReadFromStore ≫ InputReadSeq) ;
                  RemTrailWS ; RemTrailNL
            ∨ RequestInput ≫ UnSuccReadFromStore
            ∨ RequestInput ∧ ΞDoc5 ∧ ErrorFileNotExist
            ∨ RequestInput ∧ ΞDoc5 ∧ UnsuitableFile
            ∨ RequestInput ∧ ΞDoc5 ∧ ErrorFull
```
(`UnsuitableFile` for `ErrorUnsuitableFile`.) The second part has no `ΞDoc5`:
`RequestInput` lets the document change, and nothing then constrains it. -/
def Input_Quote (w w' : World os) (rep : Report) : Prop :=
  RequestInput w.doc w'.doc ∧ w'.exited = w.exited ∧
  ((∃ (rs : List Char) (m₁ m₂ : Doc2), ReadFromStore os w.store w'.store rs "OK" ∧ rep = "OK" ∧
      InputReadSeq w.doc.leftChar w.doc.rightChar m₁.leftChar m₁.rightChar rs ∧
      RemTrailWS (FlagPrevCursor w.doc.toDoc2) m₁ m₂ ∧ RemTrailNL m₂ w'.doc.toDoc2) ∨
   (∃ rs, ReadFromStore os w.store w'.store rs rep ∧ rep ≠ "OK") ∨
   (w'.doc.toDoc5 = w.doc.toDoc5 ∧
     (rep = "File does not exist" ∨ rep = "Unsuitable file" ∨ rep = "Editor full")))

/-- §6.4.6 `RequestMvLineNumber`: `ran QBuff ⊆ NumChar`, `DocCurX′ = 1`,
`DocCurY′ = min (ConvNum QBuff, # UDLines)`. `DocCurX`, `DocCurY` are never
defined; we read them as the cursor `UDCurX`, `UDCurY`. `ConvNum` is a
parameter. Built on `QuoteRequestContentChange`, it leaves the document content
unconstrained, although the prose says only the cursor changes. -/
def RequestMvLineNumber (convNum : List Char → Nat) (d d' : Doc7) : Prop :=
  QuoteRequestContentChange d d' ∧ (∀ c ∈ d.qBuff, c.isDigit) ∧ d'.udCurX = 1 ∧
  d'.udCurY = min (convNum d.qBuff) d.udLines.length

/-- `MoveLineNumber_Quote ≙ (FlagPrevCursor ; RequestMvLineNumber ; RemTrailWS ;
RemTrailNL) ∧ Success`. Defined, but not used: see `Quote_StateQuote`. -/
def MoveLineNumber_Quote (convNum : List Char → Nat) (w w' : World os) (rep : Report) : Prop :=
  ∃ m : Doc7, ∃ m₂ : Doc2, RequestMvLineNumber convNum w.doc m ∧
    RemTrailWS (FlagPrevCursor w.doc.toDoc2) m.toDoc2 m₂ ∧ RemTrailNL m₂ w'.doc.toDoc2 ∧
    rep = "OK" ∧ w'.store = w.store ∧ w'.exited = w.exited

/-- §6.4.7 `Escape.ProvideText ≫ SysInterpret ∧ Success ∨ ErrorNoCommandGiven`.
The shell command may do anything to the store. -/
def Escape_Quote (w w' : World os) (rep : Report) : Prop :=
  QuoteRequestNoChange w.doc w'.doc ∧ w'.exited = w.exited ∧
  ((w.doc.qBuff.length > 1 ∧ prefix1 ['!'] w.doc.qBuff ∧ rep = "OK") ∨
   (w.doc.qBuff = ['!'] ∧ rep = "No command given" ∧ w'.store = w.store))

/-! ## §6.5 The quote command -/

/-- ```
ValidQBuffContent ≙ { ⟨a, b, o, r, t⟩, ⟨q⟩, ⟨s⟩, ⟨!⟩ }
ValidQBuffPrefix  ≙ { ⟨a, sp⟩, ⟨i, sp⟩, ⟨w, sp⟩, ⟨!⟩ }
ValidQBuffText: QBuff ∈ ValidQBuffContent ∨ some prefix₁ of it is valid ∨ rng QBuff ⊆ NumChar
```
(`NumChar` read as the digits.) -/
def ValidQBuffText (q : List Char) : Prop :=
  q ∈ ["abort".toList, ['q'], ['s'], ['!']] ∨
  (∃ s ∈ [['a', ' '], ['i', ' '], ['w', ' '], ['!']], prefix1 s q) ∨
  ∀ c ∈ q, c.isDigit

instance (q : List Char) : Decidable (ValidQBuffText q) := by
  unfold ValidQBuffText; infer_instance

/-- `ErrorQuoteError`: `QuoteRequestNoChange`, `¬ ValidQBuffText`. -/
def ErrorQuoteError (w w' : World os) (rep : Report) : Prop :=
  QuoteRequestNoChange w.doc w'.doc ∧ ¬ ValidQBuffText w.doc.qBuff ∧ rep = "Quote error" ∧
  w'.store = w.store ∧ w'.exited = w.exited

/-- ```
Quote_StateQuote ≙ Abort_Quote ∨ Save_Quote ∨ Write_Quote ∨ Append_Quote ∨
                   Quit_Quote ∨ Input_Quote ∨ Escape_Quote ∨ ErrorQuoteError
```
Checked against the scan: `MoveLineNumber_Quote` is not included. -/
def Quote_StateQuote (w w' : World os) (rep : Report) : Prop :=
  Abort_Quote os w w' rep ∨ Save_Quote os w w' rep ∨ Write_Quote os w w' rep ∨
  Append_Quote os w w' rep ∨ Quit_Quote os w w' rep ∨ Input_Quote os w w' rep ∨
  Escape_Quote os w w' rep ∨ ErrorQuoteError os w w' rep

/-- `Quote_Doc7 ≙ Quote_StateDoc ∨ Quote_StateQuote` -/
def Quote_Doc7 (w w' : World os) (rep : Report) : Prop :=
  Quote_StateDoc os w w' rep ∨ Quote_StateQuote os w w' rep

/-! ## Findings -/

/-- When the quote buffer holds none of the command forms that some disjunct of
`Quote_StateQuote` accepts, but is still `ValidQBuffText` (so `ErrorQuoteError`
does not apply either), pressing the quote key has no outcome at all. -/
theorem quoteStateQuote_stuck {w : World os} (habort : w.doc.qBuff ≠ "abort".toList)
    (hsave : w.doc.qBuff ≠ ['s']) (hw : ¬ prefix1 ['w', ' '] w.doc.qBuff)
    (ha : ¬ prefix1 ['a', ' '] w.doc.qBuff)
    (hquit : w.doc.qBuff ≠ ['q'] ∨ w.doc.markedSeq ≠ w.doc.leftChar ++ w.doc.rightChar)
    (hinput : ¬ prefix1 ['i', ' '] w.doc.qBuff ∨ w.doc.markedSeq ≠ [])
    (hesc : ¬ prefix1 ['!'] w.doc.qBuff) (hesc' : w.doc.qBuff ≠ ['!'])
    (hvalid : ValidQBuffText w.doc.qBuff) :
    ¬ ∃ w' rep, Quote_StateQuote os w w' rep := by
  rintro ⟨w', rep, h | h | h | h | h | h | h | h⟩
  · exact habort h.2.1
  · obtain ⟨_, ⟨_, h, _⟩, _⟩ := h; exact hsave h
  · obtain ⟨_, ⟨_, h, _⟩, _⟩ := h; exact hw h
  · obtain ⟨_, ⟨_, h, _⟩, _⟩ := h; exact ha h
  · obtain ⟨ws, ⟨_, h1, h2, h3⟩, _⟩ := h
    rcases hquit with hq | hq
    · exact hq h2
    · exact hq (h1 ▸ h3)
  · obtain ⟨⟨⟨_, _, hm⟩, hp⟩, _⟩ := h
    rcases hinput with hi | hi
    · exact hi hp
    · exact hi hm
  · obtain ⟨_, _, ⟨_, hp, _⟩ | ⟨hq, _⟩⟩ := h
    · exact hesc hp
    · exact hesc' hq
  · exact h.2.1 hvalid

/-- **"Quit" has no outcome unless the whole document is marked.** `RequestQuit`
requires `WriteSeq! = MarkedSeq` and `WriteSeq! = Left_Char ⁀ Right_Char`. -/
theorem quit_stuck {w : World os} (hq : w.doc.qBuff = ['q'])
    (hm : w.doc.markedSeq ≠ w.doc.leftChar ++ w.doc.rightChar) :
    ¬ ∃ w' rep, Quote_StateQuote os w w' rep :=
  quoteStateQuote_stuck os (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)
    (by rw [hq]; decide) (.inr hm) (.inl (by rw [hq]; decide)) (by rw [hq]; decide)
    (by rw [hq]; decide) (by rw [hq]; decide)

/-- **"Move to line" can never run**, because `MoveLineNumber_Quote` is missing
from `Quote_StateQuote`; and a line number is `ValidQBuffText`, so it is not a
"Quote error" either. Typing `1` and pressing the quote key has no outcome. -/
theorem moveToLine_stuck {w : World os} (hq : w.doc.qBuff = ['1']) :
    ¬ ∃ w' rep, Quote_StateQuote os w w' rep :=
  quoteStateQuote_stuck os (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)
    (by rw [hq]; decide) (.inl (by rw [hq]; decide)) (.inl (by rw [hq]; decide))
    (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)

/-- **An empty quote command has no outcome** (pressing the quote key twice): the
empty buffer counts as a line number (`rng ⟨⟩ ⊆ NumChar`), which is valid. -/
theorem emptyQuote_stuck {w : World os} (hq : w.doc.qBuff = []) :
    ¬ ∃ w' rep, Quote_StateQuote os w w' rep :=
  quoteStateQuote_stuck os (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)
    (by rw [hq]; decide) (.inl (by rw [hq]; decide)) (.inl (by rw [hq]; decide))
    (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)

/-- **"Input" has no outcome while text is marked**, because
`QuoteRequestContentChange` requires the *before*-state `MarkedSeq = ⟨⟩`. -/
theorem input_marked_stuck {w : World os} (hq : w.doc.qBuff = ['i', ' ', 'f'])
    (hm : w.doc.markedSeq ≠ []) :
    ¬ ∃ w' rep, Quote_StateQuote os w w' rep :=
  quoteStateQuote_stuck os (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)
    (by rw [hq]; decide) (.inl (by rw [hq]; decide)) (.inr hm)
    (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)

/-- **A failed Input may replace the document with anything.** In the
`RequestInput ≫ UnSuccReadFromStore` part nothing constrains the document, so
"Cannot open file" may come with any new content `e` (and any file store). -/
theorem input_error_any_document {w : World os} (hstate : w.doc.state = .quote)
    (hq : w.doc.qBuff = ['i', ' ', 'f']) (hm : w.doc.markedSeq = [])
    (e : Doc5) (he : e.markSeq = []) (s' : Store os) :
    ∃ w', Input_Quote os w w' "Cannot open file" ∧ w'.doc.toDoc5 = e ∧ w'.store = s' := by
  let d' : Doc7 :=
    { toDoc6 := ⟨e, w.doc.pBuff⟩
      leftQuote := w.doc.leftQuote
      rightQuote := w.doc.rightQuote
      state := EdState.doc
      name := w.doc.name }
  refine ⟨⟨d', s', w.exited⟩, ⟨⟨⟨⟨hstate, rfl, rfl, rfl, rfl, rfl⟩, he, hm⟩, ?_⟩, rfl,
    .inr (.inl ⟨[], ⟨os.nullPtr, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩, by decide⟩)⟩, rfl, rfl⟩
  rw [hq]; decide

/-- **Save may skip saving, and may change any file.** With the quote buffer `s`,
the outcome "Document not changed" is always allowed (there is no record of
changes), and the store after it is unconstrained. -/
theorem save_any_store {w : World os} (hstate : w.doc.state = .quote) (hq : w.doc.qBuff = ['s'])
    (s' : Store os) :
    ∃ w', Save_Quote os w w' "Document not changed" ∧ w'.doc.toDoc5 = w.doc.toDoc5 ∧
      w'.store = s' := by
  let d' : Doc7 := { w.doc with state := .doc }
  exact ⟨⟨d', s', w.exited⟩, ⟨_, ⟨⟨⟨hstate, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, hq, rfl⟩, rfl,
    .inr rfl⟩, rfl, rfl⟩

/-! ## §6.6–6.7 Promotion of the edit operations -/

/-- The Doc6 operations: those of `EditOps2`, and Lift, Cut, Paste.
(`EditOps3` also lists `ExchMTextPBuff`, which is never defined.) -/
inductive Op6 where
  | edit (op : EditOp6)
  | lift | cut | paste

def Op6.doc6 (pageHeight : Nat) : Op6 → Doc6 → Doc6 → Report → Prop
  | .edit op => op.doc6 pageHeight
  | .lift => Lift_Doc6
  | .cut => Cut_Doc6
  | .paste => Paste_Doc6

/-- `QBuffEditOps ≙ { InsertChar, LeftMoveChar, RightMoveChar, CursorLeftChar,
CursorRightChar, LeftDeleteChar, RightDeleteChar }` -/
inductive QBuffEditOp where
  | insertChar (x : Char)
  | leftMoveChar | rightMoveChar | cursorLeftChar | cursorRightChar
  | leftDeleteChar | rightDeleteChar

/-- `OP_Quote` for each. `CursorLeftChar_Quote` and `CursorRightChar_Quote` are
never defined; we use the character moves. -/
def QBuffEditOp.quote : QBuffEditOp → QuoteOp
  | .insertChar x => InsertChar_Quote x
  | .leftMoveChar | .cursorLeftChar => LeftMoveChar_Quote
  | .rightMoveChar | .cursorRightChar => RightMoveChar_Quote
  | .leftDeleteChar => LeftDeleteChar_Quote
  | .rightDeleteChar => RightDeleteChar_Quote

def QBuffEditOp.op6 : QBuffEditOp → Op6
  | .insertChar x => .edit (.op5 (.edit (.insertChar x)))
  | .leftMoveChar => .edit (.op5 (.edit .leftMoveChar))
  | .rightMoveChar => .edit (.op5 (.edit .rightMoveChar))
  | .cursorLeftChar => .edit (.op5 (.qp .cursorLeftChar))
  | .cursorRightChar => .edit (.op5 (.qp .cursorRightChar))
  | .leftDeleteChar => .edit (.op5 (.edit .leftDeleteChar))
  | .rightDeleteChar => .edit (.op5 (.edit .rightDeleteChar))

/-- `PromoteToDoc7 ≙ ΞQuoteBuffer ∧ ΞDocState ∧ ΞDocName` -/
def PromoteToDoc7 (d d' : Doc7) : Prop :=
  d'.leftQuote = d.leftQuote ∧ d'.rightQuote = d.rightQuote ∧ d'.state = d.state ∧
  d'.name = d.name

/-- ```
∀ OP : QBuffEditOps •
    OP_Doc7 ≙ [ OP_Quote ∧ ΞDoc6 | State = State_Quote ]
            ∨ [ OP_Doc6 ∧ PromoteToDoc7 | State = State_Doc ]
```
The first part does not mention `DocState` or `DocName`, which belong to the
signature of the whole: there, `State′` and `Name′` are unconstrained. -/
def QBuffEditOp.doc7 (pageHeight : Nat) (op : QBuffEditOp) (d d' : Doc7) (rep : Report) : Prop :=
  (d.state = .quote ∧ op.quote d.toQuoteBuffer d'.toQuoteBuffer rep ∧ d'.toDoc6 = d.toDoc6) ∨
  (d.state = .doc ∧ op.op6.doc6 pageHeight d.toDoc6 d'.toDoc6 rep ∧ PromoteToDoc7 d d')

/-- **Editing the quote buffer may rename the document.** -/
theorem quoteEdit_any_name (pageHeight : Nat) {d : Doc7} (hstate : d.state = .quote)
    (n : List Char) : ∃ d' rep, (QBuffEditOp.insertChar 'x').doc7 pageHeight d d' rep ∧
      d'.name = n := by
  exact ⟨{ d with name := n }, _, .inl ⟨hstate, .inr (.inl ⟨rfl, rfl⟩), rfl⟩, rfl⟩

/-- `ErrorIllegalQBuffEditOp`: `ΞDoc7`, `State = State_Quote` (its `rep!` is
not declared). -/
def ErrorIllegalQBuffEditOp (d d' : Doc7) (rep : Report) : Prop :=
  d' = d ∧ d.state = .quote ∧ rep = "Illegal edit operation"

/-- `∀ OP : NonQBuffEditOps • OP_Doc7 ≙ [ OP_Doc6 ∧ PromoteToDoc7 | State = State_Doc ]
∨ ErrorIllegalQBuffEditOp` -/
def Op6.doc7 (pageHeight : Nat) (op : Op6) (d d' : Doc7) (rep : Report) : Prop :=
  (d.state = .doc ∧ op.doc6 pageHeight d.toDoc6 d'.toDoc6 rep ∧ PromoteToDoc7 d d') ∨
  ErrorIllegalQBuffEditOp d d' rep

end ZEditor
