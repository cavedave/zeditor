# From Z to C — The Editor Specification (definitions only)

The Z specification of the editor with all explanation, examples, lemmas and proofs removed: only the state schemas, operation schemas and definitions, in the book's order and under its section headings.

- Generated from `zeditor-part3-zspec.md` (Part Three, PDF pp.48–126). That file is the full transcription; this one is a filtered view of it. Fix transcription errors there, not here.
- Section 0 (introduction and worked examples such as `AbsStateA`) and §1.2.2 (lemmas about the word/line views) are left out entirely.
- `<!-- PDF p.N -->` gives the page where each definition is printed; `[?N]` markers refer to `corrections.csv` as before.
- A few boxes are the book's own expansions of an earlier definition (e.g. `LeftMvLine` after §1.4, `LeftMoveLine_Doc1` after §1.6, `Mv_Line` / `Del_Word` in §1.2.1). They are kept because they show what the shorthand means.

## The hierarchy at a glance

Each level includes the one below it and promotes its operations (`∀ OP : EditOpsN • OP_DocN+1 ≙ OP_DocN ∧ …`). Doc9 is the complete editor.

| Level | Adds | Section | C code (Appendix C) |
|---|---|---|---|
| Doc1 | document as `Left`/`Right` sequences of characters, words and lines; move, delete and insert | §1 | `IMPLEMENTATION OF DOC1`: gap buffer `Arr`, `LP`, `RP`, `CP` |
| Doc2 | unbounded display: document as display lines with cursor `UDCurX`, `UDCurY` | §2 | (not refined separately) |
| Doc3 | display invariants: no trailing whitespace or trailing empty lines | §3 | `IMPLEMENTATION OF DOC3` |
| QP, Doc4 | free cursor movement (the "QP" position) | §4 | `IMPLEMENTATION OF DOC4` |
| Doc5 | the mark and marked text | §5.1 | (not refined separately) |
| Doc6 | paste buffer: lift, cut, paste | §5.2 | `IMPLEMENTATION OF DOC6` |
| Doc7 | quote buffer and quoted commands: abort, save, write, append, quit, input, move-to-line, escape | §6 | (quote operations are in the DOC8 section) |
| Doc8 | search and replace with regular expressions | §7 | `IMPLEMENTATION OF DOC8` |
| Doc9 | a window onto the display; scroll, pan, centre | §8 | `IMPLEMENTATION OF DOC9`, `screen.c` |

Operations whose Z name is also a C function name (59): `Abort_Quote`, `Append_Quote`, `CentreWindow_Doc9`, `CopyMTextPBuff`, `CopyQBuffSBuff`, `CursorDown`, `CursorInWindow`, `CursorLeftChar_Doc4`, `CursorUp`, `Cut_Doc6`, `DownSearch_Doc8`, `Initialize_Doc1/3/4/6/8/9`, `Input_Quote`, `InsertChar_Doc1`, `InsertChar_Quote`, `Left/RightDeleteChar_Doc1`, `Left/RightDeleteWord_Doc1`, `Left/RightDeleteLine_Doc1`, `Left/RightMoveChar_Doc1`, `Left/RightMoveWord_Doc1`, `Left/RightMoveLine_Doc1`, `Left/RightDeleteChar_Quote`, `Left/RightMoveChar_Quote`, `Lift_Doc6`, `MoveToBot_Doc1`, `MoveToTop_Doc1`, `OP_Doc3`, `OP_Doc4`, `OP_Doc8`, `Pan`, `Paste_Doc6`, `Quit_Quote`, `Quote_StateDoc`, `Quote_StateQuote`, `ReadFromStore`, `RemMText`, `RemTrailNL`, `RemTrailWS`, `Replace_Doc8`, `Save_Quote`, `Scroll`, `ScrollAndPan`, `UpSearch_Doc8`, `WindowPolicy`, `WriteToStore`, `Write_Quote`. The `Cursor…_QP` operations correspond to the C `Cursor…_Doc4` functions (they are promoted to Doc4).

---

## 1 The Doc1 Model

### 1.1 The Generic Document

<!-- PDF p.57 -->
    Pair[X] ≙ [ Left, Right : X ]

    ΔPair[X] ≙ Pair[X] ∧ Pair′[X]

    ΞPair[X] ≙ [ ΔPair[X] | Pair[X] = Pair′[X] ]

    Ξ_Cont Pair[X] ≙ [ ΔPair[X] | Left ⁀ Right = Left′ ⁀ Right′ ]

#### 1.1.1 The Generic Move And Delete Operations

```
┌─ Mv[X] ───────────────────────
│ Ξ_Cont Pair
├───────────────────────────────
│ Left ≠ ⟨⟩
│ Left′ = front Left
└───────────────────────────────
```

```
┌─ Del[X] ──────────────────────
│ ΔPair
├───────────────────────────────
│ Left ≠ ⟨⟩
│ Left′ = front Left
│ Right′ = Right
└───────────────────────────────
```

<!-- PDF p.58 -->
```
┌─ MvBot[X] ────────────────────
│ Ξ_Cont Pair
├───────────────────────────────
│ Right ≠ ⟨⟩
│ Right′ = ⟨⟩
└───────────────────────────────
```

### 1.2 The Character, Word and Line Views Of The Document

    WhiteSpace    ≙ {sp}
    NonWhiteSpace ≙ Char − {sp, nl}

    Word · [?106] ≙ seq₁ WhiteSpace ∪ seq₁ NonWhiteSpace ∪ ⟨nl⟩
    Line          ≙ seq (Char − {nl})

<!-- PDF p.59 -->
```
┌───────────────────────────────────────────────────────────
│ DocWordSeq : ℙ (seq Word)
├───────────────────────────────────────────────────────────
│ W ∈ DocWordSeq ⇔
│     ∀ w1, w2 : Word ; w1, w2 : Word [?109] | ⟨w1, w2⟩ infix W •
│           rng [?110] (w1) = WhiteSpace ⇒ rng (w2) ≠ WhiteSpace
│           rng (w1) = NonWhiteSpace ⇒ rng (w2) ≠ NonWhiteSpace
└───────────────────────────────────────────────────────────
```

```
┌───────────────────────────────────────────────────
│ _ infix _ : seq X × seq X → 𝔹
├───────────────────────────────────────────────────
│ X1 infix X ⇔ ∃ X2, X3 : seq X • X2 ⁀ X1 ⁀ X3 = X
└───────────────────────────────────────────────────
```

```
┌───────────────────────────────
│ FW : DocWordSeq ⤖ seq Char
├───────────────────────────────
│ FW W = ⁀/ W
└───────────────────────────────
```

<!-- PDF p.60 -->
```
┌───────────────────────────────────────────────────────
│ DocLineSeq : ℙ (seq Line)
├───────────────────────────────────────────────────────
│ ∀ L : DocLineSeq ; l1, l2 : line [?111] | ⟨l1, l2⟩ infix L •
│           l1 ≠ ⟨nl⟩ ⇒ l2 = ⟨nl⟩
└───────────────────────────────────────────────────────
```

<!-- PDF p.61 -->
```
┌───────────────────────────────
│ FL : DocLineSeq ⤖ seq Char
├───────────────────────────────
│ FL L = ⁀/ L
└───────────────────────────────
```

#### 1.2.1 The Instantiated Move And Delete Operations

    Mv_Char    ≙ Mv[seq Char]
    Mv_Word    ≙ Mv[DocWordSeq]
    Mv_Line    ≙ Mv[DocLineseq]

    Del_Char   ≙ Del[seq Char]
    Del_Word   ≙ Del[DocWordSeq]
    Del_Line   ≙ Del[DocLineseq]

    MvBot_Char ≙ MvBot[seq Char]

```
┌─ Mv_Line ─────────────────────────────────
│ Left, Right, Left′, Right′ : DocLineSeq
├───────────────────────────────────────────
│ Left ⁀ Right = Left′ ⁀ Right′
│ Left ≠ ⟨⟩
│ Left′ = front Left
└───────────────────────────────────────────
```

<!-- PDF p.62 -->
```
┌─ Del_Word ────────────────────────────────
│ Left, Right, Left′, Right′ : DocWordSeq
├───────────────────────────────────────────
│ Left ≠ ⟨⟩
│ Left′ = front Left
│ Right′ = Right
└───────────────────────────────────────────
```

### 1.3 The Doc1 State

<!-- PDF p.65 -->
    Pair_Char    ≙   Pair[seq Char]
    Pair_Word    ≙   Pair[DocWordSeq]
    Pair_Line    ≙   Pair[DocLineseq] [?201]

    Left_Char    ≙   Pair_Char . Left
    Right_Char   ≙   Pair_Char . Right
    Left_Word    ≙   Pair_Word . Left
    Right_Word   ≙   Pair_Word . Right
    Left_Line    ≙   Pair_Line . Left
    Right_Line   ≙   Pair_Line . Right

```
┌─ Doc1 ──────────────────────────────────────
│ Pair_Char
│ Pair_Word
│ Pair_Line
├─────────────────────────────────────────────
│ Left_Char = FW Left_Word = FL Left_Line
│ Right_Char = FW Right_Word = FL Right_Line
└─────────────────────────────────────────────
```

    Ξ_Cont Doc1 ≙ Ξ_Cont Pair[Char] ∧ ΔDoc1

    Initialize_Doc1 ≙ [ ΔDoc1 | Left_Char′ = Right_Char′ = ⟨⟩ ]

<!-- PDF p.66 -->
    MvChar      ≙   Mv_Char      ∧   ΔDoc1
    MvWord      ≙   Mv_Word      ∧   ΔDoc1
    MvLine      ≙   Mv_Line      ∧   ΔDoc1

    DelChar     ≙   Del_Char     ∧   ΔDoc1
    DelWord     ≙   Del_Word     ∧   ΔDoc1
    DelLine     ≙   Del_Line     ∧   ΔDoc1

    McBottom [?202]  ≙   MvBot_Char   ∧   ΔDoc1

#### 1.3.1 The Insert Operation

<!-- PDF p.67 -->
```
┌─ InsNonTab ─────────────────────────
│ ΔDoc1
│ x? : Char
├─────────────────────────────────────
│ x? ≠ tab
│ Left_Char′ = Left_Char ⁀ ⟨ x? ⟩
│ Right_Char′ = Right_Char
└─────────────────────────────────────
```

```
┌─ InsTab ────────────────────────────
│ ΔDoc1
│ x? : Char
├─────────────────────────────────────
│ x? = tab
│ Left_Char prefix Left_Char′
│ rng (Left_Char′ - Left_Char) = {sp}
│ Right_Char′ = Right_Char
└─────────────────────────────────────
```

    InsChar ≙ InsNonTab ∨ InsTab

### 1.4 Introducing Direction

<!-- PDF p.68 -->
```
┌─ Mirror ────────────────────────────
│ ΔDoc1
├─────────────────────────────────────
│ Left_Char′ = rev  Right_Char
│ Right_Char′ = rev  Left_Char
└─────────────────────────────────────
```

    Mirror ; Mirror  ≙  ΞDoc1

    Right OP   ≙   Mirror ; OP ; Mirror
    Left OP    ≙   OP

    RightMvChar    ≙   Right MvChar
    LeftMvChar     ≙   Left MvChar
    RightMvWord    ≙   Right MvWord
    LeftMvWord     ≙   Left MvWord
    RightMvLine    ≙   Right MvLine
    LeftMvLine     ≙   Left MvLine

    RightDelChar   ≙   Right DelChar
    LeftDelChar    ≙   Left DelChar
    RightDelWord   ≙   Right DelWord
    LeftDelWord    ≙   Left DelWord
    RightDelLine   ≙   Right DelLine
    LeftDelLine    ≙   Left DelLine

    MvToTop        ≙   Right MvBottom
    MvToBot        ≙   Left MvBottom

<!-- PDF p.69 -->
```
┌─ LeftMvLine ────────────────────────────────
│ ΔDoc1
├─────────────────────────────────────────────
│ Left_Line ≠ ⟨⟩
│ Left_Line′ = front Left_Line
│ Left_Line′ ⁀ Right_Line′ = Left_Line ⁀ Right_Line
└─────────────────────────────────────────────
```

```
┌─ RightDelWord ──────────────────────
│ ΔDoc1
├─────────────────────────────────────
│ Right_Word ≠ ⟨⟩
│ Right_Word′ = tail Right_Word
│ Left_Word′ = Left_Word
└─────────────────────────────────────
```

### 1.5 Error Messages

    Success          ≙   [ rep! : Report | rep! = "OK" ]

    Doc1Unchanged    ≙   [ ΞDoc1 ; rep! : Report ]

```
┌─ ErrorTopOfDoc ─────────────────────
│ Doc1Unchanged
├─────────────────────────────────────
│ Left_Char = ⟨⟩
│ rep! = "At top of document"
└─────────────────────────────────────
```

<!-- PDF p.70 -->
```
┌─ ErrorBotOfDoc ─────────────────────
│ Doc1Unchanged
├─────────────────────────────────────
│ Right_Char = ⟨⟩
│ rep! = "At bottom of document"
└─────────────────────────────────────
```

```
┌─ ErrorFull ─────────────────────────
│ Doc1Unchanged
├─────────────────────────────────────
│ rep! = "Editor full"
└─────────────────────────────────────
```

### 1.6 The Total Operations On The Doc1 State

    RightMoveChar_Doc1     ≙   (RightMvChar ∧ Success)     ∨   ErrorBotOfDoc
    LeftMoveChar_Doc1      ≙   (LeftMvChar ∧ Success)      ∨   ErrorTopOfDoc
    RightMoveWord_Doc1     ≙   (RightMvWord ∧ Success)     ∨   ErrorBotOfDoc
    LeftMoveWord_Doc1      ≙   (LeftMvWord ∧ Success)      ∨   ErrorTopOfDoc
    RightMoveLine_Doc1     ≙   (RightMvLine ∧ Success)     ∨   ErrorBotOfDoc
    LeftMoveLine_Doc1      ≙   (LeftMvLine ∧ Success)      ∨   ErrorTopOfDoc

    RightDeleteChar_Doc1   ≙   (RightDelChar ∧ Success)    ∨   ErrorBotOfDoc
    LeftDeleteChar_Doc1    ≙   (LeftDelChar ∧ Success)     ∨   ErrorTopOfDoc
    RightDeleteWord_Doc1   ≙   (RightDelWord ∧ Success)    ∨   ErrorBotOfDoc
    LeftDeleteWord_Doc1    ≙   (LeftDelWord ∧ Success)     ∨   ErrorTopOfDoe [?203]
    RightDeleteLine_Doc1   ≙   (RightDelLine ∧ Success)    ∨   ErrorBotOfDoc
    LeftDeleteLine_Doc1    ≙   (LeftDelLine ∧ Success)     ∨   ErrorTopOfDoc

    InsertChar_Doc1        ≙   (InsChar ∧ Success)         ∨   ErrorFull

    MoveToTop_Doc1         ≙   (MvToTop ∧ Success)         ∨   ErrorTopOfDoc
    MoveToBot_Doc1         ≙   (MvToBot ∧ Success)         ∨   ErrorBotOfDoc

<!-- PDF p.71 -->
```
┌─ LeftMoveLine_Doc1 ─────────────────────────
│ ΔDoc1
│ rep! : Report
├─────────────────────────────────────────────
│ Left_Line′ ⁀ Right_Line′ = Left_Line ⁀ Right_Line
│     Left_Line ≠ ⟨⟩
│     Left_Line′ = front Left_Line
│     rep! = "OK"
│ ∨
│     Left_Line = Left_Line′ = ⟨⟩
│     rep! = "At top of document"
└─────────────────────────────────────────────
```

```
┌─ RightDeleteWord_Doc1 ──────────────────────
│ ΔDoc1
│ rep! : Report
├─────────────────────────────────────────────
│ Left_Word′ = Left_Word
│     Right_Word ≠ ⟨⟩
│     Right_Word′ = tail Right_Word
│     rep! = "OK"
│ ∨
│     Right_Word = Right_Word′ = ⟨⟩
│     rep! = "At bottom of document"
└─────────────────────────────────────────────
```

## 2 Unbounded Display Of The Document

### 2.1 An Unbounded Display Model

<!-- PDF p.72 -->
    DispLine  ==  seq (Char - {nl})

<!-- PDF p.73 -->
```
┌─ UD ────────────────────────────────
│ UDLines : seq₁ DispLine
│ UDCurX, UDCurY : ℕ₁
│ UDCurLine : DispLine
├─────────────────────────────────────
│ UDCurY ≤ # UDLines
│ UDCurLine = UDLines UDCurY
│ UDCurX ≤ # UDCurLine + 1
└─────────────────────────────────────
```

### 2.2 The Doc2 State

<!-- PDF p.74 -->
```
┌───────────────────────────────────────────────
│ FDL : seq₁ DispLine ⤖ seq Char
├───────────────────────────────────────────────
│ ∀ L1, L2 : seq₁ DispLine ; l : DispLine •
│     FDL (⟨ l ⟩) = l
│     FDL (L1 ⁀ L2) = (FDL L1) ⁀ ⟨ nl ⟩ ⁀ (FDL L2)
└───────────────────────────────────────────────
```

<!-- PDF p.76 -->
```
┌─ Doc2 ──────────────────────────────────────────────────
│ Doc1
│ UD
├─────────────────────────────────────────────────────────
│ UDLines = FDL⁻¹ (Left_Char ⁀ Right_Char)
│ UDCurLine = last (FDL⁻¹ Left_Char) ⁀ first (FDL⁻¹ Right_Char)
│ UDCurY = [?206] #(FDL⁻¹ Left_Char)
│ UDCurX = #(last FDL⁻¹ Left_Char) + 1
└─────────────────────────────────────────────────────────
```

<!-- PDF p.77 -->
    Initialize_Doc2  ≙  Initialize_Doc1 ∧ ΔDoc2

### 2.3 Promotion Of The Doc1 Operations To The Doc2 State

    MoveOps     ≙   { RightMoveChar, LeftMoveChar,
                      RightMoveWord, LeftMoveWord,
                      RightMoveLine, LeftMoveLine,
                      MoveTopDoc, MoveBotDoc          }

    DeleteOps   ≙   { RightDeleteChar, LeftDeleteChar,
                      RightDeleteWord, LeftDeleteWord,
                      RightDeleteLine, LeftDeleteLine    }

    InsertOp    ≙   { InsertChar }

    EditOps1  ≙  MoveOps ∪ DeleteOps ∪ InsertOp

    ∀ OP : EditOps1 • OP_Doc2 ≙ OP_Doc1 ∧ ΔDoc2

## 3 Invariants On The Unbounded Display Model

### 3.1 The Doc3 State

<!-- PDF p.78 -->
```
┌───────────────────────────────────────
│ visible _ : DispLine → 𝔹
├───────────────────────────────────────
│ visible l ⇔ (l ≠ ⟨⟩ ⇒ last l ≠ sp)
└───────────────────────────────────────
```

```
┌───────────────────────────────────────────────
│ visibleseq _ : seq DispLine → 𝔹
├───────────────────────────────────────────────
│ visibleseq L ⇔ (L ≠ ⟨⟨⟩⟩ ⇒ last L ≠ ⟨⟩)
└───────────────────────────────────────────────
```

<!-- PDF p.79 -->
```
┌─ Doc3 ──────────────────────────────────────────────────
│ Doc2
├─────────────────────────────────────────────────────────
│ ∀ i : 1 .. # UDLines - {UDCurY} • visible (UDLines i)
│ visible (UDCurLine after UDCurX - 1)
│ visibleseq (UDLines after UDCurY)
└─────────────────────────────────────────────────────────
```

```
┌───────────────────────────────────────
│ _ after _ : seq X × ℕ → seq X
├───────────────────────────────────────
│ S after N = sucᴺ ; (1 .. N ⩤ [?209] S)
└───────────────────────────────────────
```

    Initialize_Doc3  ≙  Initialize_Doc2

### 3.2 Two Relations That Tidy The Display

```
┌───────────────────────────────────────────────────
│ _ visible_prefix _ : DispLine × DispLine → 𝔹
├───────────────────────────────────────────────────
│ L′ visible_prefix L ⇔ visible L′ ∧ rng (L - L′) ⊆ {sp}
└───────────────────────────────────────────────────
```

<!-- PDF p.80 -->
```
┌───────────────────────────────────────────────────────────
│ _ visibleseq_prefix _ : seq₁ DispLine × seq₁ DispLine → B
├───────────────────────────────────────────────────────────
│ L′ visibleseq_prefix L  ⇔  visibleseq L′ ∧ rng (L − L′) ⊆ { ⟨⟩ }
└───────────────────────────────────────────────────────────
```

### 3.3 Promotion of Doc2 Operations to the Doc3 State

<!-- PDF p.82 -->
```
┌─ RemTrailWS ──────────────────
│ ΔUD
│ prevCP? : ℕ
├───────────────────────────────
│ UDCurX′, UDCurY′ = UDCurX, UDCurY
│ {prevUDCurY} ⩤ UDLines′ = {prevUDCurY} ⩤ UDLines
│     prevUDCurY = UDCurY
│     UDCurLine′ for UDCurX − 1 = UDCurLine for UDCurX − 1
│     (UDCurLine′ after UDCurX − 1) visible prefix (UDCurLine after UDCurX − 1)
│ ∨
│     prevUDCurY ≠ UDCurY
│     (UDLines′ prevUDCurY) visible_prefix (UDLines prevUDCurY)
│ where
│     prevUDCurY = #(FDL⁻¹((Left_Char ⁀ Right_Char) for prevCP?))
└───────────────────────────────
```

```
┌─ RemTrailNL ──────────────────
│ ΔUD
├───────────────────────────────
│ UDCurX′, UDCurY′ = UDCurX, UDCurY
│ UDLines′ for UDCurY = UDLines for UDCurY
│ (UDLines′ after UDCurY) visibleseq prefix (UDLines after UDCurY)
└───────────────────────────────
```

    FlagPrevCursor ≙ [ Left_Char : seq Char ; prevCP! : ℕ | prevCP! = # Left_Char ]

        OP_Doc3 ≙ FlagPrevCursor ; OP_Doc2 ; RemTrailWS ; RemTrailNL

## 4 Cursor Movement

### 4.1 The QP State

<!-- PDF p.83 -->
    QP ≙ [ QPCurX, QPCurY : ℕ₁ ]

    QPHorizMove  ≙  [ ΔQP | QPCurY′ = QPCurY ]
    QPVertMove   ≙  [ ΔQP ; y : ℕ₁ | QPCurX′ = QPCurX ]

```
┌─ QPCurUp ─────────────────────
│ QPVertMove
├───────────────────────────────
│ QPCurY − y > 0
│ QPCurY′ = QPCurY − y
└───────────────────────────────
```

```
┌─ QPCurDown ───────────────────
│ QPVertMove
├───────────────────────────────
│ QPCurY′ = QPCurY + y
└───────────────────────────────
```

<!-- PDF p.84 -->
```
┌─ QPCurLeft ───────────────────
│ QPHorizMove
├───────────────────────────────
│ QPCurX > 1
│ QPCurX′ = QPCurX − 1
└───────────────────────────────
```

```
┌─ QPCurRight ──────────────────
│ QPHorizMove
├───────────────────────────────
│ QPCurX′ = QPCurX + 1
└───────────────────────────────
```

```
┌─ ErrorAtTopPage ──────────────
│ ΞQP
│ y : ℕ [?305]
│ rep! : Report
├───────────────────────────────
│ QPCurY − y ≤ 0
│ rep! = "At top page of document"
└───────────────────────────────
```

```
┌─ ErrorQPAtTop ────────────────
│ ΞQP
│ rep! : Report
├───────────────────────────────
│ QPCurX = QPCurY = 1
│ rep! = "At top of document"
└───────────────────────────────
```

<!-- PDF p.85 -->
```
┌─ QPCurToPrevLine ─────────────
│ ΔQP
├───────────────────────────────
│ QPCurX = 1
│ QPCurY > 1
│ QPCurY′ = QPCurY − 1
└───────────────────────────────
```

    CursorUp      ≙     QPCurUp ∧ Success
                      ∨
                        ErrorAtTopPage
    CursorDown    ≙   QPCurDown ∧ Success
    CursorLeft    ≙     QPCurLeft ∧ Success
                      ∨
                        QPCurToPrevLine ∧ Success
                      ∨
                        ErrorQPTop
    CursorRight   ≙   QPCurRight ∧ Success

    CursorUpChar_QP     ≙  [ QPCursorUp     |  y = 1 ]
    CursorUpPage_QP     ≙  [ QPCursorUp     |  y = PageHeight ]
    CursorDownChar_QP   ≙  [ QPCursorDown   |  y = 1 ]
    CursorDownPage_QP   ≙  [ QPCursorDown   |  y = PageHeight ]
    CursorLeftChar_QP   ≙  QPCursorLeft
    CursorRightChar_QP  ≙  QPCursorRight

### 4.2 The Doc4 State

<!-- PDF p.86 -->
    Doc4 ≙ [ Doc3 ∧ QP | UDCurX = QPCurX ∧ UDCurY = QPCurY ]

    Initialize_Doc4  ≙  Initialize_Doc3 [?306] ∧ ΔDoc4

#### 4.2.1 Promotion Of The Doc3 Operations To The Doc4 State

```
┌─ EquateQPWithUD ──────────────
│ QP′
│ UDCurX, UDCurY : ℕ
├───────────────────────────────
│ QPCurX′, QPCurY′ = UDCurX, UDCurY
└───────────────────────────────
```

    ∀ OP : EditOps1  •  OP_Doc4 ≙ (OP_Doc3 ; EquateQPWithUD) ∧ ΔDoc4

#### 4.2.2 Promotion Of The QP Operations To The Doc4 State

<!-- PDF p.87 -->
```
┌─ EquateUDWithQP ──────────────
│ QP
│ UDCurX′, UDCurY′ : ℕ
├───────────────────────────────
│ UDCurX′, UDCurY′ = QPCurX, QPCurY
└───────────────────────────────
```

<!-- PDF p.88 -->
```
┌─ PadWSNL ─────────────────────
│ ΔUD
│ EquateUDWithQP
├───────────────────────────────
│     QPCurY ≤ # UDLines
│     {QPCurY} ⩤ UDLines′ = {QPCurY} ⩤ UDLines
│     UDLines QPCurY visible_prefix UDCurLine′
│ ∨
│     QPCurY > # UDLines
│     # UDLines′ = QPCurY
│     UDLines prefix UDLines′
│     ∀ i : # UDLines + 1 .. QPCurY − 1 • UDLines′ i = ⟨⟩
│     rng (UDCurLine′) ⊆ {sp}
└───────────────────────────────
```

    CursorLeftChar_Doc4  ≙  LeftMoveChar_Doc3 ∧ ΔDoc4

    QPCursorOps  ≙  { CursorUpChar, CursorDownChar,
                      CursorUpPage, CursorDownPage,
                      CursorLeftChar, CursorRightChar }

        OP_Doc4  ≙  FlagPrevCursor ;
                        SuccOP_QP [?308] ; PadWSNL ;
                        RemTrailWS ; RemTrailNL ∧ ΔDoc4
                    ∨
                        UnSuccOP_QP ∧ ΞDoc4
                    ∨
                        ErrorFull ∧ ΞDoc4

<!-- PDF p.89 -->
    SuccOP_QP    ≙  [ OP_QP | rep! = "OK" ]
    UnSuccOP_QP  ≙  [ OP_QP | rep! ≠ "OK" ]

## 5 Text Manipulation Operations

### 5.1 The Doc5 State And Marked Text

```
┌─ MarkedText ──────────────────
│ MarkSeq, MarkedSeq : seq Char
│ Pair_Char
├───────────────────────────────
│     MarkSeq = MarkedSeq = ⟨⟩
│ ∨
│     MarkSeq ⁀ MarkedSeq = Left_Char
│ ∨
│     MarkedSeq ⁀ MarkSeq = Right_Char
└───────────────────────────────
```

<!-- PDF p.90 -->
    Doc5 ≙ Doc4 ∧ MarkedText

    Initialize_Doc5 ≙ [ Initialize_Doc4 ∧ ΔDoc5 | MarkSeq = MarkedSeq = ⟨⟩ ]

#### The Operation To Set The Mark

```
┌─ SetMk ───────────────────────
│ MarkedText′
│ Pair_Char
├───────────────────────────────
│ MarkSeq′ = Left_Char
│ MarkedSeq′ = ⟨⟩
└───────────────────────────────
```

    SetMark_Doc5 ≙ SetMk ∧ ΞDoc4 ∧ ΔDoc5 ∧ Success

#### 5.1.1 Promotion Of The Doc4 Operations To The Doc5 State

<!-- PDF p.91 -->
    ResetMark  ≙  [ ΔMarkedText | MarkSeq′ = MarkedSeq′ = ⟨⟩ ]

    NonCursorOps          ≙  DeleteOps ∪ InsertOp
    CursorOps             ≙  MoveOps ∪ QPCursorOps − NonCursorOps
    CursorOps_NoMarkSet   ≙  CursorOps | MarkSeq′ = MarkedSeq′ = ⟨⟩
    CursorOps_MarkSet     ≙  CursorOps | MarkSeq′ ⁀ MarkedSeq′ ≠ ⟨⟩

    ∀ OP : NonCursorOps          •  OP_Doc5 ≙ OP_Doc4 [?309] ∧ ResetMark
    ∀ OP : CursorOps_NoMarkSet [?310]  •  OP_Doc5 ≙ OP_Doc4 ∧ ΞMarkedText
    ∀ OP : CursorOps_MarkSet     •  OP_Doc5 ≙ OP_Doc4 [?311] ∧ ΔMarkedText

### 5.2 The Doc6 State And The Lift, Cut And Paste Operations

    PasteBuffer  ≙  [ PBuff : seq Char ]
    Doc6         ≙  Doc5 ∧ PasteBuffer

    Initialize_Doc6 ≙ [ Initialize_Doc5 ∧ ΔDoc6 | PBuff′ = ⟨⟩ ]

#### The Lift Operation

<!-- PDF p.92 -->
```
┌─ CopyMTextPBuff ──────────────
│ ΔPasteBuffer
│ Left_Char
│ MarkedText
├───────────────────────────────
│ PBuff′ = MarkedSeq ≠ ⟨⟩
└───────────────────────────────
```

```
┌─ ErrorNoTextMarked ───────────
│ ΞDoc6
│ rep! : Report
├───────────────────────────────
│ MarkedSeq = ⟨⟩
│ rep! = "No text marked"
└───────────────────────────────
```

    Lift_Doc6  ≙    CopyMTextPBuff ∧ ΞDoc5 ∧ ΔDoc6 ∧ Success
                  ∨
                    ErrorNoTextMarked

#### The Cut Operation

```
┌─ RemMText ────────────────────
│ ΔPair_Char
│ ΔMarkedText
├───────────────────────────────
│ MarkSeq′ = Markedseq′ [?312] = ⟨⟩
│ MarkSeq ⁀ MarkedSeq = Left_Char  ⇒  Left_Char′ = MarkSeq
│                                     Right_Char′ = Right_Char
│ MarkedSeq ⁀ MarkSeq = Left_Char [?313]  ⇒  Right_Char′ = MarkSeq
│                                     Left_Char′ = Left_Char
└───────────────────────────────
```

    Cut_Doc6  ≙  FlagPrevCursor ;
                     CopyMTextPBuff ; RemMText ;
                     RemTrailWS ; RemTrailNL ∧ Success
                 ∨
                     ErrorNoTextMarked

#### The Paste Operation

<!-- PDF p.93 -->
```
┌─ Pst ─────────────────────────
│ ΔPair_Char
│ ΔMarkedText
│ PasteBuffer
├───────────────────────────────
│ PBuff ≠ ⟨⟩
│ Left_Char′ = Left_Char ⁀ PBuff
│ Right_Char′ = Right_Char
│ MarkSeq′ = Left_Char
│ MarkedSeq′ = ⟨⟩
└───────────────────────────────
```

```
┌─ ErrorPBuffEmpty ─────────────
│ ΞDoc6
│ rep! : Report
├───────────────────────────────
│ PBuff = ⟨⟩
│ rep! = "Paste buffer empty"
└───────────────────────────────
```

    Paste_Doc6  ≙  FlagPrevCursor ;
                       Pst ; RemTrailWS ; RemTrailNL ∧ ΔDoc6 ∧ Success
                   ∨
                       ΞDoc6 ∧ ErrorFull
                   ∨
                       ErrorPBuffEmpty

#### 5.2.1 Promotion Of The Doc5 Operations To The Doc6 State

    EditOps2  ≙  CursorOps ∪ NonCursorOps ∪ {Mark}

    ∀ OP : EditOps2  •  OP_Doc6 ≙ OP_Doc5 ∧ ΞPasteBuffer

## 6 Quote Commands

### 6.1 The Quote Buffer

<!-- PDF p.94 -->
```
┌─ QuoteBuffer ─────────────────
│ Left_Quote, Right_Quote : seq Char
│ QBuff : seq Char
├───────────────────────────────
│ QBuff = Left_Quote ⁀ Right_Quote
└───────────────────────────────
```

#### 6.1.1 Operations To Edit The Quote Buffer

```
┌─ QteInsChar ──────────────────
│ ΔQuoteBuffer
│ x? : Char
├───────────────────────────────
│ x? ≠ tab
│ Left_Quote′ = Left_Quote ⁀ ⟨x?⟩
│ Right_Quote′ = Right_Quote
└───────────────────────────────
```

<!-- PDF p.95 -->
```
┌─ QteLeftDelChar ──────────────
│ ΔQuoteBuffer
├───────────────────────────────
│ Left_Quote ≠ ⟨⟩
│ Left_Quote′ = front Left_Quote
│ Right_Quote′ = Right_Quote
└───────────────────────────────
```

```
┌─ QteRightDelChar ─────────────
│ ΔQuoteBuffer
├───────────────────────────────
│ Right_Quote ≠ ⟨⟩
│ Left_Quote′ = Left_Quote
│ Right_Quote′ = tail Right_Quote
└───────────────────────────────
```

```
┌─ QteLeftMvChar ───────────────
│ ΔQuoteBuffer
├───────────────────────────────
│ Left_Quote ≠ ⟨⟩
│ Left_Quote′ ⁀ Right_Quote′ = Left_Quote ⁀ Right_Quote
│ Left_Quote′ = front Left_Quote
└───────────────────────────────
```

```
┌─ QteRightMvChar ──────────────
│ ΔQuoteBuffer
├───────────────────────────────
│ Right_Quote ≠ ⟨⟩
│ Left_Quote′ ⁀ Right_Quote′ = Left_Quote ⁀ Right_Quote
│ Right_Quote′ = tail Right_Quote
└───────────────────────────────
```

    ErrorQuote  ≙  [ ΞQuoteBuffer ; rep! : Report ]

```
┌─ ErrorIllegalCharacter ───────
│ ErrorQuote
│ x? : Char
├───────────────────────────────
│ x? = tab
│ rep! = "Illegal quote character"
└───────────────────────────────
```

<!-- PDF p.96 -->
```
┌─ ErrorQuoteFull ──────────────
│ ErrorQuote
├───────────────────────────────
│ rep! = "Quote buffer full"
└───────────────────────────────
```

```
┌─ ErrorTopQuote ───────────────
│ ErrorQuote
├───────────────────────────────
│ Left_Quote = ⟨ ⟩
│ rep! = "At top of quote buffer"
└───────────────────────────────
```

```
┌─ ErrorBotQuote ───────────────
│ ErrorQuote
├───────────────────────────────
│ Right_Quote = ⟨ ⟩
│ rep! = "At bottom of quote buffer"
└───────────────────────────────
```

```
InsertChar_Quote        ≙   (QteInsChar ∧ Success) ∨ ErrorQuoteFull ∨
                                    ErrorIllegalCharacter
LeftDeleteChar_Quote    ≙   (QteLeftDelChar ∧ Success) ∨ ErrorTopQuote
RightDeleteChar_Quote   ≙   (QteRightDelChar ∧ Success) ∨ ErrorBotQuote
LeftMoveChar_Quote      ≙   (QteLeftMvChar ∧ Success) ∨ ErrorTopQuote
RightMoveChar_Quote     ≙   (QteRightMvChar ∧ Success) ∨ ErrorBotQuote
```

### 6.2 Operating System I/O

<!-- PDF p.97 -->
```
┌─ SysGetPtr ───────────────────
│ filename? : seq Char
│ filemode?, filemode! : {⟨r⟩, ⟨w⟩, ⟨a⟩}
│ Sysptr! : Ptr
├───────────────────────────────
│ filemode! = filemode?
└───────────────────────────────
```

    SuccSysGetPtr    ≙  [ SysGetPtr | Sysptr! ≠ NullPtr ]
    UnSuccSysGetPtr  ≙  [ SysGetPtr | Sysptr! = NullPtr ]

    Store ≙ [ FStore : Ptr → Cont ]

<!-- PDF p.98 -->
```
┌───────────────────────────────
│ storedseq : Cont → seq Char
└───────────────────────────────
```

```
┌─ SysWrite ────────────────────
│ ΔStore
│ Sysptr? : Ptr
│ WriteSeq? : seq Char
│ filemode? : {⟨w⟩, ⟨a⟩}
│ NoWriteError! : 𝔹
├───────────────────────────────
│ ¬ NoWriteError!  ⇒  FStore = FStore′
│ NoWriteError! ∧ filemode? = ⟨w⟩ ⇒
│         {Sysptr?} ⩤ FStore′ = {Sysptr?} ⩤ FStore
│         storedseq(FStore′ Sysptr?) = WriteSeq?
│ NoWriteError! ∧ filemode? = ⟨a⟩ ⇒
│ Sysptr? ∈ dom FStore
│         {Sysptr?} ⩤ FStore′ = {Sysptr?} ⩤ FStore
│         storedseq(FStore′ Sysptr?) = storedseq(FStore Sysptr?) ⁀ WriteSeq?
└───────────────────────────────
```

    SuccSysWrite    ≙  [ SysWrite | NoWriteError! ]
    UnSuccSysWrite  ≙  [ SysWrite | ¬ NoWriteError! ]

```
┌─ SysRead ─────────────────────
│ ΞStore
│ Sysptr? : Ptr
│ ReadSeq! : seq Char
│ filemode? : {⟨r⟩}
│ NoReadError! : 𝔹
├───────────────────────────────
│ ¬ NoReadError!  ⇒  ReadSeq! = storedseq(FStore Sysptr?)
└───────────────────────────────
```

<!-- PDF p.99 -->
    SuccSysRead    ≙  [ SysRead | NoReadError! ]
    UnSuccSysRead  ≙  [ SysRead | ¬ NoReadError! ]

    ErrorCannotOpenFile  ≙  [ rep! : Report | rep! = "Cannot open file" ]
    ErrorWritingFile     ≙  [ rep! : Report | rep! = "Error writing file" ]
    ErrorReadingFile     ≙  [ rep! : Report | rep! = "Error reading file" ]

```
WriteToStore ≙
        SuccSysGetPtr ≫ SuccSysWrite ∧ Success
    ∨
        SuccSysGetPtr ≫ UnSuccSysWrite ∧ ErrorWritingFile
    ∨
        UnSuccSysGetPtr ∧ ErrorCannotOpenFile
```

    SuccWriteToStore    ≙  [ WriteToStore | rep! = "OK" ]
    UnSuccWriteToStore  ≙  [ WriteToStore | rep! ≠ "OK" ]

    ErrorReadFull ≙ [ rep! : Report | rep! = "Editor full" ]

```
ReadFromStore ≙
        SuccSysGetPtr ≫ SuccSysRead ∧ Success
    ∨
        SuccSysGetPtr ≫ UnSuccSysRead ∧ ErrorReadingFile
    ∨
        UnSuccSysGetPtr ∧ ErrorCannotOpenFile
    ∨
        SuccGetSysPtr ∧ ErrorReadFull
```

    SuccReadFromStore    ≙  [ ReadFromStore | rep! = "OK" ]
    UnSuccReadFromStore  ≙  [ ReadFromStore | rep! ≠ "OK" ]

### 6.3 The Doc7 State

<!-- PDF p.100 -->
    DocState  ≙  [ State : {State_Doc, State_Quote} ]
    DocName   ≙  [ Name : seq Char ]
    Doc7      ≙  Doc6 ∧ QuoteBuffer ∧ DocState ∧ DocName

```
┌─ Initialize_Doc7 ─────────────
│ Initialize_Doc6[?403]
│ ΔDoc7
│ filename? : seq Char
├───────────────────────────────
│ QBuff′ = ⟨ ⟩
│ State′ = State_Doc
│ Name′ = filename?
└───────────────────────────────
```

### 6.4 Quoted Operations

```
┌─ Quote_StateDoc ──────────────
│ ΔDoc7
│ ΞDoc6
│ rep! : Report
├───────────────────────────────
│ Name′ = Name
│ State = State_Doc
│ State′ = State_Quote
│ QBuff′ = ⟨ ⟩
│ rep! = "OK"
└───────────────────────────────
```

<!-- PDF p.101 -->
```
┌─ QuoteRequest ────────────────
│ ΔDoc7
│ ΞDocName
│ ΞPasteBuffer
│ ΞQuoteBuffer
│ filename! : seq Char
│ filemode! : {⟨r⟩, ⟨w⟩, ⟨a⟩}
├───────────────────────────────
│ State = State_Quote
│ State′ = State_Doc
└───────────────────────────────
```

    QuoteRequestContentChange ≙ [ QuoteRequest | MarkSeq′[?404] = MarkedSeq = ⟨ ⟩ ]

    QuoteRequestNoChange ≙ QuoteRequest ∧ ΞDoc5[?405]

#### 6.4.1 The Abort Command

<!-- PDF p.102 -->
```
┌─ RequestAbort ────────────────
│ QuoteRequestNoChange
├───────────────────────────────
│ ⟨a, b, o, r, t⟩ = QBuff
│ rep! = "OK"
└───────────────────────────────
```

    Abort_Quote ≙ RequestAbort ; SysReturnControl

#### 6.4.2 The Save Command

    ErrorDocNotChanged ≙ [ rep! : Report | rep! = "Document not changed" ]

<!-- PDF p.103 -->
```
┌─ RequestSave ─────────────────
│ QuoteRequestNoChange
│ WriteSeq! : seq Char
├───────────────────────────────
│ ⟨s⟩ = QBuff
│ filemode! = ⟨w⟩
│ WriteSeq! = Left_Char ⁀ Right_Char
│ filename! = Name
└───────────────────────────────
```

```
Save_Quote ≙
        RequestSave ≫ WriteToStore
    ∨
        RequestSave ≫ ErrorDocNotChanged
```

#### 6.4.3 The Write And Append Commands

```
┌───────────────────────────────
│ _ prefix₁ _ : seq X × seq X → 𝔹
├───────────────────────────────
│ S prefix₁ T  ⇔  S prefix T ∧ S ≠ T
└───────────────────────────────
```

```
┌─ RequestWriteMarkedText ──────
│ QuoteRequestNoChange
│ WriteSeq! : seq Char
├───────────────────────────────
│ ⟨w, sp⟩ prefix₁ QBuff
│ filemode! = ⟨w⟩
│ filename! = QBuff after 2
│ WriteSeq! = MarkedSeq
└───────────────────────────────
```

<!-- PDF p.104 -->
```
┌─ RequestAppendMarkedText ─────
│ QuateRequestNoChange[?407]
│ WriteSeq! : seq Char
├───────────────────────────────
│ ⟨a, sp⟩ prefix₁ QBuff
│ filemode! = ⟨a⟩
│ filename! = QBuff after 2
│ WriteSeq! = MarkedSeq
└───────────────────────────────
```

```
Write_Quote ≙
        [RequestWriteMarkedText | MarkedSeq ≠ ⟨ ⟩] ≫ WriteToStore
    ∨
        RequestWriteMarkedText ∧ ErrorNoTextMarked
```

```
Append_Quote ≙
        [RequestAppendMarkedText | MarkedSeq ≠ ⟨ ⟩] ≫ WriteToStore
    ∨
        RequestAppendMarkedText ∧ ErrarNoTextMarked[?408]
```

#### 6.4.4 The Quit Command

```
┌─ RequestQuit ─────────────────
│ QuoteRequestNoChange
│ WriteSeq! : seq Char
├───────────────────────────────
│ WriteSeq! = MarkedSeq
│ ⟨q⟩ = QBuff
│ filename! = Name
│ filemode! = ⟨w⟩
│ WriteSeq! = Left_Char ⁀ Right_Char
└───────────────────────────────
```

<!-- PDF p.105 -->
```
Quit_Quote ≙
        RequestQuit ≫ SuccWriteToStore ; SysReturnControl
    ∨
        RequestQuit ≫ ErrorDocNotChanged ; SysReturnControl
    ∨
        RequestQuit ≫ UnSuccWriteToStore
```

#### 6.4.5 The Input Command

```
┌─ RequestInput ────────────────
│ QuoteRequestContentChange
├───────────────────────────────
│ ⟨i, sp⟩ prefix₁ QBuff
│ filemode! = ⟨r⟩
│ filename! = QBuff after 2
└───────────────────────────────
```

```
┌─ InputReadSeq ────────────────
│ ΔDocI[?409]
│ ReadSeq? : seq Char
├───────────────────────────────
│ Left_Char′ = Left_Char ⁀ ReadSeq?
│ Right_Char′ = Right_Char
└───────────────────────────────
```

    ErrorFileNotExist     ≙  [ rep! : Report | rep! = "File does not exist" ]
    ErrorUnsuitableFile   ≙  [ rep! : Report | rep! = "Unsuitable file" ]

<!-- PDF p.106 -->
```
Input_Quote ≙
    FlagPrevCursor ;
            (RequestInput ≫ SuccReadFromStore ≫ InputReadSeq) ;
            RemTrailWS ; RemTrailNL
        ∨
            RequestInput ≫ UnSuccReadFromStore
        ∨
            RequestInput ∧ ΞDoc5 ∧ ErrorFileNotExist
        ∨
            RequestInput ∧ ΞDoc5 ∧ UnsuitableFile
        ∨
            RequestInput ∧ ΞDoc5 ∧ ErrorFull
```

#### 6.4.6 The Move To Line Number Command

```
┌─ RequestMvLineNumber ─────────
│ QuoteRequestContentChange
├───────────────────────────────
│ ran QBuff ⊆ NumChar
│ DocCurX′ = 1
│ DocCurY′ = min (ConvNum QBuff, # UDLines)
└───────────────────────────────
```

<!-- PDF p.107 -->
```
MoveLineNumber_Quote ≙
        (FlagPrevCursor ; RequestMvLineNumber ;
        RemTrailWS ; RemTrailNL) ∧ Success
```

#### 6.4.7 The Escape Command

```
┌─ Escape.ProvideText[?411] ────
│ QuoteRequestNoChange
│ commandseq! : seq Char
├───────────────────────────────
│ # QBuff > 1
│ ⟨!⟩ prefix₁ QBuff
│ commandseq! = tail QBuff
└───────────────────────────────
```

```
┌─ ErrorNoCommandGiven ─────────
│ QuoteRequestNoChange
│ rep! : Report
├───────────────────────────────
│ ⟨!⟩ = QBuff
│ rep! = "No command given"
└───────────────────────────────
```

```
Eseape_Quote[?412] ≙
        Escape.ProvideText ≫ SysInterpret ∧ Success
    ∨
        ErrorNoCommmandGiven[?413]
```

### 6.5 The Quote Command

<!-- PDF p.108 -->
    ValidQBuffContent  ≙  { ⟨a, b, o, r, t⟩, ⟨q⟩, ⟨s⟩, ⟨!⟩ }

    ValidQBuffPrefix   ≙  { ⟨a, sp⟩, ⟨i, sp⟩, ⟨w, sp⟩, ⟨!⟩ }

```
┌─ ValidQBuffText ──────────────
│ QuoteBuffer
├───────────────────────────────
│     ∃ s : ValidQBuffContent • s = QBuff
│ ∨
│     ∃ s : ValidQBuffPrefix • s prefix₁ QBuff
│ ∨
│     rng QBuff ⊆ NumChar
└───────────────────────────────
```

```
┌─ ErrorQuoteError ─────────────
│ QuoteRequestNoChange
│ ¬ ValidQBuffText
│ rep! : Report
├───────────────────────────────
│ rep! = "Quote error"
└───────────────────────────────
```

```
Quote_StateQuote  ≙  Abort_Quote   ∨  Save_Quote  ∨  Write_Quote  ∨
                     Append_Quote  ∨  Quit_Quote  ∨  Input_Quote  ∨
                     Escape_Quote  ∨  ErrorQuoteError
```

    Quote_Doc7  ≙  Quote_StateDoc ∨ Quote_StateQuote

### 6.6 Promotion Of Quote Buffer Edit Operations To The Doc7 State

<!-- PDF p.109 -->
```
QBuffEditOps  ≙  { InsertChar, LeftMoveChar, RightMoveChar,
                   CursorLeftChar, CursorRightChar,
                   LeftDeleteChar, RightDeleteChar }
```

    PromoteToDoc7 ≙ ΞQuoteBuffer ∧ ΞDocState ∧ ΞDocName

```
∀ OP : QBuffEditOps •
    OP_Doc7  ≙      [ OP_Quote[?414] ∧ ΞDoc6 | State = State_Quote ]
                ∨
                    [ OP_Doc6 ∧ PromoteToDoc7 | State = State_Doc ]
```

### 6.7 Promotion Of Remaining Doc6 Operations To The Doc7 State

    EditOps3 ≙ EditOps2 ∪ { Lift, Cut, Paste, ExchMTextPBuff }

    NonQBuffEditOps ≙ EditOps3 − QBuffEditOps

```
┌─ ErrorIllegalQBuffEditOp ─────
│ ΞDoc7
├───────────────────────────────
│ State = State_Quote
│ rep! = "Illegal edit operation"
└───────────────────────────────
```

<!-- PDF p.110 -->
```
∀ OP : NonQBuffEditOps •
    OP_Doc7  ≙      [ OP_Doc6 ∧ PromoteToDoc7 | State = State_Doc ]
                ∨
                    ErrorIllegalQBuffEditOp
```

## 7 The Search And Replace Operations

### 7.1 The Doc8 State

    SearchBuffer   ≙  [ SBuff : seq Char ]
    ReplaceBuffer  ≙  [ RBuff : seq Char ]
    Doc8           ≙  Doc7 ∧ SearchBuffer ∧ ReplaceBuffer

    Initialize_Doc8 ≙ [ Initialize_Doc7 ∧ ΔDoc8 | SBuff′ = RBuff′ = ⟨ ⟩ ]

### 7.2 Regular Expressions

<!-- PDF p.111 -->
```
┌───────────────────────────────
│ _ regexpmatches _ : RegExpression × seq Char → 𝔹
├───────────────────────────────
│ e regexpmatches s  ⇒  # e ≥ s[?416]
└───────────────────────────────
```

```
┌───────────────────────────────
│ _ matches _ : seq Char × seq Char → 𝔹
├───────────────────────────────
│ ∀ e : RegExpression ; s1, s2 ∈ seq Char | s1 ∉ RegExpression •
│         e matches s2  ⇔  e regexpmatches s[?417]
│         s1 matches s2  ⇔  s1 prefix s2
└───────────────────────────────
```

### 7.3 The Down Search Operation

<!-- PDF p.112 -->
```
┌─ SearchOp ────────────────────
│ Ξ_Cont Doc1
│ ΞSearchBuffer
│ ΔDocState
├───────────────────────────────
│ SBuff ≠ ⟨⟩
│ State′ = State_Doc
└───────────────────────────────
```

```
┌───────────────────────────────
│ matchedlength : seq Char × seq Char ⇸ ℕ
├───────────────────────────────
│ (s1, s2) ∈ dom matchedlength  ⇔  s1 matches s2
└───────────────────────────────
```

```
┌─ SuccDownSch_Doc ─────────────
│ SearchOp
├───────────────────────────────
│ State = State_Doc
│ # Right_Char ≥ # SBuff
│ SBuff matches Right_Char′
│ ¬(∃ S in n .. m ↿ (Left_Char ⁀ Right_Char) • SBuff matches S)   [?501]
│ where
│     n, m = (# Left_Char + 2), (# Left_Char′ + matchedlength (SBuff, Right_Char′) − 1)
└───────────────────────────────
```

<!-- PDF p.113 -->
```
┌─ CopyQBuffSBuff ──────────────
│ ΔSearchBuffer
│ ΔDocState
│ QuoteBuffer
├───────────────────────────────
│ State = State_Quote
│ State′ = State_Doc
│ SBuff′ = QBuff
└───────────────────────────────
```

    SuccDownSch_Quote ≙ CopyQBuffSBuff ; SuccDownSch_Doc

```
┌─ UnSuccDownSch_Doc ───────────
│ SearchOp
│ ΞDoc1
├───────────────────────────────
│ State = State_Doc
│ SBuff ≠ ⟨⟩
│ ¬ (∃ S in (tail Right_Char) • SBuff matches S)
└───────────────────────────────
```

    UnSuceDownSch_Quote [?502] ≙ CopyQBuffSBuff ; UnSuccDownSch_Doc

    RepStringNotFound ≙ [ rep! : Report | rep! = "String not found" ]

```
┌─ ErrorSBuffEmpty_Doc ─────────
│ ΞDoc8
│ rep! : Report
├───────────────────────────────
│ State = State_Doc
│ SBuff = ⟨⟩
│ rep! = "Search buffer empty"
└───────────────────────────────
```

    ErrorSBuffEmpty_Quote ≙ CopyQBuffSBuff ; ErrorSBuffEmpty_Doc

<!-- PDF p.114 -->
    SuccDownSearch    ≙ SuccDownSch_Doc ∨ SuccDownSch_Quote
    UnSuccDownSearch  ≙ UnSuccDownSch_Doc ∨ UnSuccDownSch_Quote
    ErrorSBuffEmpty   ≙ ErrorSBuffEmpty_Doc ∨ ErrorSBuffEmpty_Quote

```
┌─ PromoteSearch ───────────────
│ ΔDoc8
│ Ξ_Cont Doc1
│ ΔMarkedText
│ ΞPasteBuffer
│ ΞQuoteBuffer
│ ΞDocName
│ ΞReplaceBuffer
└───────────────────────────────
```

    PromoteSearchUnMark    ≙ [ PromoteSearch | MarkSeq = MarkedSeq′ = ⟨⟩ ]   [?503]
    PromoteSearchLeaveMark ≙ PromoteSearch ∧ ΞMarkedText

```
DownSearch_Doc8 ≙
    FlagPrevCursor ;
        SuccDownSearch ; RemTrailWS ; RemTrailNL ∧
        PromoteSearchUnMark ∧ Success
    ∨
        UnSuccDownSearch ∧ PromoteSearchLeaveMark ∧ RepStringNotFound
    ∨
        ErrorSBuffEmpty
```

### 7.4 The Up Search Operation

<!-- PDF p.115 -->
```
┌─ SuccUpSch_Doc ───────────────
│ SearchOp
├───────────────────────────────
│ State = State_Doc
│ # Left_Char ≥ # SBuff
│ SBuff matches Right_Char′
│ ¬ (∃ S in n .. m ↿ (Left_Char ⁀ Right_Char) • SBuff matches S)   [?504]
│ where
│     n, m = (# Left_Char′ + 2), (# Left_Char + matchedlength (SBuff, Right_Char′) − 1)
└───────────────────────────────
```

    SuccUpSch_Quote ≙ CopyQBuffSBuff ; SuccUpSch_Doc

```
┌─ UnSuccUpSch_Doc ─────────────
│ SearchOp
│ ΞDoc1
├───────────────────────────────
│ State = State_Doc
│ SBuff ≠ ⟨⟩
│ ¬ (∃ S in (front Left_Char) • SBuff matches S)
└───────────────────────────────
```

    UnSuccUpSch_Quote ≙ CopyQBuffSBuff ; UnSuccUpSch_Doc

    SuccUpSearch   ≙ SuccUpSch_Doc ∨ SuccUpSch_Quote
    UnSuccUpSearch ≙ UnSuccUpSch_Doc ∨ UnSuccUpSch_Quote

```
UpSearch_Doc8 [?505] ≙
    FlagPrevCursor ;
        SuccUpSearch ; RemTrailWS ; RemTrailNL ∧
        PromoteSearchUnMark ∧ Success
    ∨
        UnSuccUpSearch ∧ PromoteSearchLeaveMark ∧ RepStringNotFound
    ∨
        ErrorSBuffEmpty
```

### 7.5 The Replace Operation

<!-- PDF p.116 -->
```
┌─ RemMatchedText ──────────────
│ ΔDoc1
│ ΞDocState
│ SearchBuffer
├───────────────────────────────
│ SBuff matches Right_Char
│ Right_Char′ = Right_Char after matchedlength (SBuff, Right_Char)
│ Left_Char′ = Left_Char
│ State = State_Doc
└───────────────────────────────
```

```
┌─ InsRBuffText ────────────────
│ ΔDoc1
│ ReplaceBuffer
├───────────────────────────────
│ Right_Char′ = RBuff ⁀ Right_Char
│ Left_Char′ = Left_Char
└───────────────────────────────
```

    SuccRpl_Doc ≙ RemMatehedText [?506] ; InsRBuffText

    CopyQBuffRBuff ≙ CopyQBuffSBuff[ReplaceBuffer \ SearchBuffer]   [?507]

    SuccRpl_Quote ≙ CopyQBuffRBuff ; SuccRpl_Doc

<!-- PDF p.117 -->
```
┌─ UnSuccRpl_Doc ───────────────
│ ΞDoc1
│ ΞDocState
│ SearchBuffer
├───────────────────────────────
│ ¬ (SBuff matches Right_Char)
│ State = State_Doc
└───────────────────────────────
```

    UnSuccRpl_Quote ≙ CopyQBuffRBuff ; UnSuccRpl_Doc

```
┌─ RepNoMatchSBuff ─────────────
│ rep! : Report
├───────────────────────────────
│ rep! = "No match with search buffer"
└───────────────────────────────
```

```
┌─ PromoteReplace ──────────────
│ ΔDoc8
│ Ξ_Cont Doc1
│ ΔMarkedText
│ ΞPasteBuffer
│ ΞQuoteBuffer
│ ΞDocName
│ ΞSearchBuffer
└───────────────────────────────
```

    PromoteReplaceUnMark    ≙ [ PromoteReplace | MarkSeq = MarkedSeq′ = ⟨⟩ ]   [?508]
    PromoteReplaceLeaveMark ≙ PromoteReplace ∧ ΞMarkedText

```
┌─ ErrorReplaceFull_Doc ────────
│ ΞDoc8
├───────────────────────────────
│ State = State_Doc
│ rep! = "Editor full"
└───────────────────────────────
```

<!-- PDF p.118 -->
    ErrorReplaceFull_Quote ≙ CopyQBuffRBuff ; ErrorReplaceFull_Doc
    ErrorReplaceFull       ≙ ErrorReplaceFull_Doc ∨ ErrorReplaceFull_Quote

    SuccReplace   ≙ SuccRpl_Doc ∨ SuccRpl_Quote
    UnSuccReplace ≙ UnSuccRpl_Doc ∨ UnSuccRpl_Quote

```
Replace_Doc8 ≙
    FlagPrevCursor ;
        SuccReplace ; RemTrailWS ; RemTrailNL ∧
        PromoteReplaceUnMark ∧ Success
    ∨
        UnSuccReplace ∧ PromoteReplaceLeaveMark ∧ RepNoMatchSBuff
    ∨
        ErrorReplaceFull
```

### 7.6 Promotion Of The Doc7 Operations To The Doc8 State

    EditOps4 ≙ EditOps3 ∪ { Quote }

```
∀ OP : EditOps4 •
        OP_Doc8 ≙ OP_Doc7 ∧ ΞSearchBuffer ∧ ΞReplaceBuffer
```

## 8 A Window On To the Display

### 8.1 The Window State

<!-- PDF p.119 -->
    WindowOffset ≙ [ OffsetX, OffsetY : ℕ ]

```
┌─ WindowCursor ────────────────
│ WinCurX, WinCurY : ℕ₁
├───────────────────────────────
│ 1 ≤ WinCurX ≤ WinWidth
│ 1 ≤ WinCurY ≤ WinHeight
└───────────────────────────────
```

```
┌─ Window ──────────────────────
│ WindowLines : seq₁ DispLine
│ WindowOffset
│ WindowCursor
├───────────────────────────────
│ # WindowLines ≤ WinHeight
│ ∀ y : 1 .. # WinLines • #(WindowLines y) ≤ WinWidth
└───────────────────────────────
```

### 8.2 The Doc9 State

<!-- PDF p.121 -->
```
┌─ Doc9 ────────────────────────
│ Doc8
│ Window
├───────────────────────────────
│ WinCurX, WinCurY = UDCurX − OffsetX, UDCurY − OffsetY
│ WindowLines = (WinMaskLines after OffsetY) for WinHeight
│ where
│     # WinMaskLines = # UDLines
│     ∀ y : 1 .. # UDLines •
│             WinMaskLines y = ((UDLines y) after OffsetX) for WinWidth
└───────────────────────────────
```

<!-- PDF p.122 -->
    Initialize_Doc9 ≙ Initialize_Doc8 ∧ ΔDoc9

#### 8.2.1 An Operation To Centre The Window

<!-- PDF p.124 -->
```
┌─ CenWin ──────────────────────
│ ΔDoc9
│ ΞDoc8
├───────────────────────────────
│ UDCurY ≥ HalfWinHeight
│ OffsetX′ = OffsetX
│ OffsetY′ = UDCurY − HalfWinHeight
└───────────────────────────────
```

```
┌─ ErrorTooNearTop ─────────────
│ ΞDoc9
│ rep! : Report
├───────────────────────────────
│ UDCurY < HalfWinHeight
│ rep! = "Too near top of document"
└───────────────────────────────
```

    CentreWindow_Doc9 ≙ (CenWin ∧ Success) ∨ ErrorTooNearTop

#### 8.2.2 Promotion Of Doc8 Operations To The Doc9 State

<!-- PDF p.125 -->
```
┌─ CursorInWindow ──────────────
│ ΔWindowOffset
│ ΞDoc8
├───────────────────────────────
│ UDCurX − OffsetX ∈ 1 .. WinWidth
│ UDCurY − OffsetY ∈ 1 .. WinHeight
│ UDCurX′ − OffsetX′ ∈ 1 .. WinWidth
│ UDCurY′ − OffsetY′ ∈ 1 .. WinHeight
└───────────────────────────────
```

```
┌─ Scroll ──────────────────────
│ ΔWindowOffset
│ ΞDoc8
├───────────────────────────────
│ UDCurX − OffsetX ∈ 1 .. WinWidth
│ UDCurY − OffsetY ∉ 1 .. WinHeight
│ OffsetX′ = OffsetX
│ UDCurY′ − OffsetY′ ∈ 1 .. WinHeight
└───────────────────────────────
```

```
┌─ Pan ─────────────────────────
│ ΔWindowOffset
│ ΞDoc8
├───────────────────────────────
│ UDCurX − OffsetX ∉ 1 .. WinWidth
│ UDCurY − OffsetY ∈ 1 .. WinHeight
│ UDCurX′ − OffsetX′ ∈ 1 .. WinWidth
│ OffsetY′ = OffsetY
└───────────────────────────────
```

<!-- PDF p.126 -->
```
┌─ ScrollAndPan ────────────────
│ ΔWindowOffset
│ ΞDoc8
├───────────────────────────────
│ UDCurX − OffsetX ∉ 1 .. WinWidth
│ UDCurY − OffsetY ∉ 1 .. WinHeight
│ UDCurX′ − OffsetX′ ∈ 1 .. WinWidth
│ UDCurY′ − OffsetY′ ∈ 1 .. WinHeight
└───────────────────────────────
```

```
WindowPolicy ≙
        (CursorInWindow ∨ Scroll ∨ Pan ∨ ScrollAndPan) ∧ Doc9′
```

    EditOps5 ≙ EditOps4 ∪ {DownSearch, UpSearch, Replace}

    ∀ OP : EditOps5 • OP_Doc9 ≙ OP_Doc8 [?512] ; WindowPolicy

