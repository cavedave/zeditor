# From Z to C — Part Three: Z Specification Of A Full Screen Text Editor (PDF pages 48–126)

Source: `../source/Zeditor.pdf` (Neilson, PRG-101, 1990), printed pp.45–123. Transcribed from page images.

Conventions (as in `zeditor-p001-020.md`, plus):
- `<!-- PDF p.N / printed p.M -->` marks each scanned page.
- `[?N]` marks a doubtful spot; N is the ID column in `corrections.csv` (IDs 101–599 for this part).
- Original spellings, typos and apparent errors in the original are kept as printed. Exception: the scan regularly blurs "u" into "n" in prose ("docnment"); those are written as the intended word without a flag.
- Boxed schemas are drawn with `┌─ Name ─`, `├──` (divider) and `└──` in code blocks; unnamed (axiomatic/generic) boxes start with `┌───`. Indentation of predicates is significant (aligned lines are conjoined).
- Multi-letter subscripts, which have no Unicode form, are written with an underscore: `Left_Char`, `OP_Doc4`, `Ξ_Cont`. Single-digit subscripts use Unicode (`C₀`).
- Sequence brackets are written ⟨ ⟩; bold B/P/N as 𝔹/ℙ/ℕ; relational image ⦇ ⦈.

---

<!-- PDF p.48 / printed p.45 -->

# PART THREE

# Z Specification Of A Full Screen Text Editor

## Contents

- **0 Introduction** — **48**
  - 0.1 The Hierarchy Of Abstract States — 49
  - 0.2 A Note Regarding Specification Convention — 49
  - 0.3 Specification Proof Obligations — 50
- **1 The Doc1 Model** — **53**
  - 1.1 The Generic Document — 53
    - 1.1.1 The Generic Move And Delete Operations — 54
  - 1.2 The Character, Word and Line Views Of The Document — 55
    - 1.2.1 The Instantiated Move And Delete Operations — 58
    - 1.2.2 Some Results Concerning Characters, Words And Lines — 59
  - 1.3 The Doc1 State — 61
    - 1.3.1 The Insert Operation — 64
  - 1.4 Introducing Direction — 64
  - 1.5 Error Messages — 66

<!-- PDF p.49 / printed p.46 -->

  - 1.6 The Total Operations On The Doc1 State — 67
- **2 Unbounded Display Of The Document** — **69**
  - 2.1 An Unbounded [?101] Display Model — 69
  - 2.2 The Doc2 State — 70
  - 2.3 Promotion Of The Doc1 Operations To The Doc2 State — 74
- **3 Invariants On The Unbounded Display Model** — **75**
  - 3.1 The Doc3 State — 75
  - 3.2 Two Relations That Tidy The Display — 76
  - 3.3 Promotion of Doc2 Operations to the Doc3 State — 78
- **4 Cursor Movement** — **80**
  - 4.1 The QP State — 80
  - 4.2 The Doc4 State — 82
    - 4.2.1 Promotion Of The Doc3 Operations To The Doc4 State — 83
    - 4.2.2 Promotion Of The QP Operations To The Doc4 State — 83
- **5 Text Manipulation Operations** — **86**
  - 5.1 The Doc5 State And Marked Text — 86
    - 5.1.1 Promotion Of The Doc4 Operations To The Doc5 State — 87
  - 5.2 The Doc6 State And The Lift, Cut And Paste Operations — 88
    - 5.2.1 Promotion Of The Doc5 Operations To The Doc6 State — 90
- **6 Quote Commands** — **91**
  - 6.1 The Quote Buffer — 91
    - 6.1.1 Operations To Edit The Quote Buffer — 91
  - 6.2 Operating System I/O — 94
  - 6.3 The Doc7 State — 97
  - 6.4 Quoted Operations — 97

<!-- PDF p.50 / printed p.47 -->

    - 6.4.1 The Abort Command — 99
    - 6.4.2 The Save Command [?102] — 99
    - 6.4.3 The Write And Append Commands — 100
    - 6.4.4 The Quit Command — 101
    - 6.4.5 The Input Command — 102
    - 6.4.6 The Move To Line Number Command — 103
    - 6.4.7 The Escape Command — 104
  - 6.5 The Quote Command — 105
  - 6.6 Promotion Of Quote Buffer Edit Operations To The Doc7 State — 106
  - 6.7 Promotion Of Remaining Doc6 Operations To The Doc7 State — 106
- **7 The Search And Replace Operations** — **107**
  - 7.1 The Doc8 State — 107
  - 7.2 Regular Expressions — 108
  - 7.3 The Down Search Operation — 108
  - 7.4 The Up Search Operation — 111
  - 7.5 The Replace Operation — 113
  - 7.6 Promotion Of The Doc7 Operations To The Doc8 State — 115
- **8 A Window On To the Display** — **115**
  - 8.1 The Window State — 116
  - 8.2 The Doc9 State — 116
    - 8.2.1 An Operation To Centre The Window — 120
    - 8.2.2 Promotion Of Doc8 Operations To The Doc9 State — 121

<!-- PDF p.51 / printed p.48 -->

## 0 Introduction

We present a formal specification of a screen-oriented text editor, written in **Z** [19], [?103] [27], [28] and using the Schema Calculus [20].

The specification is developed in a hierarchical manner such that the abstract data representation being currently specified is an embellishment of the previous one. We start with a simple abstract representation of the editor, successively enriching it until we finally have a complete mathematical model. Each abstract data type (an abstract data representation together with an initialisation and a family of operations) is thus embedded in succeeding hierarchies. This technique ensures that each step isolates a specific problem, enabling clear specification objectives, and supporting the concept of "separation of concerns" [1]. Thus at each hierarchy of the specification we are able to specify additional operations (requiring the enriched state) and "promote" existing operations (i.e. re-specify each one on the embellished state, such that its original characteristics are retained).

Where possible we employ an orthogonal development method: the orthogonal model is constructed outside the main model, the two having no common state. The orthogonal model is subsequently introduced into the main model through logical (schema) conjunction, with the possible addition of an invariant indicating the way in which the two are related. This method leaves the main model uncluttered by, for example, the necessary or desirable establishment of theory.

Further, we use generic constructions, in which families of concepts may be captured in a single definition, enabling a theory on the formal generic parameter to be constructed, rather than having to develop like theories for each actual generic parameter.

Each operation specified is total. Typically an operation is specified in several stages using schema inclusion, conjunction and/or disjunction, and an operation with an inherent pre-condition is made total by disjunction with an "error" schema, in a similar way to that presented in [8].

This specification uses many of the ideas put forward in [25], which in turn was heavily motivated by [29]; the latter was written in **Z** but did not employ the Schema Calculus (which hadn't then been fully developed) and employed "higher order" functions (functions that take other functions as arguments) to achieve a hierarchical structure. We gratefully acknowledge that paper as a source of inspiration for this specification.

We summarize our requirements as the editor [32], together with the facility to move the cursor around the quarter plane in which the document resides (rather than just around the document itself), and the provisos that no line may end in whitespace (other than the current line when the cursor is at the right hand end - otherwise it would be impossible to insert a space character at the end of a line) and that the document may not have trailing empty lines; neither can be detected on the terminal screen. An editor should inspire the confidence of the user [6], and without these latter two requirements a move to the bottom of the document or end of line, for example, could have (literally!)

<!-- PDF p.52 / printed p.49 -->

unforeseen consequences. We extend the quote operations (operations not effected by single keystrokes, but requiring the input of text into a buffer) to include the writing and appending of marked text to a named file, and exclude the exchange marked text with paste buffer operation of the editor [32] (since the latter operation may be accomplished by the former).

### 0.1 The Hierarchy Of Abstract States

Our first simple abstract representation of the editor is the *Doc1* model (Section 1) in which we use a pair of sequences to capture both the content and the current position of a document, the latter being the point at which changes to the document may be made. This model incorporates equivalent character, word and line "views"; we discuss their relationship and specify a change of current position and the insertion and deletion of text by using the view which is most appropriate.

We model the document's display by first considering an unbounded display specification, *UD*, orthogonal to that of the document specified in *Doc1*, which models the display as a sequence of display lines, incorporating a cursor and a cursor line. We conjoin the two models into *Doc2* (Section 2), in which we give the relationship between the contents and current position of a document to its unbounded display and cursor position.

We then "tidy" the display of the document to the *Doc3* model (Section 3), by requiring that the trailing whitespace/null lines requirements are met.

We define the *QP* state (Section 4) in which cursor movement around the quarter plane is developed orthogonally to the main model, subsequently conjoining *QP* with *Doc3* to give the *Doc4* model, in which we require that the cursors of *UD* and *QP* are equivalent.

Further *Doc* models introduce the remaining edit operations. In Section 5 we specify the text manipulation operations concerned with marking text (*Doc5*), and lifting, cutting and pasting text (*Doc6*). Section 6 is concerned with commands which cannot be activated by a single keystroke - for example commands requiring textual input - the Quote commands (*Doc7*). In Section 7 we specify commands which permit the searching for and replacing of text (*Doc8*).

After all edit operations have been specified, our last development is to introduce a movable window on to the unbounded display of the document, Section 8, and we define the top-level hierarchical state, *Doc9*, which represents our complete mathematical model of the editor.

For convenience, we give a summary of the specification state hierarchies in Appendix A.

### 0.2 A Note Regarding Specification Convention

We continue to use the convention that vertically aligned predicates imply their logical

<!-- PDF p.53 / printed p.50 -->

conjunction (see **Part 2**, Section 0.1).

Also we use the convention that, for example, "*string*" represents the sequence of characters ⟨s, t, r, i, n, g⟩.

The reader should refer to [28] for a full description of the **Z** notation: anything not provided by that library will be defined as it is required.

### 0.3 Specification Proof Obligations

We consider proof obligations that ensure that a possible implementation for the specification exists (thereby ensuring that we have not specified an unimplementable system).

Each specification representation will include an invariant on the state variables (in simple cases this will be the type of the variables), and our first proof obligation is to show that the initialization operation establishes that invariant. Defining our abstract variables as AS⃗, our state invariant as abs_inv AS⃗ and denoting our initialisation as *Init* which has after-state variables AS⃗′, we may formally define our first proof obligation as:

```
⊢                                                        PO 0
   ∃ AS⃗′ • Init ∧ abs_inv AS⃗′
```

For example, if our abstract state comprises two variables *a* and *b*, with state invariant that both are natural numbers together with the requirement that *a* must not exceed *b*, and the initialisation sets both to zero, our proof obligation is:

```
⊢
   ∃ a′, b′ • a′ = 0 ∧ b′ = 0 ∧ a′ ∈ ℕ ∧ b′ ∈ ℕ ∧ a′ ≤ b′
```

simplifying to:

```
0 ∈ ℕ ∧ 0 ≤ 0
```

Once the state invariant has been established by the initialization operation, we are obliged to show that each subsequent operation preserves the invariant, assuming the pre-condition of the operation: if operation *Op* has before-state variables AS⃗ and after-state variables AS⃗′, we must show that:

```
   abs_inv (AS⃗) ∧ pre[Op]
⊢                                                        PO 1
   ∃ AS⃗′ • Op ∧ abs_inv (AS⃗′)
```

<!-- PDF p.54 / printed p.51 -->

Using the example given above, suppose an operation *Op* has the pre-condition that *a* is non-zero and decreases *a* by *1* leaving *b* unchanged, our proof obligation is:

```
   a ∈ ℕ ∧ b ∈ ℕ ∧ a ≤ b ∧ a ≠ 0
⊢
   ∃ a′, b′ • a′ = a − 1 ∧ b′ = b ∧ a′ ∈ ℕ ∧ b′ ∈ ℕ ∧ a′ ≤ b′
```

simplifying to

```
a ∈ ℕ₁ ⇒ a − 1 ∈ ℕ
a ∈ ℕ₁ ∧ b ∈ ℕ ∧ a ≤ b ⇒ a − 1 ≤ b
```

Notice that since since both *a′* and *b′* were explicitly set by the operation, the existential quantifier disappears (by the "one-point" rule). When the operation is non-deterministic, however, this is not the case.

For example by defining the operation on the "*Δ*" abstract state (for an example, see Section 1.3) the before- and after-invariant is frozen in to the specification of the operation, and any variables not explicitly set are thus allowed to change to any value consistent with the state invariant.

Continuing with the same example, suppose another operation is defined on *ΔAbsState* (where *AbsState* incorporates the state invariant that *a* and *b* are natural numbers with *a* not exceeding *b*) which has the same pre-condition, decreases *a* by *1*, but leaves *b* non-deterministic. Our proof obligation is:

```
   a ∈ ℕ ∧ b ∈ ℕ ∧ a ≤ b ∧ a ≠ 0
⊢
   ∃ a′, b′ • a′ = a − 1 ∧ a′ [?104] ∈ ℕ ∧ b′ ∈ ℕ ∧ a′ ≤ b′
```

which simplifies to:

```
a ∈ ℕ₁  ⇒  a − 1 ∈ ℕ
           ∃ b′ • b′ ∈ ℕ ∧ b′ ≥ a − 1
```

We employ an orthogonal method of specification development, combining the orthogonal models using schema conjunction with (usually) an invariant cementing the relationship between the two states (for an example, see Section 2.2). In order to identify our proof obligation we could expand the conjoined state and the proof obligations outlined above would apply. However, if we have already discharged the obligations for each orthogonal state, we may lighten our proof obligation load.

<!-- PDF p.55 / printed p.52 -->

Suppose a state *AbsStateA* incorporates variables AS⃗ with invariant A_abs_inv, and another state *AbsStateB* has variables BS⃗ with invariant B_abs_inv, and we schema-conjoin the states to form *AbsStateC*, adding the invariant C_abs_inv. Thus the conjoined state comprises both sets of variables on which both invariants, as well as the additional invariant, holds.

If an operation *Op*, defined on AS⃗ and preserving A_abs_inv, is promoted to *AbsStateC* through logical conjunction with *ΔAbsStateC*, we must show that *Op* does not violate the invariant of the orthogonally specified state B_abs_inv, by showing the existence of an after state of *AbsStateB* under C_abs_inv, assuming the pre-condition of the operation:

```
   A_abs_inv (AS⃗) ∧ A_abs_inv (AS⃗′) ∧ pre[Op]
⊢                                                        PO 2
   ∃ BS⃗′ • Op ∧ C_abs_inv (AS⃗′, BS⃗′) ∧ B_abs_inv (BS⃗′)
```

For example, suppose we have:

    AbsStateA ≙ [ a, b [?105] : ℕ | a ≤ b ]
    AbsStateB ≙ [ s, t : ℕ | s ≤ t ]

with operations:

    OpA ≙ [ ΔAbsStateA | a′ = 1 ∧ b′ = 2 ]
    OpB ≙ [ ΔAbsStateB | s ≠ 0 ∧ s′ = s − 1 ∧ t′ = s ]

Suppose we have discharged all proof obligations, and we wish to specify a composite state *AbsStateC*, where:

    AbsStateC ≙ [ AbsStateA ∧ AbsStateB | b = s ]

For *OpA* (which is total, and so its pre-condition is therefore *true*), we must show the existence of an after-state of *AbsStateB*, under the invariant of *AbsStateC*:

```
   a ∈ ℕ ∧ b ∈ ℕ ∧ a ≤ b ∧ a′ ∈ ℕ ∧ b′ ∈ ℕ ∧ a′ ≤ b′
⊢
   ∃ s′, t′ • a′ = 1 ∧ b′ = 2 ∧ b′ = s′ ∧ s′ ∈ ℕ ∧ t′ ∈ ℕ ∧ s′ ≤ t′
```

which simplifies to:

```
∃ t′ • t′ ∈ ℕ ∧ t′ ≥ 2
```

For *OpB*, we must show the existence of an after-state of *AbsStateA*, under the invariant of *AbsStateC*:

<!-- PDF p.56 / printed p.53 -->

```
   s ∈ ℕ ∧ t ∈ ℕ ∧ s ≤ t ∧ s′ ∈ ℕ ∧ t′ ∈ ℕ ∧ s′ ≤ t′ ∧ s ≠ 0
⊢
   ∃ a′, b′ • s′ = s − 1 ∧ t′ = s ∧
              b′ = s′ ∧ a′ ∈ ℕ ∧ b′ ∈ ℕ ∧ a′ ≤ b′
```

which simplifies to:

```
s ∈ ℕ₁  ⇒  s − 1 ∈ ℕ
           ∃ a′ • a′ ∈ ℕ ∧ a′ ≤ s − 1
```

Note that we may achieve the same specification by renaming *s* to *b* in *AbsStateB*, in which case *AbsStateC* would require no additional invariant (and so C_abs_inv would just be *true*). In this case the same proof obligation applies.

Often the discharge of these proof obligations will be trivial (particularly type obligations); when this is not the case, we give a proof that the obligation is met, or indicate how it may be discharged.

Of course we may choose to do more than just meet the specification proof obligations, and state (or prove) further properties relating to the specification which, we feel, may give further insight into the system, increase our confidence in the model we are building, or demonstrate conformity to our initial (informal) requirements.

## 1 The Doc1 Model

### 1.1 The Generic Document

The two essential characteristics of the state of a document being edited are its contents and current position; changes made to the contents of a document will take place at that position. These two characteristics may be captured by representing a document as a pair of sequences, one corresponding to the part of the document preceding, and the other to that part which follows the current position. The contents will thus be the concatenation of the two sequences.

A document may thus be modelled as a pair of sequences of *characters*. However it is often convenient to represent the document as a pair of sequences of *words* or *lines* (for instance when moving the cursor by a word or line at a time, rather than a character at a time). Therefore our initial definitions will use the formal parameter *X*, which we will instantiate by the sets of actual generic parameters of sequences of characters, words and lines to give three different, but equivalent, views of the document:

<!-- PDF p.57 / printed p.54 -->

    Pair[X] ≙ [ Left, Right : X ]

We use the symbol "*Δ*" throughout the specification to represent the conjunction of a before-state (undashed) and an after-state (dashed):

    ΔPair[X] ≙ Pair[X] ∧ Pair′[X]

and the symbol "*Ξ*" to represent a no change *Δ*-state:

    ΞPair[X] ≙ [ ΔPair[X] | Pair[X] = Pair′[X] ]

Finally, we use "*Ξ_Cont*" to represent a before- and after-document whose content hasn't changed (i.e. it allows for a change of current position):

    Ξ_Cont Pair[X] ≙ [ ΔPair[X] | Left ⁀ Right = Left′ ⁀ Right′ ]

#### 1.1.1 The Generic Move And Delete Operations

We specify the basic operations move (left) and delete (left): the former has the pre-condition that *Left* must not be empty, its last element being moved to the beginning of *Right*:

```
┌─ Mv[X] ───────────────────────
│ Ξ_Cont Pair
├───────────────────────────────
│ Left ≠ ⟨⟩
│ Left′ = front Left
└───────────────────────────────
```

and the latter has the same pre-condition, but this operation discards the last element of *Left*, leaving *Right* unchanged:

```
┌─ Del[X] ──────────────────────
│ ΔPair
├───────────────────────────────
│ Left ≠ ⟨⟩
│ Left′ = front Left
│ Right′ = Right
└───────────────────────────────
```

We also specify an operation which moves the current position to the end of the document, with pre-condition that that must not already be the current position:

<!-- PDF p.58 / printed p.55 -->

```
┌─ MvBot[X] ────────────────────
│ Ξ_Cont Pair
├───────────────────────────────
│ Right ≠ ⟨⟩
│ Right′ = ⟨⟩
└───────────────────────────────
```

### 1.2 The Character, Word and Line Views Of The Document

A *Word* may be defined as a non-empty sequence of characters which consist entirely of whitespace (space characters) or non-whitespace (no spaces or newlines), or the unit sequence whose element is the newline character. A *Line* may be defined as a (possibly empty) sequence of characters not containing the newline character. We therefore introduce two special characters:

    sp, nl : Char | sp ≠ nl

and define:

    WhiteSpace    ≙ {sp}
    NonWhiteSpace ≙ Char − {sp, nl}

to give:

    Word · [?106] ≙ seq₁ WhiteSpace ∪ seq₁ NonWhiteSpace ∪ ⟨nl⟩
    Line          ≙ seq (Char − {nl})

We wish to define a total bijective function that converts a sequence of characters into a unique sequence of words; if we consider the sequence of characters:

    ⟨t, h, e, sp, sp, c [?107], a, t⟩

we want the corresponding word sequence to be:

    ⟨⟨t, h, e,⟩, ⟨sp, sp⟩, ⟨c, a, t,⟩⟩ [?108]

so that each member of the sequence satisfies the definition of *Word*, and the sequence flattens (through distributed concatenation) into the character sequence. However the following word sequence also satisfies those requirements:

    ⟨⟨t, h, e⟩, ⟨sp⟩, ⟨sp⟩, ⟨c, a⟩, ⟨t⟩⟩

In order to obtain the desired word view of the document, therefore, we must not allow two *Whitespace* words or two *NonWhiteSpace* words to be adjacent in that representation. Clearly, this requirement will ensure a unique word sequence for each sequence of characters. We define:

<!-- PDF p.59 / printed p.56 -->

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

where:

```
┌───────────────────────────────────────────────────
│ _ infix _ : seq X × seq X → 𝔹
├───────────────────────────────────────────────────
│ X1 infix X ⇔ ∃ X2, X3 : seq X • X2 ⁀ X1 ⁀ X3 = X
└───────────────────────────────────────────────────
```

As a direct consequence of this definition, if we have two *DocWordSequences* such that their distributed concatenation is equal, the sequences themselves are equal:

    **Corollary 3 : 1.2a**

        W1, W2 : DocWordSeq | ⁀/ W1 = ⁀/ W2
      ⊢
        W1 = W2

      ■

Since by definition of "⁀/", if two sequences are equal, so is their distributed concatenation, we now define the required one-to-one function, FW (FlattenWords):

```
┌───────────────────────────────
│ FW : DocWordSeq ⤖ seq Char
├───────────────────────────────
│ FW W = ⁀/ W
└───────────────────────────────
```

The sequence of words corresponding to the empty sequence of characters is the empty sequence of words:

    **Lemma 3 : 1.2b**

        C = ⟨⟩
      ⊢
        FW⁻¹ C = ⟨⟩

      ■

**Proof**

<!-- PDF p.60 / printed p.57 -->

Follows directly from the definition of FW, since ⁀/(⟨⟩) = ⟨⟩
■

We also wish to define an analogous function that transforms the line view of the document into the character view. For example, we want the sequence of characters:

    ⟨c, a, n, a, r, y⟩

to correspond to the line sequence:

    ⟨⟨c, a, n, a, r, y⟩⟩

and the character sequence:

    ⟨t, h, e, nl, c, a, n, a, r, y, nl, nl, a, t, e⟩

to correspond to the line sequence:

    ⟨⟨t, h, e⟩, ⟨nl⟩, ⟨c, a, n, a, r, y⟩, ⟨nl⟩, ⟨nl⟩, ⟨a, t, e⟩⟩

so that the line sequence flattens (through distributed concatenation) to the character sequence. In order to ensure that each line view is unique, we define a *DocLineSeq*, analogous to *DocWordseq*, requiring that two non-newline words may not be adjacent in the representation:

```
┌───────────────────────────────────────────────────────
│ DocLineSeq : ℙ (seq Line)
├───────────────────────────────────────────────────────
│ ∀ L : DocLineSeq ; l1, l2 : line [?111] | ⟨l1, l2⟩ infix L •
│           l1 ≠ ⟨nl⟩ ⇒ l2 = ⟨nl⟩
└───────────────────────────────────────────────────────
```

As a direct consequence of this definition, if we have two *DocLineSequences* such that their distributed concatenation is equal, the sequences themselves are equal:

    **Corollary 3 : 1.2c**

        L1, L2 : DocLineSeq | ⁀/ L1 = ⁀/ L2
      ⊢
        L1 = L2

      ■

Since by definition of "⁀/", if two sequences are equal, so is their distributed concatenation, we now define the required one-to-one function, FL (FlattenLines):

<!-- PDF p.61 / printed p.58 -->

```
┌───────────────────────────────
│ FL : DocLineSeq ⤖ seq Char
├───────────────────────────────
│ FL L = ⁀/ L
└───────────────────────────────
```

The sequence of lines corresponding to the empty sequence of characters is the empty sequence of lines:

    **Lemma 3 : 1.2d**

        C = ⟨⟩
      ⊢
        FL⁻¹ C = ⟨⟩

      ■

**Proof**
Similar to Lemma 3:1.2b.
■

#### 1.2.1 The Instantiated Move And Delete Operations

We now instantiate the formal parameter *X* with the sets of actual generic parameters *seq Char*, *DocWordSeq* and *DocLineSeq* to give schemas that specify movement and deletion by a character, word or line:

    Mv_Char    ≙ Mv[seq Char]
    Mv_Word    ≙ Mv[DocWordSeq]
    Mv_Line    ≙ Mv[DocLineseq]

    Del_Char   ≙ Del[seq Char]
    Del_Word   ≙ Del[DocWordSeq]
    Del_Line   ≙ Del[DocLineseq]

    MvBot_Char ≙ MvBot[seq Char]

Expanding the schemas for *Mv_Line* and *Del_Word*, for example, we have:

```
┌─ Mv_Line ─────────────────────────────────
│ Left, Right, Left′, Right′ : DocLineSeq
├───────────────────────────────────────────
│ Left ⁀ Right = Left′ ⁀ Right′
│ Left ≠ ⟨⟩
│ Left′ = front Left
└───────────────────────────────────────────
```

<!-- PDF p.62 / printed p.59 -->

```
┌─ Del_Word ────────────────────────────────
│ Left, Right, Left′, Right′ : DocWordSeq
├───────────────────────────────────────────
│ Left ≠ ⟨⟩
│ Left′ = front Left
│ Right′ = Right
└───────────────────────────────────────────
```

#### 1.2.2 Some Results Concerning Characters, Words And Lines

Since move and delete operations involve the front and tail of sequences, we give the following results concerning those operators applied to the word and line view of the *Doc1* model in terms of the character view.

We first consider the tail of a word sequence. Suppose *C* is a non-empty sequence of characters, *W* the corresponding word sequence, *W′* the tail of *W* and *C′* the character sequence corresponding to *W′*. We consider three cases: the first element of *W* being a newline word, a whitespace word and a non-whitespace word.

For the first case, since the newline itself forms a word, *C′* is obtained from *C* by the removal of the newline, for example:

    C = ⟨nl, t, h, e, sp, c, a, t⟩
    W = FW⁻¹ C = ⟨⟨nl⟩, ⟨t, h, e⟩, ⟨sp⟩, ⟨c, a, t,⟩⟩ [?112]
    W′ = tail W = ⟨⟨t, h, e⟩, ⟨sp⟩, ⟨c, a, t,⟩⟩
    C′ = FW W′ = ⟨t, h, e, sp, c, a, t⟩

For the second case, *C′* will postfix *C* starting at the first non-space character, for example:

    C = ⟨sp, sp, t, h, e, sp, c, a, t⟩
    W = FW⁻¹ C = ⟨⟨sp, sp⟩, ⟨t, h, e⟩, ⟨sp⟩, ⟨c, a, t,⟩⟩
    W′ = tail W = ⟨⟨t, h, e⟩, ⟨sp⟩, ⟨c, a, t,⟩⟩
    C′ = FW W′ = ⟨t, h, e, sp, c, a, t⟩

or *C′* will be empty if no such non-space character exists, for example:

    C = ⟨sp, sp, sp, sp⟩
    W = FW⁻¹ C = ⟨⟨sp, sp, sp, sp⟩⟩
    W′ = tail W = ⟨⟩
    C′ = FW W′ = ⟨⟩

Similarly for the last case, *C′* will postfix *C* starting at the first non-non-whitespace character (space or newline), or be empty if no such character exists.

We therefore have:

<!-- PDF p.63 / printed p.60 -->

    **Lemma 3 : 1.2.2a**

        C ∈ seq₁ Char
        C′ ∈ seq Char | C′ = FW(tail FW⁻¹ C)
      ⊢
        C′ postfix C ∧
            head C = nl
            C′ = tail C
        ∨
            C ⦇ 1 .. #C − #C′ ⦈ [?113] ⊆ {sp}
            C′ ≠ ⟨⟩ ⇒ C(#C − #C′ + 1) ≠ sp
        ∨
            C ⦇ 1 .. #C − #C′ ⦈ ∩ {sp, nl} = ∅
            C′ ≠ ⟨⟩ ⇒ C(#C − #C′ + 1) ∈ {sp, nl}

      ■

**Proof**

    1.  ∀ S : seq₁ Char • ⁀/(tail S) postfix ⁀/ S        propt. ⁀/
    2.  ⁀/(tail FW⁻¹ C) postfix ⁀/(FW⁻¹ C)               1.
    3.  FW(tail FW⁻¹ C) postfix FW(FW⁻¹ C)               2., def.FW
    4.  C′ postfix C                                     3., def.FW

The three disjunctions follow from the definition of *DocWordSeq*: the first followssince a newline word has length one, and the remaining two since, by definition, no two whitespace words and no two non-whitespace words can be adjacent in a *DocWordSeq*
■

In a similar way, we now consider the front of a line sequence. Suppose *C* is a non-empty sequence of characters, *L* the corresponding line sequence, *L′* the front of *L* and *C′* the character sequence corresponding to *L′*. We consider two cases: the last element of *L* being a newline word, and being a non-newline word.

For the first case, *C′* is obtained from *C* by the removal of the newline character, for example:

    C = ⟨c, a, n, a, r, y, sp, a, t, e, nl⟩
    L = FL⁻¹ C = ⟨⟨c, a, n, a, r, y, sp, a, t, e⟩, ⟨nl⟩⟩
    L′ = front L = ⟨⟨c, a, n, a, r, y, sp, a, t, e⟩⟩
    C′ = FL L′ = ⟨c, a, n, a, r, y, sp, a, t, e⟩

and for the second case, *C′* will prefix *C* up to the first newline character, for example:

<!-- PDF p.64 / printed p.61 -->

    C = ⟨ c, a, n, a, r, y, sp, a, t, e, nl, t, h, e ⟩
    L = FL⁻¹ C = ⟨⟨ c, a, n, a, r, y, sp, a, t, e ⟩, ⟨ nl ⟩, ⟨ t, h, e ⟩⟩
    L′ = front L = ⟨⟨ c, a, n, a, r, y, sp, a, t, e ⟩, ⟨ nl ⟩⟩
    C′ = FL L′ = ⟨ c, a, n, a, r, y, sp, a, t, e, nl ⟩

or *C′* will be empty if no such non-space character exists, for example:

    C = ⟨ c, a, n, a, r, y ⟩
    L = FL⁻¹ C = ⟨⟨ c, a, n, a, r, y ⟩⟩
    L′ = front L = ⟨⟩
    C′ = FL L′ = ⟨⟩

**Lemma 3 : 1.2.2b**

      C ∈ seq₁ Char
      C′ ∈ seq Char | C′ = FL(front FL⁻¹ C)
    ⊢
      C′ prefix C ∧
          last C = nl
          C′ = front C
      ∨
          nl ∉ C ⦇ # C′ + 1 .. # C ⦈
          C′ ≠ ⟨⟩ ⇒ C(# C′) ≠ nl
    ■

**Proof**

    1.  ∀ S : seq₁ Char • ⁀/(front S) prefix ⁀/ S          propt. ⁀/
    2.  ⁀/(tail FW⁻¹ C) postfix ⁀/(FW⁻¹ C)                 1.
    3.  FW(tail FW⁻¹ C) postfix FW(FW⁻¹ C)                 2., def.FW
    4.  C′ postfix C                                       3., def.FW

The two disjunctions follow from the definition of *DocLineSeq*: the first follows since a newline word has length one, and second since, by definition, no two non-newline words can be adjacent in a *DocLineSeq*

■

### 1.3 The Doc1 State

We now wish to define a document state which incorporates the character, word and line views of the document, cementing the equivalence of the three views through a state invariant using the FW and FL functions.

<!-- PDF p.65 / printed p.62 -->

This enables us to specify each operation on the appropriate view of the document, and since we specify on a "Δ" state which incorporates the state invariant, the other two equivalent views will be "automatically" updated.

We specify the three representations that are provided by *Pair_Char*, *Pair_Word* and *Pair_Line* which are schemas instantiating the generic set *X* of the *Pair* schema of Section 2.1 with the sets *seq Char*, *DocWordSeq* and *DocLineSeq*:

    Pair_Char    ≙   Pair[seq Char]
    Pair_Word    ≙   Pair[DocWordSeq]
    Pair_Line    ≙   Pair[DocLineseq] [?201]

and for the sake of brevity, we define:

    Left_Char    ≙   Pair_Char . Left
    Right_Char   ≙   Pair_Char . Right
    Left_Word    ≙   Pair_Word . Left
    Right_Word   ≙   Pair_Word . Right
    Left_Line    ≙   Pair_Line . Left
    Right_Line   ≙   Pair_Line . Right

and incorporate an invariant relating the three views to give:

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

For non content-changing operations, we define:

    Ξ_Cont Doc1 ≙ Ξ_Cont Pair[Char] ∧ ΔDoc1

Initially the left and right character sequences are empty:

    Initialize_Doc1 ≙ [ ΔDoc1 | Left_Char′ = Right_Char′ = ⟨⟩ ]

and we discharge PO 0, since Lemmas 3:1.2b and 3:1.2d give:

<!-- PDF p.66 / printed p.63 -->

**Lemma 3 : 1.3a**

      Initialize_Doc1
    ⊢
      Left_Char′ = Right_Char′ = ⟨⟩
      Left_Word′ = Right_Word′ = ⟨⟩ = FW⁻¹ (Left_Char′) = FW⁻¹ (Right_Char′)
      Left_Line′ = Right_Line′ = ⟨⟩ = FL⁻¹ (Left_Char′) = FL⁻¹ (Right_Char′)
    ■

We now promote the move and delete operations to the *Doc1* state:

    MvChar      ≙   Mv_Char      ∧   ΔDoc1
    MvWord      ≙   Mv_Word      ∧   ΔDoc1
    MvLine      ≙   Mv_Line      ∧   ΔDoc1

    DelChar     ≙   Del_Char     ∧   ΔDoc1
    DelWord     ≙   Del_Word     ∧   ΔDoc1
    DelLine     ≙   Del_Line     ∧   ΔDoc1

    McBottom [?202]  ≙   MvBot_Char   ∧   ΔDoc1

We must discharge PO 1 for each of these operations: for example, for *DelWord* we have:

      Left_Char = FW Left_Word = FL Left_Line
      Right_Char = FW Right_Word = FL Right_Line
      Left_Word ≠ ⟨⟩
    ⊢
      ∃ Left_Char′, Right_Char′, Left_Word′, Right_Word′, Left_Line′, Right_Line′ •
                  Left_Word′ = front (Left_Word)
                  Right_Word′ = Right_Word
                  Left_Char′ = FW Left_Word′ = FL Left_Line′
                  Right_Char′ = FW Right_Word′ = FL Right_Line′

which simplifies to:

      Left_Char = FW Left_Word = FL Left_Line
      Left_Word ≠ ⟨⟩
    ⊢
      ∃ Left_Char′, Left_Line′ •
                  Left_Char′ = FW front (Left_Word)
                  Left_Line′ = FL⁻¹ (Left_Char′)

Thus this and each of the other PO 1 proof obligations may be discharged since FW and FL are bijective.

<!-- PDF p.67 / printed p.64 -->

#### 1.3.1 The Insert Operation

We specify the operation to insert a character on the *Doc1* state, distinguishing the insertion of the tab character from a non-tab character. We introduce:

    tab : Char

and first specify the operation to insert a non-tab character, *x*, at the end of the left character sequence, the right sequence remaining unchanged:

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

The tab character itself is not inserted into the document, but instead sufficient space characters are inserted at the end of the left character sequence to ensure that the current position is moved to the next (implementation- dependent) tabstop, with the right character sequence remaining unchanged:

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

to give, as the insert operation:

    InsChar ≙ InsNonTab ∨ InsTab

PO 1 may be discharged in the same way as in Section 1.3.

### 1.4 Introducing Direction

So far, the operations that we have defined have been "left" operations, and we now consider their "right" counterparts. We are able to derive the latter operations from the former by using of the schema

<!-- PDF p.68 / printed p.65 -->

```
┌─ Mirror ────────────────────────────
│ ΔDoc1
├─────────────────────────────────────
│ Left_Char′ = rev  Right_Char
│ Right_Char′ = rev  Left_Char
└─────────────────────────────────────
```

and since  rev ; rev  is the identity on sequences, we have:

    Mirror ; Mirror  ≙  ΞDoc1

If we apply *Mirror* followed by the left operation, followed by *Mirror* again we have achieved the corresponding right operation. To aid readability, we use the following syntactic shorthand:

    Right OP   ≙   Mirror ; OP ; Mirror
    Left OP    ≙   OP

and apply to the move and delete operations defined in Section 2.2 to obtain:

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

Partly expanding the schema *LeftMvLine*, for example, we obtain the operation initially requiring that the left line sequence does not comprise an empty line, with the left line sequence becoming equal to its front, and the right line sequence changing in such a way that the concatenation of the left and right line sequences does not change:

<!-- PDF p.69 / printed p.66 -->

```
┌─ LeftMvLine ────────────────────────────────
│ ΔDoc1
├─────────────────────────────────────────────
│ Left_Line ≠ ⟨⟩
│ Left_Line′ = front Left_Line
│ Left_Line′ ⁀ Right_Line′ = Left_Line ⁀ Right_Line
└─────────────────────────────────────────────
```

and similarly expanding the schema for *RightDelWord* we obtain an operation with the pre-condition that the right word sequence is non-empty, with the right word sequence becoming equal to its tail, and the left word sequence not changing:

```
┌─ RightDelWord ──────────────────────
│ ΔDoc1
├─────────────────────────────────────
│ Right_Word ≠ ⟨⟩
│ Right_Word′ = tail Right_Word
│ Left_Word′ = Left_Word
└─────────────────────────────────────
```

PO 1 for the "left" operations are discharged in Section 1.3; those for the "right" operations may be discharged in exactly the same way.

### 1.5 Error Messages

The move and delete commands of Section 1.4 have pre-conditions that either the right or left sequences must be non-empty. In order to make the operations total, we extend the operation domains by the inclusion of the report of an appropriate error message if an attempt is made to execute the command outside its domain: such error messages are assumed to belong to the set *Report*. We define:

    [Report]

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

<!-- PDF p.70 / printed p.67 -->

```
┌─ ErrorBotOfDoc ─────────────────────
│ Doc1Unchanged
├─────────────────────────────────────
│ Right_Char = ⟨⟩
│ rep! = "At bottom of document"
└─────────────────────────────────────
```

Although we are not concerned with operational detail in this abstract specification, we must recognize that the editor will have finite capacity, and that the insert operation may not always be successful. We define:

```
┌─ ErrorFull ─────────────────────────
│ Doc1Unchanged
├─────────────────────────────────────
│ rep! = "Editor full"
└─────────────────────────────────────
```

### 1.6 The Total Operations On The Doc1 State

We now have:

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

Partly expanding the schema for *LeftMoveLine_Doc1*, for example, we obtain an operation which, if the left line sequence does not comprise an empty line performs *LeftMvLine*

<!-- PDF p.71 / printed p.68 -->

and issues an "OK" report, and if the left line sequence is an empty line does nothing except issue the "At top of document" report:

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

and similarly expanding the schema for *RightDeleteWord_Doc1* defines an operation which, if the right word sequence is non-empty performs *RightDelWord* and issues a report of "OK", and if the right word sequence is empty does nothing except issue the report "At bottom of document":

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

Lemma 3:1.3a implies that the initialization operation will always succeed, and so we do not include a report message with that operation.

Since a *Success* schema does not alter the state, if we have discharged our invariant preservation obligation for some operation *OP*, then we have also discharged our obligation for the conjunction of that operation with a *Success* schema. An *Error* leaves the state unchanged, and so there is no associated proof obligation. Each of the above operations comprises a disjunction of two other operations, both of which preserve the state invariant, and thus each operation itself must preserve the state invariant.

<!-- PDF p.72 / printed p.69 -->

## 2 Unbounded Display Of The Document

### 2.1 An Unbounded Display Model

In this section we specify a model which displays a document in full, and then (Section 8 [?204]) use this unbounded model to develop a bounded display model incorporating a single movable window on to the document. We define the unbounded display in a manner orthogonal to that of *Doc1*.

An unbounded display may be uniquely characterised in many different ways. We choose a line model because this enables the display to be very naturally viewed as a sequence of lines placed one above the other and aligned at the left, the first at the top, the next immediately below, and so on.

For example, we want the four line display:

    the canary
    ate

    the

to correspond to the sequence:

    ⟨⟨ t, h, e, sp, c, a, n, a, r, y ⟩, ⟨ a, t, e ⟩, ⟨⟩, ⟨ t, h, e ⟩⟩

Note that each display line may be empty, but cannot contain a newline (unlike the line view incorporated in the *Doc1* model). The empty display will correspond to the unit sequence containing the empty display line.

We therefore define a display line as a sequence of characters not containing a newline:

    DispLine  ==  seq (Char - {nl})

and we characterize the display of an unbounded document by *UDLines*, a non-empty sequence of *DispLine*.

We model the screen cursor by a pair of natural numbers, with the top left hand position corresponding to (*1*, *1*), and we require the cursor to be inside the display of the document. If *UDCurX* and *UDCurY* represent the horizontal and vertical displacement from the top left hand corner of the screen, we therefore require that the latter cannot exceed the length of *UDLines*, and the former cannot be one more than the length of the *UDCurY*ᵗʰ line of *UDLines* (*UDCurX* attaining its greatest value when it appears immediately after the last character of that line).

For ease of reference, we also include *UDCurLine*, the *UDCurY*ᵗʰ line of *UDLines* (the line in which the cursor resides) in the unbounded display model:

<!-- PDF p.73 / printed p.70 -->

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

We note the following result when the display contains a single empty line:

**Lemma 3 : 2.1a**

      UD | UDLines = ⟨⟨⟩⟩
    ⊢
      UDCurY = 1
      UDCurLine = ⟨⟩
      UDCurX = 1
    ■

**Proof**

    UDCurY ∈ ℕ₁ ∧ UDCurY ≤ # ⟨⟨⟩⟩  ⇒  UDCurY = 1
    UDCurLine = ⟨⟨⟩⟩ 1 = ⟨⟩
    UDCurX ∈ ℕ₁ ∧ UDCurX ≤ # ⟨⟩ + 1  ⇒  UDCurX = 1

■

### 2.2 The Doc2 State

The *Doc1* state is now extended to *Doc2* by incorporating its unbounded display: We relate the two through their respective character sequences, such that the flattened display line sequence is the concatenation of the left and right character views of *Doc1*.

To obtain the character sequence corresponding to a sequence of display lines, we define a function FDL (FlattenDisplayLines) that inserts a newline character between adjacent display lines before flattening the sequence. Clearly, we have a function which is bijective:

<!-- PDF p.74 / printed p.71 -->

```
┌───────────────────────────────────────────────
│ FDL : seq₁ DispLine ⤖ seq Char
├───────────────────────────────────────────────
│ ∀ L1, L2 : seq₁ DispLine ; l : DispLine •
│     FDL (⟨ l ⟩) = l
│     FDL (L1 ⁀ L2) = (FDL L1) ⁀ ⟨ nl ⟩ ⁀ (FDL L2)
└───────────────────────────────────────────────
```

We establish three results relating to this definition.

Firstly, an empty sequence of characters corresponds to the display containing a single empty line:

**Lemma 3 : 2.2a**

      C = ⟨⟩
      L : seq₁ DispLine | L = FDL⁻¹ C
    ⊢
      L = ⟨⟨⟩⟩
    ■

**Proof**

    FDL⁻¹ ⟨⟩ = ⟨⟨⟩⟩

■

Secondly, if *L* is a non-empty sequence of display lines, the number of newlines in the corresponding character sequence is one less than the length of *L*:

**Lemma 3 : 2.2b**

      L : seq₁ DispLine
    ⊢
      #((FDL L) ▷ {nl}) = # L - 1
    ■

**Proof**

<!-- PDF p.75 / printed p.72 -->

We use induction on the length of the sequence *L*

    Base :  L = ⟨ l ⟩
      1.  # L = 1 [?205]                                         Base
      2.  FDL L = l                                              Base, defn. FDL
      3.  #((FDL L) ▷ {nl}) = 0                                  2., l ∈ DispLine
      4.  #((FDL L) ▷ {nl}) = # L - 1                            3., 1.
    Step :  L = L1 ⁀ ⟨ l ⟩  where L1 ≠ ⟨⟩
      5.  #((FDL L1) ▷ {nl}) = # L1 - 1                          Step
      6.  # L = # L1 + 1                                         Step
      7.  FDL L = (FDL L1) ⁀ ⟨ nl ⟩ ⁀ l                          Step, defn. FDL
      8.  #((FDL L) ▷ {nl}) = #((FDL L1) ▷ {nl}) + 1             7., l ∈ DispLine
      9.  #((FDL L) ▷ {nl}) = # L - 1                            5., 6., 8.

■

Finally, the character sequence corresponding to a sequence of display lines of length at least two and whose last element is the empty line has a newline as its last element:

**Lemma 3 : 2.2c**

      L : seq₁ DispLine  |  # L ≥ 2 ∧ last L = ⟨⟩
      C : seq Char       |  C = FDL L
    ⊢
      last C = nl
    ■

**Proof**

    1.  Let L = L1 ⁀ ⟨⟨⟩⟩
    2.  L1 ≠ ⟨⟩                                                  1., # L ≥ 2
    3.  C = FDL(L1 ⁀ ⟨⟨⟩⟩)                                       1.
    4.  C = (FDL L1) ⁀ ⟨ nl ⟩ ⁀ ⟨⟩                               2., 3., def. FDL
    5.  last C = nl                                              4., defs. ⁀ , ⟨⟩

■

We now define the *Doc2* state as the conjunction of the *Doc1* and *UD* models, requiring that the two character representations are the same. Then *UDCurLine* comprises the last of the display line sequence corresponding to *Left_Char* concatenated with the *first* of the display line sequence corresponding to *Right_Char*; *UDCurY* equals the length of the display line sequence corresponding to *Left_Char*, and *UDCurX* equals the length of the last element of that sequence:

<!-- PDF p.76 / printed p.73 -->

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

We note that the invariant of *Doc2* is consistent with that of *Doc1*, since the word and line views of the latter are not used in the specification of the former. We show that there is no conflict between the *Doc2* and *UD* invariants by assuming that the two character representations are the same (the first predicate of *Doc2*) and showing that the definitions of *UDCurLine*, *UDCurX* and *UDCurY* meet the *UD* invariant.

In order to show the first of these, we have, denoting FDL⁻¹ *Left_Char* by *L*, FDL⁻¹ *Right_Char* by *R*, *UDLines* by *U*, and *UDCurY* by n:

    1.  Let L = L0 [?207] ⁀ ⟨ l ⟩ and ⟨ r ⟩ ⁀ R0 = R              defn. FDL
    2.  # L0 = n - 1                                              1., # L = n
    3.  FDL L ⁀ FDL R =
            FDL L0 ⁀ ⟨ nl ⟩ ⁀ ⟨ l ⟩ ⁀
                    ⟨ r ⟩ ⁀ ⟨ nl ⟩ ⁀ FDL R0                       2., defn. FDL
    4.  FDL L ⁀ FDL R =
            FDL L0 ⁀ ⟨ nl ⟩ ⁀ ⟨ l, r ⟩ ⁀ ⟨ nl ⟩ ⁀ FDL R0          3., defn. ⁀
    5.  FDL L ⁀ FDL R = FDL (L0 ⁀ ⟨ l, r ⟩ ⁀ R0)                  4., defn. FDL
    6.  FDL⁻¹ (FDL L ⁀ FDL R) = L0 ⁀ ⟨ l, r ⟩ ⁀ R0                5., defn. FDL
    7.  U = L0 ⁀ ⟨ l, r ⟩ ⁀ R0                                    6., Doc2, defn. FDL
    8.  U n = ⟨ l, r ⟩                                            2., 7., defn. ⁀

The minimum value for *UDCurY* is given when *Left_Char* is minimal in the document - when *Left_Char* is empty:

    UDCurY  =  # FDL⁻¹ ⟨⟩  =  # ⟨⟨⟩⟩  =  1

and the maximum value is given when *Left_Char* is maximal - when *Right_Char* is empty:

    UDCurY  =  # FDL⁻¹ (Left_Char ⁀ Right_Char)  =  # UDLines

Finally, the minimum value for *UDCurX* will be given when the last of FDL⁻¹ *Left_Char* is minimal in *UDCurLine* - when it is empty:

    UDCurX  =  #( ⟨⟩ ) + 1  =  1

and its maximum value will occur when the last of FDL⁻¹ *Right_Char* is maximal - when the first of FDL⁻¹ *Right_Char* is empty:

<!-- PDF p.77 / printed p.74 -->

    UDCurX  =  #(last (FDL⁻¹ Left_Char) ⁀ first (FDL⁻¹ Right_Char)) + 1
            =  # UDCurLine + 1

Hence there is no conflict between the invariants of *Doc2* and *UD*.

Initially:

    Initialize_Doc2  ≙  Initialize_Doc1 ∧ ΔDoc2

and as a direct result of the definition of FDL and Lemmas 3:1.3a and 3:2.1b [?208], we have:

**Lemma 3 : 2.2d**

      Initialize_Doc2
    ⊢
      UDLines′ = ⟨⟨⟩⟩
      UDCurLine′ = ⟨⟩
      (UDCurX′, UDCurY′) = (1, 1)
    ■

### 2.3 Promotion Of The Doc1 Operations To The Doc2 State

Each of the operations of the *Doc1* state is promoted to the *Doc2* state in the same way. In order to save unnecessary repetition in this and subsequent promotion processes, we use the following informal method: we define the set of names:

    MoveOps     ≙   { RightMoveChar, LeftMoveChar,
                      RightMoveWord, LeftMoveWord,
                      RightMoveLine, LeftMoveLine,
                      MoveTopDoc, MoveBotDoc          }

    DeleteOps   ≙   { RightDeleteChar, LeftDeleteChar,
                      RightDeleteWord, LeftDeleteWord,
                      RightDeleteLine, LeftDeleteLine    }

    InsertOp    ≙   { InsertChar }

to give:

    EditOps1  ≙  MoveOps ∪ DeleteOps ∪ InsertOp

Then for each operation *OP* defined in Section 1.6 on the *Doc1* state and in the set *EditOps1*, we have:

    ∀ OP : EditOps1 • OP_Doc2 ≙ OP_Doc1 ∧ ΔDoc2

<!-- PDF p.78 / printed p.75 -->

The *Doc2* invariant ensures that each of the unbounded display components is uniquely defined in terms of the *Doc1* components, and satisfy the *UD* invariant, which means that the introduction of the *UD* variables does not result in additional proof obligations since they are redundant - they may be calculated from the *Doc1* and we have shown that they do not violate the state invariant.

## 3 Invariants On The Unbounded Display Model

### 3.1 The Doc3 State

It is impossible to identify trailing whitespace (space characters at the end of a line) on a terminal screen (except when the cursor is at the end of a line) and so we require that each document line (except the cursor line) has no trailing whitespace. We define a display line to be visible if and only if it is empty or its last character is not a space character:

```
┌───────────────────────────────────────
│ visible _ : DispLine → 𝔹
├───────────────────────────────────────
│ visible l ⇔ (l ≠ ⟨⟩ ⇒ last l ≠ sp)
└───────────────────────────────────────
```

For the same reason, we require that the document has no trailing null lines, and we specify that a non-empty sequence of display lines is a visibleseq if and only if it is empty or its last element is non-null:

```
┌───────────────────────────────────────────────
│ visibleseq _ : seq DispLine → 𝔹
├───────────────────────────────────────────────
│ visibleseq L ⇔ (L ≠ ⟨⟨⟩⟩ ⇒ last L ≠ ⟨⟩)
└───────────────────────────────────────────────
```

Expressing the above definition in terms of the corresponding character sequence gives:

**Lemma 3 : 3.1a**

      L : seq₁ DispLine
      C : seq Char | FDL L = C
    ⊢
      visibleseq L ⇔ (C ≠ ⟨⟩ ⇒ last C ≠ nl)
    ■

**Proof**

<!-- PDF p.79 / printed p.76 -->

Follows from Lemmas 3:2.2a and 3:2.2c.

■

In the *Doc3* model we therefore require that every line except the cursor line is visible, that the cursor line itself is visible following the cursor position, and that the sequence of lines below the cursor line is a visibleseq. We define:

```
┌─ Doc3 ──────────────────────────────────────────────────
│ Doc2
├─────────────────────────────────────────────────────────
│ ∀ i : 1 .. # UDLines - {UDCurY} • visible (UDLines i)
│ visible (UDCurLine after UDCurX - 1)
│ visibleseq (UDLines after UDCurY)
└─────────────────────────────────────────────────────────
```

where:

```
┌───────────────────────────────────────
│ _ after _ : seq X × ℕ → seq X
├───────────────────────────────────────
│ S after N = sucᴺ ; (1 .. N ⩤ [?209] S)
└───────────────────────────────────────
```

Since the *Doc3* state introduces no new components, the initial state of *Doc3* is exactly that of *Doc2*:

    Initialize_Doc3  ≙  Initialize_Doc2

We note that, after initialization, and using Lemma 3:2.2d, the first predicate of *Doc3* is trivially true (since # *UDLines* = *UDCurY* = *1*); the second predicate follows by definition of "after", noting that *UDCurLine* is initially empty and that the empty sequence is visible; the final predicate holds again by definition of "after" noting that, initially, *UDLines* after *UDCurY* is empty, and thus comprises a visibleseq. Thus we discharge PO 0 [?210].

### 3.2 Two Relations That Tidy The Display

We now consider the preservation of the two invariant requirements of the *Doc3* model.

We first consider the whitespace invariant, and define a relation between two display lines in which the first is visible and is the longest such that it is a prefix the second:

```
┌───────────────────────────────────────────────────
│ _ visible_prefix _ : DispLine × DispLine → 𝔹
├───────────────────────────────────────────────────
│ L′ visible_prefix L ⇔ visible L′ ∧ rng (L - L′) ⊆ {sp}
└───────────────────────────────────────────────────
```

<!-- PDF p.80 / printed p.77 -->

Note that, since *L* and *L′* are sequences:

    rng (L − L′)  ⊆  {sp}    ⇔    L′ prefix L
                                  L ⦇ # L′ + 1 .. # L ⦈  ⊆  {sp}

and that visible prefix is reflexive for all visible lines:

    **Lemma 3 : 3.2a**

        visible L
      ⊢
        L visible_prefix L [?301]
      ■

**Proof**

    1.  L prefix L                                   defn. prefix
    2.  L ⦇ # L + 1 .. # L ⦈  =  ∅  ⊆  {sp}          defns. …, ⊆ [?302]
    3.  L visible prefix L                           1..2.

■

We now consider the preservation of the null lines invariant of the *Doc3* model by defining an analogous relation on sequences of display lines, in which the first sequence is a visibleseq and is the longest such prefix of the second:

```
┌───────────────────────────────────────────────────────────
│ _ visibleseq_prefix _ : seq₁ DispLine × seq₁ DispLine → B
├───────────────────────────────────────────────────────────
│ L′ visibleseq_prefix L  ⇔  visibleseq L′ ∧ rng (L − L′) ⊆ { ⟨⟩ }
└───────────────────────────────────────────────────────────
```

Relating this result to the corresponding character sequences gives:

    **Lemma 3 : 3.2b**

        L, L′ : seq₁ DispLine
        C, C′ : seq Char  |  C = FDL L ∧ C′ = FDL L′
      ⊢
        L′ visibleseq prefix L   ⇔   C′ prefix C
                                     C′ ≠ ⟨⟩  ⇒  last C′ ≠ nl
                                     C ⦇ # C′ + 1 .. # C ⦈  ⊆  {nl}
      ■

**Proof**
The result follows directly from the definition of FDL, and the results of Lemmas 3:2.2c [?303]

<!-- PDF p.81 / printed p.78 -->

and 3:3.1a.
■

We note that visibleseq_prefix is also reflexive for all visibleseq:

    **Lemma 3 : 3.2c**

        visibleseq L
      ⊢
        L visibleseq_prefix L
      ■

**Proof**
    Similar to Lemma 3:3.2a.

■

### 3.3 Promotion of Doc2 Operations to the Doc3 State

When showing that an operation preserves the invariant of the state on which it is defined, we assume that the state invariant is true before the operation is invoked (PO 1). Thus the only display line that may contain violating trailing whitespace after an operation has been performed is the previous cursor line (which may, of course, not have changed).

We therefore define an operation that removes violating trailing whitespace from the previous cursor line, taking the previous value of the length of *Left_Char* as the identifying input parameter, (since we will post-sequentially compose with this operation) leaving all other *Doc2* components unchanged.

If the cursor line has not changed, there must be no trailing whitespace to the right of the new cursor position, and so the cursor line after *UDCurY − 1* [?304] must become a visible prefix of itself, with the cursor line to the left of that position remaining unchanged, and if the cursor line has changed, the whole of the previous cursor line must become a visible prefix of itself:

<!-- PDF p.82 / printed p.79 -->

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

The first two predicates ensure that all lines except the previous cursor line and the cursor position do not change. the first disjunction treats the case when the cursor line does not change, and the second deals with a change of cursor line. In both cases, since all lines except the previous cursor line cannot have had trailing whitespace, and since visible prefix is reflexive (Lemma 3:3.2c), the *Doc3* trailing whitespace invariant is met.

We now define an operation that removes trailing null lines from that part of the document following the new cursor line (once again leaving the cursor position unchanged):

```
┌─ RemTrailNL ──────────────────
│ ΔUD
├───────────────────────────────
│ UDCurX′, UDCurY′ = UDCurX, UDCurY
│ UDLines′ for UDCurY = UDLines for UDCurY
│ (UDLines′ after UDCurY) visibleseq prefix (UDLines after UDCurY)
└───────────────────────────────
```

The first two predicates ensure that the cursor position and all lines above and including the new cursor line do not change. the last predicate ensures no trailing null lines after the new cursor line, which meets the *Doc3* null lines requirement.

We promote the operations of Section 2.3, defined on the *Doc2* state, to the *Doc3* state by sequential composition with the first of the above operations (to remove trailing whitespace), followed by sequential composition with the second (to remove trailing null lines). We define an operation to identify the previous cursor position:

    FlagPrevCursor ≙ [ Left_Char : seq Char ; prevCP! : ℕ | prevCP! = # Left_Char ]

For each operation *OP* identified with the set *EditOps1* (Section 2.3), we have:

    ∀ OP : EditOps1 •
        OP_Doc3 ≙ FlagPrevCursor ; OP_Doc2 ; RemTrailWS ; RemTrailNL

<!-- PDF p.83 / printed p.80 -->

We note that each *Rem* operation is total, and therefore may freely post-compose with both.

## 4 Cursor Movement

### 4.1 The QP State

The eight move operations defined on the *Doc3* state (left and right, by character. word and line. and to the top and bottom of the document) facilitate cursor movement around the document. but do not enable positions "outside" its unbounded display to be reached.

The unbounded display of the document defines a "quarter plane" - a plane bounded by the top and left hand edges of the document. but unbounded to the right and below - and we now consider operations to move the cursor around that quarter plane.

We specify a state comprising a coordinate position within the quarter plane, orthogonal to the model developed so far:

    QP ≙ [ QPCurX, QPCurY : ℕ₁ ]

We wish to define cursor movement up, down, left and right, and first define horizontal and vertical moves (when, respectively, *QPCurY* and *QPCurX* do not change); we define a vertical move with the parameter *y* so that we may subsequently use the definition to specify vertical movement by character or page:

    QPHorizMove  ≙  [ ΔQP | QPCurY′ = QPCurY ]
    QPVertMove   ≙  [ ΔQP ; y : ℕ₁ | QPCurX′ = QPCurX ]

where the parameter *y* represents the number of characters to be moved vertically (since we wish to specify vertical movement by a page as well as a character). We define:

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

<!-- PDF p.84 / printed p.81 -->

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

noting that the pre-conditions are necessary for leftward and upward movement to ensure the preservation of the *QP* invariant.

To totalise the operations (by which we mean transform each such that it becomes total) we define the following error messages, the first when upward movement would cause *QPCurY* to become non-positive, and the second when the cursor is at the top left hand corner of the plane when any leftward move would similarly violate the invariant:

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

The remaining case to consider is when the cursor is at the left edge of the document but not in the top line. In this case, rather than the left move operation failing, and an appropriate error message being issued (which, we feel, would be frustrating for the user), we decrease *QPCurY* by one without specifying the value of *QPCurX*. This non-determinism enables the operation to mimic the left *UD* cursor move (which will thus be to the end of the previous line) when conjoined with the *Doc3* state (which, we feel, would be what the user would actually expect of the operation). We define:

<!-- PDF p.85 / printed p.82 -->

```
┌─ QPCurToPrevLine ─────────────
│ ΔQP
├───────────────────────────────
│ QPCurX = 1
│ QPCurY > 1
│ QPCurY′ = QPCurY − 1
└───────────────────────────────
```

We now have the total operations:

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

each of which clearly preserves the state invariant, and so we discharge PO 1.

We now consider cursor movement vertically by a page: it is desirable that the page height should be less than than that of the terminal screen (*WindowHeight*, introduced formally in Section 8), thereby ensuring that some information contained in the current display is "carried over" to the next display. We introduce:

    PageHeight : ℕ₁   |   PageHeight < WindowHeight

and now define:

    CursorUpChar_QP     ≙  [ QPCursorUp     |  y = 1 ]
    CursorUpPage_QP     ≙  [ QPCursorUp     |  y = PageHeight ]
    CursorDownChar_QP   ≙  [ QPCursorDown   |  y = 1 ]
    CursorDownPage_QP   ≙  [ QPCursorDown   |  y = PageHeight ]
    CursorLeftChar_QP   ≙  QPCursorLeft
    CursorRightChar_QP  ≙  QPCursorRight

### 4.2 The Doc4 State

We combine the *Doc3* and *QP* states into the *Doc4* state by logically conjoining the two, and requiring that the two cursor positions coincide:

<!-- PDF p.86 / printed p.83 -->

    Doc4 ≙ [ Doc3 ∧ QP | UDCurX = QPCurX ∧ UDCurY = QPCurY ]

We specify the initialize operation as:

    Initialize_Doc4  ≙  Initialize_Doc3 [?306] ∧ ΔDoc4

which means that, by definition of *Doc4*, the *QP* cursor must initially be the same as the of the *UD* cursor:

    **Lemma 3 : 4.2a**

        Initialize_Doc4
      ⊢
        QPCurX′ = QPCurY′ = 1
      ■

and we discharge PO 0.

#### 4.2.1 Promotion Of The Doc3 Operations To The Doc4 State

Since the *Doc4* state requires that the *QP* and *UD* cursors agree, we specify a total operation to alter the value of the former to the latter:

```
┌─ EquateQPWithUD ──────────────
│ QP′
│ UDCurX, UDCurY : ℕ
├───────────────────────────────
│ QPCurX′, QPCurY′ = UDCurX, UDCurY
└───────────────────────────────
```

We now define, for each *OP* defined on the *Doc3* state and associated with the set *EditOps1* of Section 2.3:

    ∀ OP : EditOps1  •  OP_Doc4 ≙ (OP_Doc3 ; EquateQPWithUD) ∧ ΔDoc4

post-sequential composition with the *Equate* operation ensuring that each operation preserves the *Doc4* invariant.

#### 4.2.2 Promotion Of The QP Operations To The Doc4 State

In order to preserve the *Doc4* invariant for each of the *QP* cursor movement operations, we must specify an operation to change the values of the *UD* cursor, but in so doing we may violate the invariant of the *Doc3* model. If the cursor position remains inside

<!-- PDF p.87 / printed p.84 -->

the unbounded display, the treatment of the operation is the same as that for a *Doc3* operation, but when the cursor position is moved outside, we must change the contents of the document, ensuring that the whitespace/null lines requirement is met.

As with the *UD* operations, the only line that may contain violating whitespace after the operation is the previous cursor line, and so for each *QP* operation, we post-sequentially compose with *RemTrailWS*. To ensure that there are no trailing null lines after the new cursor line we also post-sequentially compose with *RemTrailNL*. In both cases the cursor position does not change, and the considerations are exactly the same as those discussed in Section 3.3. we now consider the two cases when the cursor is moved outside the unbounded display.

We first consider the case when the *QP* cursor position is to the right of the unbounded display, when the cursor line position will not have changed. We may leave all lines unchanged except for this one (since we are. in effect, performing a left insert operation, which affects only the cursor line), and we choose to "pad" this line with whitespace (since this is what the user would naturally perceive on a terminal screen). Thus the previous cursor line (the *QPCurY*^th line of *UDLines*) will be a visible_prefix of the new (the *QPCurY*^th line of *UDLines′* - i.e. *UDCurLine′*). Note that since visible_prefix is reflexive (Lemma 3:3.2a) this relation will also hold when it is not necessary to change the contents of the line.

We now consider the *QP* cursor being moved below the bottom of the unbounded display. In this case we choose to pad the end of the document with empty lines (again fitting in with the users's [?307] perception of the display). Further, if the cursor is not at the left hand edge of the document, we pad the last of these lines with space characters. In all cases, all display lines in the (possibly empty) range # *UDLines* + 1 to *QPCurY* − 1 will be empty, and the rng of the last line (which in this case will be the current line *UDCurLine′*) will be a subset of {*sp*} (which also holds, of course, when that line is empty).

We define the operation to equate the *UD* with the *QP* cursor:

```
┌─ EquateUDWithQP ──────────────
│ QP
│ UDCurX′, UDCurY′ : ℕ
├───────────────────────────────
│ UDCurX′, UDCurY′ = QPCurX, QPCurY
└───────────────────────────────
```

and the operation to pad the display with whitespace/newlines:

<!-- PDF p.88 / printed p.85 -->

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

The first disjunction treats the case when the cursor does not move below the unbounded display: the second predicate ensures that no lines change except the cursor line. and the third allows whitespace padding of that line. The second disjunction deals with the cursor being moved below the unbounded display: the second predicate extends the number of display lines in the document to agree with *QPCurY*, the third predicate ensures that existing display lines do not change, the next ensures that all lines (except the last) appended to the display are empty, and the final predicate allows for whitespace padding of the last (cursor) line. The operation is total, and thus post-sequential composition with this operation will ensure that all newly added lines satisfy the *Doc3* invariant.

The *CursorLeftChar* operation is identical to *LeftMoveChar_Doc3* (since the *QP* cursor will always remain inside the unbounded display):

    CursorLeftChar_Doc4  ≙  LeftMoveChar_Doc3 ∧ ΔDoc4

We now promote the remaining *QP* cursor operations by defining the set of names:

    QPCursorOps  ≙  { CursorUpChar, CursorDownChar,
                      CursorUpPage, CursorDownPage,
                      CursorLeftChar, CursorRightChar }

and have, recognizing that the editor's capacity may be exceeded:

    ∀ OP : QPCursorOps − {CursorLeftChar} •
        OP_Doc4  ≙  FlagPrevCursor ;
                        SuccOP_QP [?308] ; PadWSNL ;
                        RemTrailWS ; RemTrailNL ∧ ΔDoc4
                    ∨
                        UnSuccOP_QP ∧ ΞDoc4
                    ∨
                        ErrorFull ∧ ΞDoc4

<!-- PDF p.89 / printed p.86 -->

where

    SuccOP_QP    ≙  [ OP_QP | rep! = "OK" ]
    UnSuccOP_QP  ≙  [ OP_QP | rep! ≠ "OK" ]

The last two disjunctions do not change the content of the operation, and for the first, the *Pad* operation ensures that the two cursor positions agree and, together with the two *Rem* operations, ensures that the *Doc3* invariant is maintained (and as explained in Section 3.3 we flag the cursor position before the start of each operation). Thus we discharge PO 1.

## 5 Text Manipulation Operations

### 5.1 The Doc5 State And Marked Text

It is sometimes necessary to identify a portion of text in order that it may either be removed from the document (and, possibly, replaced elsewhere) or lifted (to be copied elsewhere). Such text is referred to as "marked". The operation to set the mark identifies a particular character position in the document and marked text is that lying between the mark and the cursor; hence marked text can lie above or below the cursor.

In the former case we define *MarkSeq* to be the sequence of characters starting at the top of the document and finishing at this marked position. and thus marked text, which we define as *MarkedSeq*, will be the sequence of characters lying between the marked and current positions. In the latter case *MarkSeq* will start at the marked position and end at the bottom of the document and *MarkedSeq* will lie between the current and marked positions. If the mark is not set, we define both *MarkSeq* and *MarkedSeq* to be empty. Thus when the mark is set moving the cursor increases or reduces the amount of text that is marked.

We extend the document state to incorporate marked text:

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

<!-- PDF p.90 / printed p.87 -->

    Doc5 ≙ Doc4 ∧ MarkedText

Initially the document does not contain marked text:

    Initialize_Doc5 ≙ [ Initialize_Doc4 ∧ ΔDoc5 | MarkSeq = MarkedSeq = ⟨⟩ ]

and thus we discharge PO 0 since the first predicate of *MarkedText* is satisfied (since *Initialize_Doc4* ensures that *Left_Char* is empty).

#### The Operation To Set The Mark

We define the operation to set the mark at the current cursor position:

```
┌─ SetMk ───────────────────────
│ MarkedText′
│ Pair_Char
├───────────────────────────────
│ MarkSeq′ = Left_Char
│ MarkedSeq′ = ⟨⟩
└───────────────────────────────
```

which leaves the *Doc4* components of *Doc5* unchanged:

    SetMark_Doc5 ≙ SetMk ∧ ΞDoc4 ∧ ΔDoc5 ∧ Success

#### 5.1.1 Promotion Of The Doc4 Operations To The Doc5 State

It is desirable that cursor-changing operations should preserve the mark (set or unset) but necessary that content-changing operations reset the mark (for instance if part of the document is deleted then *Mark* could point beyond the end of the document). However, since cursor-changing operations may themselves change the content of the document (through the *RemTrailWS* or *RemTrailNL* operations of Section 3.3. or the *PadWSNL* operation of Section 4.2.2) we may not stipulate that the marked position does not change, because if whitespace/newlines are inserted/deleted at a point in the document above the marked position, preserving the mark will, in fact, move it relative to the rest of the document.

Thus our policy for promoting the *Doc4* operations is to require that all content-changing operations result in the mark being reset, but to adopt a non-deterministic approach for cursor-changing operations when the mark is already set, allowing the implementation policy to dictate when the mark should be reset for such operations; in the latter case, when the mark is not set, it will remain so.

We define:

<!-- PDF p.91 / printed p.88 -->

    ResetMark  ≙  [ ΔMarkedText | MarkSeq′ = MarkedSeq′ = ⟨⟩ ]

and use *MoveOps* , *DeleteOps* and *InsertOp* (Section 2.3) and *QPCursorOps* (Section 4.2.2) to define:

    NonCursorOps          ≙  DeleteOps ∪ InsertOp
    CursorOps             ≙  MoveOps ∪ QPCursorOps − NonCursorOps
    CursorOps_NoMarkSet   ≙  CursorOps | MarkSeq′ = MarkedSeq′ = ⟨⟩
    CursorOps_MarkSet     ≙  CursorOps | MarkSeq′ ⁀ MarkedSeq′ ≠ ⟨⟩

to give:

    ∀ OP : NonCursorOps          •  OP_Doc5 ≙ OP_Doc4 [?309] ∧ ResetMark
    ∀ OP : CursorOps_NoMarkSet [?310]  •  OP_Doc5 ≙ OP_Doc4 ∧ ΞMarkedText
    ∀ OP : CursorOps_MarkSet     •  OP_Doc5 ≙ OP_Doc4 [?311] ∧ ΔMarkedText

We note that there are no associated proof obligations associated with this promotion process since *Doc4* and *MarkedText* do not have variables in common, and there is no "cementing" invariant contained in *Doc5*.

### 5.2 The Doc6 State And The Lift, Cut And Paste Operations

Marked text may be placed into a paste buffer by a *Lift* or *Cut* operation (the former leaving the marked text in the document, the latter removing it) and subsequently copied from the buffer to a (new) cursor position by the *Paste* operation. Text in the buffer is not changed until a new *Lift* or *Cut*. and consequently several copies of the buffer may be made at different points in the document.

We enrich the document state as follows:

    PasteBuffer  ≙  [ PBuff : seq Char ]
    Doc6         ≙  Doc5 ∧ PasteBuffer

and initially we set the buffer to be the empty sequence:

    Initialize_Doc6 ≙ [ Initialize_Doc5 ∧ ΔDoc6 | PBuff′ = ⟨⟩ ]

#### The Lift Operation

We first define an operation in which non-empty marked text is copied to the paste buffer:

<!-- PDF p.92 / printed p.89 -->

```
┌─ CopyMTextPBuff ──────────────
│ ΔPasteBuffer
│ Left_Char
│ MarkedText
├───────────────────────────────
│ PBuff′ = MarkedSeq ≠ ⟨⟩
└───────────────────────────────
```

In order to totalise the operation we define the error schema:

```
┌─ ErrorNoTextMarked ───────────
│ ΞDoc6
│ rep! : Report
├───────────────────────────────
│ MarkedSeq = ⟨⟩
│ rep! = "No text marked"
└───────────────────────────────
```

to give:

    Lift_Doc6  ≙    CopyMTextPBuff ∧ ΞDoc5 ∧ ΔDoc6 ∧ Success
                  ∨
                    ErrorNoTextMarked

#### The Cut Operation

This operation is similar to *Lift*, except that the marked text is actually removed from the document, and thus the mark pointer must be reset. We define a total operation which removes marked text from the document and resets the mark:

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

Since the content of the document is changed, we must ensure the preservation of the *Doc3* invariant, and have:

    Cut_Doc6  ≙  FlagPrevCursor ;
                     CopyMTextPBuff ; RemMText ;
                     RemTrailWS ; RemTrailNL ∧ Success
                 ∨
                     ErrorNoTextMarked

<!-- PDF p.93 / printed p.90 -->

#### The Paste Operation

The *Paste* operation concatenates the (non-empty) paste buffer onto the end of *Left_Char*, with *Right_Char* and the paste buffer being left unchanged: the pasted text becomes marked text and thus we set the mark to the original length of *Left_Char*:

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

We acknowledge that the paste operation may cause the capacity of the editor to be exceeded, and again ensure that the *Doc3* invariant is met by post-sequential composition with the *Rem* operations of Section 3.3 to give:

    Paste_Doc6  ≙  FlagPrevCursor ;
                       Pst ; RemTrailWS ; RemTrailNL ∧ ΔDoc6 ∧ Success
                   ∨
                       ΞDoc6 ∧ ErrorFull
                   ∨
                       ErrorPBuffEmpty

#### 5.2.1 Promotion Of The Doc5 Operations To The Doc6 State

We use *CursorOps* and *NonCursorOps* (Section 5.1.1) to define the set of names:

    EditOps2  ≙  CursorOps ∪ NonCursorOps ∪ {Mark}

and stipulate that each operation *OP* in *EditOps2* leaves the paste buffer unchanged:

    ∀ OP : EditOps2  •  OP_Doc6 ≙ OP_Doc5 ∧ ΞPasteBuffer

<!-- PDF p.94 / printed p.91 -->

We again note that there are no proof obligations associated with this promotion process, for the same reasons as those discussed in Section 5.1.1.

## 6 Quote Commands

### 6.1 The Quote Buffer

Unlike other commands, quoted commands are not necessarily single-key commands, and may requre entry of text; we introduce a buffer, *QuoteBuffer*, into which such text may be directly typed and edited, which we specify as the concatenation of a pair of sequences of characters. thereby enabling character movement during editing:

```
┌─ QuoteBuffer ─────────────────
│ Left_Quote, Right_Quote : seq Char
│ QBuff : seq Char
├───────────────────────────────
│ QBuff = Left_Quote ⁀ Right_Quote
└───────────────────────────────
```

#### 6.1.1 Operations To Edit The Quote Buffer

In general, text typed into *QuoteBuffer* will be short , and so we provide only the limited editing features of character movement. insertion and deletion. We define the insert operation, noting that we exclude the insertion of the tab character (since this will result in a varying number of spaces being introduced into the buffer) and the other quote edit operations in an analogous way to those defined on *Doc1*:

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

<!-- PDF p.95 / printed p.92 -->

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

and the error messages:

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

<!-- PDF p.96 / printed p.93 -->

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

to give:

```
InsertChar_Quote        ≙   (QteInsChar ∧ Success) ∨ ErrorQuoteFull ∨
                                    ErrorIllegalCharacter
LeftDeleteChar_Quote    ≙   (QteLeftDelChar ∧ Success) ∨ ErrorTopQuote
RightDeleteChar_Quote   ≙   (QteRightDelChar ∧ Success) ∨ ErrorBotQuote
LeftMoveChar_Quote      ≙   (QteLeftMvChar ∧ Success) ∨ ErrorTopQuote
RightMoveChar_Quote     ≙   (QteRightMvChar ∧ Success) ∨ ErrorBotQuote
```

To discharge PO 2, we note that each operation is a disjunction, only the first of which changes the buffer. Each of the first disjunctions of the first three operations explicitly set *Left_Quote′* and *Right_Quote′*; for the first disjunction of the left move operation, we note that:

```
    Left_Quote, Right_Quote : seq Char  ∧  Left_Quote ≠ ⟨ ⟩
  ⊢
    ∃ Left_Quote′, Right_Quote′ •
              Left_Quote′, Right_Quote′ : seq Char
              Left_Quote′ ⁀ Right_Quote′ = Left_Quote ⁀ Right_Quote
              Left_Quote′ = front Left_Quote
```

simplifies to:

```
    Left_Quote, Right_Quote : seq Char  ∧  Left_Quote ≠ ⟨ ⟩
  ⊢
    ∃ Right_Quote′  •   Right_Quote′ : seq Char
                        Right_Quote′ = (last Left_Quote) ⁀ Right_Quote
```

<!-- PDF p.97 / printed p.94 -->

which is *true*. We may treat the right operation in an analogous way, and since *QBuff* is redundant (it may be calculated from *Left_Quote* and *Right_Quote*), we discharge P0 2.[?401]

### 6.2 Operating System I/O

Although we are not concerned with implementation detail in the abstract specification, we must make some high-level assumptions about the operating system under which the editor will run since several quote operations will require the facility to read from or write to files and, in order to simplify their specification, we assume the existence of three operating system operations, stating our assumptions of these operations in the following "specifications".

The first, *SysGetPtr*, returns a pointer to the computer's store, from which reading or writing is to commence, and takes a file name (a sequence of characters) and file mode ("*r*" for reading, "*w*" for re-writing - creating a new file, or emptying an existing file - and "*a*" for appending to the end of an existing file) as input parameters. If the operation is unsuccessful (for example the file might have read or write protection), *NullPtr* is returned. We assume the set of such pointers *Ptr*:

    [Ptr]

    NullPtr : Ptr

```
┌─ SysGetPtr ───────────────────
│ filename? : seq Char
│ filemode?, filemode! : {⟨r⟩, ⟨w⟩, ⟨a⟩}
│ Sysptr! : Ptr
├───────────────────────────────
│ filemode! = filemode?
└───────────────────────────────
```

and define

    SuccSysGetPtr    ≙  [ SysGetPtr | Sysptr! ≠ NullPtr ]
    UnSuccSysGetPtr  ≙  [ SysGetPtr | Sysptr! = NullPtr ]

The second operation, *SysWrite*, takes the pointer returned by *SysGetPtr* and *WriteSeq*, the sequence of characters to be written, and returns the boolean variable *NoWriteError* indicating whether or not the operation was successful.

Although we are not concerned with the operational detail of how the computers filestore is changed by an operation, we assume that the filestore is a mapping from *Ptr* to *Cont*

    [Cont]
    Store ≙ [ FStore : Ptr → Cont ]

<!-- PDF p.98 / printed p.95 -->

and define a function that converts the contents of a stored file into a sequence of characters:

```
┌───────────────────────────────
│ storedseq : Cont → seq Char
└───────────────────────────────
```

We now define the operation *SysWrite*: it has the input parameters *Sysptr*,[?402] *WriteSeq?* and *filemode?* and returns the flag *NoWriteError* indicating the success or otherwise of the operation. If the operation was unsuccessful, *FStore* will not change, otherwise if *filemode?* indicates a write, its *Sysptr* element will now be associated with *WriteSeq* (through the **storedseq** function), and if *filemode?* indicates an append, that element will now be associated with the concatenation of its previous association concatenated with *WriteSeq*:

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

The final operation that we assume, *SysRead*, is analogous to *SysWrite*, takes the parameter *filemode* (which must equal "*r*") and the pointer returned by *SysGetPtr*, returning the flag *NoReadError* indicating its success or otherwise, and in the former case, the sequence of characters *ReadSeq*, associated with *Sysptr* in *Store* (through **storedseq**); in all cases *Store* remains unchanged:

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

<!-- PDF p.99 / printed p.96 -->

    SuccSysRead    ≙  [ SysRead | NoReadError! ]
    UnSuccSysRead  ≙  [ SysRead | ¬ NoReadError! ]

To totalise the read and write operations, we define the error messages:

    ErrorCannotOpenFile  ≙  [ rep! : Report | rep! = "Cannot open file" ]
    ErrorWritingFile     ≙  [ rep! : Report | rep! = "Error writing file" ]
    ErrorReadingFile     ≙  [ rep! : Report | rep! = "Error reading file" ]

to give:

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

We note that *WriteToStore* contains the input parameters *filename?*, *filemode?* and *WriteSeq?*, which will be provided by the quote operation. We recognize that text read from store will be appended to the document and so must allow for the possibility that the editor's capacity will be exceeded, and define:

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

We note that *ReadFromStore* contains the input parameters *filename?* and *filemode?* (which will be provided by the quote operation) and returns the component *ReadSeq!*.

<!-- PDF p.100 / printed p.97 -->

### 6.3 The Doc7 State

In order to enable text entered at the keyboard to be directed either to the document or to the *QuoteBuffer* it is necessary to incorporate two states into the editor: a *State_Doc* for normal document editing and a *State_Quote* for *QuoteBuffer* editing. Further, some quoted commands also require the file name (a sequence of characters), and we therefore extend the document state as follows:

    DocState  ≙  [ State : {State_Doc, State_Quote} ]
    DocName   ≙  [ Name : seq Char ]
    Doc7      ≙  Doc6 ∧ QuoteBuffer ∧ DocState ∧ DocName

*Name* is to be provided by the (operating system) command to start editing, and is assumed to be input to the editor through that command; *QBuff* is initially set to the empty sequence, with the editor in *State_Doc*, giving:

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

All operations (with the exception of the search/replace commands - see Section 7) are begun and terminated by pressing a particular key (the quote key), unlike the other operations specified so far which require the implementation to "bind" each one to a different key. When the document is in *State_Doc* and the quote command (through the quote key) changes nothing except the state (which is changed to *State_Quote*) and the quote buffer (which is emptied ready to receive text):

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

<!-- PDF p.101 / printed p.98 -->

After the appropriate text has been entered into *QBuff*, the quote key is pressed again (now, of course, in *State_Quote*) and this acts as a request for the operation - dictated by the *QBuff* text - to be carried out ("request" since some of these commands will be concerned with the operating system, and may, for a variety of reasons not concerned with the editor, fail). We are not concerned with the explicit specification of such operating system operations (although we do make limited assumptions about the input and output relating to each, Section 6.2).

In order to save unnecessary repetition in the specification of the quote operations, we define two operations that perform a quote request, distinguishing between a document content change - *QuoteRequestContentChange* - and no content change - *QuoteRequestNoChange*.

We first define the operation *QuoteRequest* which is executed in *State_Quote* and terminates in *State_Doc* with the document name, paste and quote buffers unchanged, allowing only the content of the document and marked text to change, and providing the *filename* and *filemode* input for operating system i/o:

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

If a quote (request) operation does change the content of the document, the mark is reset:

    QuoteRequestContentChange ≙ [ QuoteRequest | MarkSeq′[?404] = MarkedSeq = ⟨ ⟩ ]

and we note that the operation defines all components of the *Doc7* state except the content of the document, and therefore when using it we ensure that the whitespace and null lines invariant of *Doc3* is maintained (using the *Rem* operations of Section 3.3) which therefore preserve the *Doc7* invariant.

We finally define a quote (request) operation that allows neither document content nor marked text to change:

    QuoteRequestNoChange ≙ QuoteRequest ∧ ΞDoc5[?405]

and we note that this operation defines all components of the *Doc7* state, and so when using this operation we ensure that the *Doc7* invariant is preserved.

<!-- PDF p.102 / printed p.99 -->

Each quote operation, except abort and escape, will be identified by its first letter, with optional arguments being separated by spare[?406] characters; we require that the abort operation is entered in full to preclude possibly disastrous consequences, the escape operation being identified by the character "!". We introduce:

    a, b, i, o, q, r, s, t, w, ! : Char

#### 6.4.1 The Abort Command

This command returns control to the operating system without saving the contents of the document to backing store. We assume the set *SysOp* of operating system instructions and introduce:

    [SysOp]

    SysReturnControl : SysOp

noting that it has no associated input. We define the command for requesting an abort, which is always successful:

```
┌─ RequestAbort ────────────────
│ QuoteRequestNoChange
├───────────────────────────────
│ ⟨a, b, o, r, t⟩ = QBuff
│ rep! = "OK"
└───────────────────────────────
```

to give:

    Abort_Quote ≙ RequestAbort ; SysReturnControl

#### 6.4.2 The Save Command

The command writes the entire content of the document to store; we note that the content of the document might not have changed since it was loaded from store, or since it was last written, and so define the error message:

    ErrorDocNotChanged ≙ [ rep! : Report | rep! = "Document not changed" ]

This operation specifies the sequence of characters to be writen, *WriteSeq*, as the entire document, provides *filemode* as "*w*" and *filename* as the document name (as input to the *WriteToStore* operation of Section 6.2), and does not change the content of the document:

<!-- PDF p.103 / printed p.100 -->

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

and we have:

```
Save_Quote ≙
        RequestSave ≫ WriteToStore
    ∨
        RequestSave ≫ ErrorDocNotChanged
```

Our comments of Section 6.4 indicate that, since we are using *QuoteRequestNoChange*, there are no proof obligations associated with the *Save* operation.

#### 6.4.3 The Write And Append Commands

These commands write or append non-empty marked text to a named file, and do not change the document. We define a "proper" prefix relation in which *S* is a proper prefix of *T* if and only if *S* is a prefix of *T* but not equal to it:

```
┌───────────────────────────────
│ _ prefix₁ _ : seq X × seq X → 𝔹
├───────────────────────────────
│ S prefix₁ T  ⇔  S prefix T ∧ S ≠ T
└───────────────────────────────
```

and now define the operation to write marked text, which specifies *filemode* as "*w*", *WriteSeq* as *MarkedSeq* and provides *filename* as the contents of the quote buffer following the first two characters (since these characters indicate the quoted operation required) as input to *WriteToStore*:

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

<!-- PDF p.104 / printed p.101 -->

and the analogous operation to append marked text, with *filemode* specified as "*a*":

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

We require that the marked text is non-empty, and use the *ErrorNoTextMarked* schema of Section 5.2 to give:

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

As in the previous section, the use of *QuoteRequestNoChange* ensures that we have no proof obligations.

#### 6.4.4 The Quit Command

This command has no argument and first performs a save operation (if necessary - i.e. if the document's content has changed) and if successful issues an "OK" report, subsequently returning control to the operating system; if the save is necessary, but unsuccessful, editing continues with the document unchanged. We define:

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

<!-- PDF p.105 / printed p.102 -->

to give:

```
Quit_Quote ≙
        RequestQuit ≫ SuccWriteToStore ; SysReturnControl
    ∨
        RequestQuit ≫ ErrorDocNotChanged ; SysReturnControl
    ∨
        RequestQuit ≫ UnSuccWriteToStore
```

#### 6.4.5 The Input Command

This command inserts text from a named file to the current cursor position, and we specify a request operation to provide *filemode* as "*r*" and *filename* as the contents of the quote buffer following the first two characters as input for *ReadFromStore* (Section 6.2):

```
┌─ RequestInput ────────────────
│ QuoteRequestContentChange
├───────────────────────────────
│ ⟨i, sp⟩ prefix₁ QBuff
│ filemode! = ⟨r⟩
│ filename! = QBuff after 2
└───────────────────────────────
```

the text from a successful input is the concatenated on to the end of the left character sequence:

```
┌─ InputReadSeq ────────────────
│ ΔDocI[?409]
│ ReadSeq? : seq Char
├───────────────────────────────
│ Left_Char′ = Left_Char ⁀ ReadSeq?
│ Right_Char′ = Right_Char
└───────────────────────────────
```

We note that the file might not exist, that it might be of an unsuitable type (e.g. not a text file) or that the input may cause the capacity of the editor to be exceeded, and so define:

    ErrorFileNotExist     ≙  [ rep! : Report | rep! = "File does not exist" ]
    ErrorUnsuitableFile   ≙  [ rep! : Report | rep! = "Unsuitable file" ]

to give:

<!-- PDF p.106 / printed p.103 -->

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

Only the first disjunction will change the document, and in line the comments made in Section 6.4 regarding *QuoteRequestContentChange* we ensure that the *Doc7* invariant is maintained.

#### 6.4.6 The Move To Line Number Command

This command moves the cursor to the beginning of the line number indicated by the *QBuff* text; if this number exceeds the number of lines in the document, the cursor is positioned at the beginning of the last line.

We assume the set of numbers *NumChar*, a subset of *Char*:

    NumChar ⊂ Char

and introduce a total function that converts a sequence of *NumChar* into a natural number:

    ConvNum : seq NumChar → ℕ

The command is a cursor movement command and so all *Doc7* components (except the cursor) remain unchanged. We define:

```
┌─ RequestMvLineNumber ─────────
│ QuoteRequestContentChange
├───────────────────────────────
│ ran QBuff ⊆ NumChar
│ DocCurX′ = 1
│ DocCurY′ = min (ConvNum QBuff, # UDLines)
└───────────────────────────────
```

to give, noting that we must preserve the *Doc3* invariant:

<!-- PDF p.107 / printed p.104 -->

```
MoveLineNumber_Quote ≙
        (FlagPrevCursor ; RequestMvLineNumber ;
        RemTrailWS ; RemTrailNL) ∧ Success
```

Similar comments to those made regarding the discharge of the proof obligation for *Input* also apply here.

#### 6.4.7 The Escape Command

Communication with the operating system from within the editor may be achieved through a *Quote* operation: *QBuff* text commencing with the "!" character constitutes a request for such a command, the test[?410] for the command itself being the quote buffer text following that character. We introduce an operating system interpretive command, *commandseq*, which accepts a sequence of characters, and performs the appropriate action:

    SysInterpret : SysOp

We define:

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

to give:

```
Eseape_Quote[?412] ≙
        Escape.ProvideText ≫ SysInterpret ∧ Success
    ∨
        ErrorNoCommmandGiven[?413]
```

Note that although the system command may not succeed, the *Doc7* operation itself is successful.

<!-- PDF p.108 / printed p.105 -->

### 6.5 The Quote Command

We now express the effect of pressing the quote key, when the editor is in *Quote* state, as a disjunction of the above operations. However, when *QBuff* contains text other than that defined in the previous sections describing the *Quote* operations, an error is reported. We define:

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

to give the error message:

```
┌─ ErrorQuoteError ─────────────
│ QuoteRequestNoChange
│ ¬ ValidQBuffText
│ rep! : Report
├───────────────────────────────
│ rep! = "Quote error"
└───────────────────────────────
```

We therefore have:

```
Quote_StateQuote  ≙  Abort_Quote   ∨  Save_Quote  ∨  Write_Quote  ∨
                     Append_Quote  ∨  Quit_Quote  ∨  Input_Quote  ∨
                     Escape_Quote  ∨  ErrorQuoteError
```

and we now express the *Quote* operation as the disjunction of the operations specified on the *Doc* and *Quote* states:

    Quote_Doc7  ≙  Quote_StateDoc ∨ Quote_StateQuote

Since we have demonstrated that each individual operation preserves the invariant on *Doc7*, the disjunction of those operations must do likewise.

<!-- PDF p.109 / printed p.106 -->

### 6.6 Promotion Of Quote Buffer Edit Operations To The Doc7 State

We use the same names for the quote buffer edit operations as those we specified on *Doc1*; the former are promoted to *Doc7* by stipulating that they do not affect the *Doc6* components, and the latter by stipulating that they have no affect on the quote buffer, document state or document name. We define the set of names:

```
QBuffEditOps  ≙  { InsertChar, LeftMoveChar, RightMoveChar,
                   CursorLeftChar, CursorRightChar,
                   LeftDeleteChar, RightDeleteChar }
```

and:

    PromoteToDoc7 ≙ ΞQuoteBuffer ∧ ΞDocState ∧ ΞDocName

to give:

```
∀ OP : QBuffEditOps •
    OP_Doc7  ≙      [ OP_Quote[?414] ∧ ΞDoc6 | State = State_Quote ]
                ∨
                    [ OP_Doc6 ∧ PromoteToDoc7 | State = State_Doc ]
```

and, clearly, we have no proof obligations associated with this promotion.

### 6.7 Promotion Of Remaining Doc6 Operations To The Doc7 State

We note that the remaining *Doc6* operations may successfully be effected only in *State_Doc*, and they are promoted in the same way as those described above. We use *EditOps2* (Section 5.2.1) to define the set of names:

    EditOps3 ≙ EditOps2 ∪ { Lift, Cut, Paste, ExchMTextPBuff }

to give:

    NonQBuffEditOps ≙ EditOps3 − QBuffEditOps

We define the error schema:

```
┌─ ErrorIllegalQBuffEditOp ─────
│ ΞDoc7
├───────────────────────────────
│ State = State_Quote
│ rep! = "Illegal edit operation"
└───────────────────────────────
```

<!-- PDF p.110 / printed p.107 -->

to give:

```
∀ OP : NonQBuffEditOps •
    OP_Doc7  ≙      [ OP_Doc6 ∧ PromoteToDoc7 | State = State_Doc ]
                ∨
                    ErrorIllegalQBuffEditOp
```

and again we have no associated proof obligation.

## 7 The Search And Replace Operations

We now consider the operations to search for a specific string of characters, and (possibly) to replace that string with another specified string of characters. Since we wish all document changes to take place at the cursor position we do not allow "global" string replacement, and specify the replace operation as having the pre-condition that the cursor must be at the start of text matching that specified in the search operation.

### 7.1 The Doc8 State

We enrich the document state by providing two buffers:

    SearchBuffer   ≙  [ SBuff : seq Char ]
    ReplaceBuffer  ≙  [ RBuff : seq Char ]
    Doc8           ≙  Doc7 ∧ SearchBuffer ∧ ReplaceBuffer

and initially each buffer is set to the empty sequence:

    Initialize_Doc8 ≙ [ Initialize_Doc7 ∧ ΔDoc8 | SBuff′ = RBuff′ = ⟨ ⟩ ]

As described in Section 6.3 pressing the quote key - *QuoteKey* - change states. Each time *QuoteKey* is pressed in *State_Quote*, the quote buffer is emptied ready to accept new text. Pressing the search key - *SearchKey* - will then have three effects: copying the contents of the quote buffer into the search buffer, carrying out a search operation for that text, and returning the editor to *State_Doc*. The replace operation performs a similar function except that text immediately following the cursor in the document must match that in *SBuff* (as it would immediately following a successful search operation) to enable a replace operation to start.

For example, if we wanted to search for the string "*foo*" and replace it with the string "*baz*", we would type the following at the keyboard (with the document initially in *State_Doc*):

<!-- PDF p.111 / printed p.108 -->

    QuoteKey  f o o  SearchKey  QuoteKey  b a z  ReplaceKey

Notice that both *SearchKey* and *ReplaceKey* are pressed in *State_Quote*, and afterwards the search buffer contains "*foo*" and the replace buffer contains "*baz*". To repeat the above search/replace operation we would type:

    SearchKey  ReplaeeKey[?415]

the difference being that now both keys are pressed in *State_Quote* which means that the current contents of the search and replace buffers are used.

### 7.2 Regular Expressions

We wish to use a form of "regular expression" when searching for a string of characters and introduce:

    RegExpression : ℙ (seq Char)

and define a relation which holds when a regular expression matches a prefix of a sequence of characters, and require that an expression cannot match by a sequence that is shorter in length:

```
┌───────────────────────────────
│ _ regexpmatches _ : RegExpression × seq Char → 𝔹
├───────────────────────────────
│ e regexpmatches s  ⇒  # e ≥ s[?416]
└───────────────────────────────
```

Since we wish the document to be in a matched state when text in the search buffer matches text immediately following the cursor, we now define a relation between sequences of characters, the first of which may contain a bracket expression:

```
┌───────────────────────────────
│ _ matches _ : seq Char × seq Char → 𝔹
├───────────────────────────────
│ ∀ e : RegExpression ; s1, s2 ∈ seq Char | s1 ∉ RegExpression •
│         e matches s2  ⇔  e regexpmatches s[?417]
│         s1 matches s2  ⇔  s1 prefix s2
└───────────────────────────────
```

We note that a sequence cannot be matched by one that is shorter in length.

### 7.3 The Down Search Operation

Search operations are cursor-changing operations and will start only when the search buffer (which does not change) is non-empty, and will terminate in *State_Doc*. We define:

<!-- PDF p.112 / printed p.109 -->

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

We need a means of determining the length of the matched string in the document, and so we define a partial function which takes two matched sequences (the first of which, of course, may be a regular expression) and returns the length of the match (i.e. the length of the matching prefix of the second sequence):

```
┌───────────────────────────────
│ matchedlength : seq Char × seq Char ⇸ ℕ
├───────────────────────────────
│ (s1, s2) ∈ dom matchedlength  ⇔  s1 matches s2
└───────────────────────────────
```

After a successful search, *SBuff* will match *Right_Char* and this will be the first such available match - i.e. the text in *SBuff* must not match the content of the document from:

    # Left_Char + 2 .. # Left_Char′ + matchedlength (SBuff, Right_Char) − 1

since the search will have started from the second element of *Right_Char*,and the match is with the first matchedlength *SBuff* elements of *Right_Char′*. We define a successful down search in *State_Doc*, which has the pre-condition that the length of *Right_Char* must be at least that of the length of the search buffer:

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

The only difference between this and the corresponding operation in *State_Quote* is that the quote buffer is first copied into the search buffer, with the operation terminating in *State_Doc*. We define:

<!-- PDF p.113 / printed p.110 -->

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

to give:

    SuccDownSch_Quote ≙ CopyQBuffSBuff ; SuccDownSch_Doc

An unsuccessful find in *State_Quote* occurs when the search buffer is not in the tail of *Right_Char* (since the search will start from its second element):

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

and we have the corresponding operation in *QuoteState*:

    UnSuceDownSch_Quote [?502] ≙ CopyQBuffSBuff ; UnSuccDownSch_Doc

To totalise the operation, we define the following report and error message:

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

To give:

<!-- PDF p.114 / printed p.111 -->

    SuccDownSearch    ≙ SuccDownSch_Doc ∨ SuccDownSch_Quote
    UnSuccDownSearch  ≙ UnSuccDownSch_Doc ∨ UnSuccDownSch_Quote
    ErrorSBuffEmpty   ≙ ErrorSBuffEmpty_Doc ∨ ErrorSBuffEmpty_Quote

For each search operation, only the search buffer, document state and cursor position may change; however since a change of cursor position may result in a change of content (it may necessitate the removal of whitespace), we also unmark marked text in such cases. We define the promotion schema:

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

to give:

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

The last two disjunctions do not change the content of the document; for the first, we ensure the preservation of the *Doc3* invariant by post-sequential composition with the *Rem* operations of Section 3.3.

### 7.4 The Up Search Operation

We define searches up the document in an entirely analogous way. The difference occurs in the specification of the 'first match': the search buffer must not match the content of the document from:

    # Left_Char′ + 2 .. # Left_Char + matchedlength (SBuff, Right_Char) − 1

<!-- PDF p.115 / printed p.112 -->

since the search will have started from the element corresponding to the penultimate character of the matched sequence of *Right_Char* (or, if the search buffer is of unit length, from the last element of *Left_Char* up to the second element of *Right_Char′*). We define:

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

An unsuccessful up find in *State_Quote* occurs when the search buffer is not in the front of *Left_Char*:

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

We may now specify the up search operation:

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

The comments made regarding proof obligations for the promotion of the down search operation (Section 7.3) also apply here.

<!-- PDF p.116 / printed p.113 -->

### 7.5 The Replace Operation

A *Replace* operation can only be successful when the document is in a "matched" state - i.e. when *SBuff* matches *Right_Char*, after which the document is left in *State_Doc*. The operation can be carried out in either *State_Doc* or *State_Quote* and we first consider the former: the text matched with that in the search buffer is first removed, the state remaining unchanged:

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

and then the text in the replace buffer is concatenated on to the front of *Right_Char*:

```
┌─ InsRBuffText ────────────────
│ ΔDoc1
│ ReplaceBuffer
├───────────────────────────────
│ Right_Char′ = RBuff ⁀ Right_Char
│ Left_Char′ = Left_Char
└───────────────────────────────
```

and we have:

    SuccRpl_Doc ≙ RemMatehedText [?506] ; InsRBuffText

The difference between this and the corresponding operation in *State_Quote* is that the quote buffer is first copied into the replace buffer, after which the quote buffer is emptied. In a similar schema to *CopyQBuffSBuff* of Section 7.2, we define:

    CopyQBuffRBuff ≙ CopyQBuffSBuff[ReplaceBuffer \ SearchBuffer]   [?507]

to give:

    SuccRpl_Quote ≙ CopyQBuffRBuff ; SuccRpl_Doc

An unsuccessful *Replace* operation in *State_Doc* occurs when the document is not in a matched state, when neither the content nor the state change. We define:

<!-- PDF p.117 / printed p.114 -->

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

and have the corresponding operation in *State_Quote*:

    UnSuccRpl_Quote ≙ CopyQBuffRBuff ; UnSuccRpl_Doc

We define the following error message:

```
┌─ RepNoMatchSBuff ─────────────
│ rep! : Report
├───────────────────────────────
│ rep! = "No match with search buffer"
└───────────────────────────────
```

Note that there is no replace schema analogous to the search schema *ErrorSBuffEmpty* since we want to make it possible to replace the found string with the null string - i.e. to enable a series of deletions to be made. For the replace operation, only the replace buffer, document state and document content may change (and in the latter case marked text must be unmarked), and we define:

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

and, recognizing that the *Replace* operation may exceed the editor's capacity, we define:

```
┌─ ErrorReplaceFull_Doc ────────
│ ΞDoc8
├───────────────────────────────
│ State = State_Doc
│ rep! = "Editor full"
└───────────────────────────────
```

<!-- PDF p.118 / printed p.115 -->

    ErrorReplaceFull_Quote ≙ CopyQBuffRBuff ; ErrorReplaceFull_Doc
    ErrorReplaceFull       ≙ ErrorReplaceFull_Doc ∨ ErrorReplaceFull_Quote

to give:

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

The comments made regarding proof obligations for the promotion of the down search operation (Section 7.3) also apply here.

### 7.6 Promotion Of The Doc7 Operations To The Doc8 State

We use *EditOps3* (Section 6.7) to define the set of names:

    EditOps4 ≙ EditOps3 ∪ { Quote }

We require that each operation in the set *EditOps4* does not change the search or replace buffers, to give:

```
∀ OP : EditOps4 •
        OP_Doc8 ≙ OP_Doc7 ∧ ΞSearchBuffer ∧ ΞReplaceBuffer
```

Clearly this promotion process does not incur proof obligations.

## 8 A Window On To the Display

In Section 2 we incorporate an unbounded display into the specification of the editor; in this section we specify a (movable) window on to that display. We first define a *Window* state, orthogonal to the *Doc* model.

<!-- PDF p.119 / printed p.116 -->

### 8.1 The Window State

The window is assumed to be rectangular and of fixed width and height:

    WinWidth, WinHeight : ℕ₁

We need a means of moving the window, and we introduce two values that represent its horizontal and vertical displacement from a fixed origin (so that the window always appears to the right of and below the origin):

    WindowOffset ≙ [ OffsetX, OffsetY : ℕ ]

The window contains a non-empty sequence of display lines (Section 2.1), the sequence having a maximum length of *WinHeight*, each line of the sequence being of maximum length *WinWidth*. The lines are displayed in the window one above the other, with the first line at the top of the window, the second immediately below it and so on, each vertically aligned with its left hand end flush against the left edge of the window

We incorporate a cursor, a pair of positive natural numbers, such that the top left hand corner of the window corresponds with cursor position (*1*, *1*), the bottom right hand corner being (*WinWidth*, *WinHeight*), and which we require to always be in the window:

```
┌─ WindowCursor ────────────────
│ WinCurX, WinCurY : ℕ₁
├───────────────────────────────
│ 1 ≤ WinCurX ≤ WinWidth
│ 1 ≤ WinCurY ≤ WinHeight
└───────────────────────────────
```

and have:

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

We define the *Doc9* state by conjoining the *Doc8* and *Window* states. In order to obtain the sequence of window lines from the sequence of unbounded display lines we first mask

<!-- PDF p.120 / printed p.117 -->

out that part of the unbounded display lying to the left and right of the window position, to obtain the sequence *WinMaskLines*:

```
∀ y : 1 .. # UDLines •
    WinMaskLines y = (UDLines y after OffsetX) for WinWidth
```

We note that the definition of for ensures that the length of each *WinMaskLine* does not exceed *WinWidth*.

We now mask out that part of *WimMaskLines* [?509] lying above and below the window:

    WindowLines = (WinMaskLines after OffsetY) for WinHeight

and again, the definition of for ensures that the length of *WindowLines* does not exceed *WinHeight*.

The window cursor values will be the difference between the document cursor values and the offsets:

[Figure: diagram of the unbounded display and the window. A large region open to the right and bottom (top edge continues as a dashed line to the right, left edge continues as a dashed line downward) is labelled "UNBOUNDED DISPLAY OF THE DOCUMENT" (small caps). Inside it a smaller rectangle labelled "Window" at its bottom right. Dashed dimension arrows: *OffsetY* (vertical, from top of display to top of window); *OffsetX* (horizontal, from left of display to left of window); *UDCurY* (vertical, from top of display down to the cursor, a small filled block inside the window); *UDCurX* (horizontal, from left of display to the cursor); *WinCurY* (vertical, from top of window down to cursor level); *WinCurX* (horizontal, from left of window to cursor).]

<!-- PDF p.121 / printed p.118 -->

We now define:

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

We note that the *WindowLines* sequence is redundant since it may be calculated from *UDLines*, the offsets and the window cursor; further, the offsets may be calculated from the window cursor, and vice-versa, using *Doc8* and the *UD* cursor. Hence *Doc8* and either the offsets or the window cursor uniquely define *Doc9*.

We show that the character at the (*WinCurY*, *WinCurX*) window position is the same as that at the (*UDCurX*, *UDCurY*) position of the unbounded display of the document:

**Lemma 3 : 8.2a**

        Doc9
      ⊢
        (WindowLines WinCurY) WinCurX = (UDLines UDCurY) UDCurX
      ■

**Proof**

<!-- PDF p.122 / printed p.119 -->

```
1    WindowLines WinCurY =
         ((WinMaskLines after OffsetY) for WinHeight) (UDCurY−OffsetY)
                                                                   Doc9
2    1 ≤ WinCurY ≤ WinHeight                              WindowCursor
3.   1 ≤ UDCurY−OffsetY ≤ WinHeight                           2., Doc9
4.   WindowLines WinCurY =
         (WinMaskLines after OffsetY) (UDCurY−OffsetY)    1., 3., propt. for
5.   WindowLines WinCurY = WinMaskLines UDCurY                4., Doc9
6.   (WindowLines WinCurY) WinCurX =
       (((UDLines UDCurY) after OffsetX) for WinWidth) (UDCurX−OffsetX)
                                                              5., Doc9
7.   1 ≤ WinCurX ≤ WinWidth                               WindowCursor
8.   1 ≤ UDCurX−OffsetX ≤ WinHeight                           7., Doc9
9.   (WindowLines WinCurY) WinCurX =
       ((UDLines UDCurY)after OffsetX) (UDCurX−OffsetX)   6., 8., propt. for
10.  (WindowLines WinCurY) WinCurX = (UDLines UDCurY) UDCurX
                                                    8., propt. after [?510]
```

■

We specify the initialization operation as:

    Initialize_Doc9 ≙ Initialize_Doc8 ∧ ΔDoc9

which implies that initially both offsets are zero, and both window cursors are set to unity:

**Lemma 3 : 8.2b**

        Initialize_Doc9
      ⊢
        OffsetX′, OffsetY′ = 0, 0
        WinCurX′, WinCurY′ = 1, 1
      ■

**Proof**

```
1.  UDCurX′, UDCurY′ = 1, 1                        Lemma 3 : 2.2d
2.  WinCurX′ : ℕ₁ ∧ WinCurY′ : ℕ₁                           Doc9′
3.  1 − OffsetX′ ≥ 1 ∧ 1 − OffsetY′ ≥ 1              1., 2., Doc9′
4.  OffsetX′ : ℕ ∧ OffsetY′ : ℕ                             Doc9′
5.  OffsetX′, OffsetY′ = 0, 0                              3., 4.
6.  WinCurX′, WinCurY′ = 1, 1                              1., 5.
```

■

<!-- PDF p.123 / printed p.120 -->

**Lemma 3 : 8.2c**

        Initialize_Doc9
      ⊢
        WindowLines′ = ⟨⟨⟩⟩
      ■

**Proof**

```
1.  UDLines′ = ⟨⟨⟩⟩                                 Lemma 3 : 2.2d
2.  # WinMaskLines′ = 1                                   1., Doc9′
3.  WinMaskLines′ = ⟨(⟨⟨⟩⟩ after 0) for WinWidth⟩
                                      1., 2., Lemma 3 : 2.2b, Doc9′
4.  WinMaskLines′ = ⟨⟨⟩⟩                           3., WinWidth : ℕ₁
5.  WindowLines′ = (⟨⟨⟩⟩ after 0) for WinHeight
                                          4., Lemma 3 : 2.2b, Doc9′
6.  WindowLines′ = ⟨⟨⟩⟩                            5., WinWidth : ℕ₁
```

■

Thus we discharge PO 0.

#### 8.2.1 An Operation To Centre The Window

We specify an operation to move the window vertically such that the current line appears in the centre of the window, document length permitting. We introduce:

    HalfWinHeight : ℕ | HalfWinHeight = WinHeight/2

(where "/" represents integer division, and so *HalfWinHeight* has minimum value *1* and maximum value *WinHeight*).

We require that *OffsetY* should be changed such that *WinCurY* equals *HalfWinHeight* - i.e. we set *OffsetY* to equal (*UDCurY* − *HalfWinHeight*). In order to preserve the *Doc9* invariant that the offset be non-negative, we thus have the pre-condition:

    UDCurY ≥ HalfWinHeight

and so we define:

<!-- PDF p.124 / printed p.121 -->

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

together with the error message:

```
┌─ ErrorTooNearTop ─────────────
│ ΞDoc9
│ rep! : Report
├───────────────────────────────
│ UDCurY < HalfWinHeight
│ rep! = "Too near top of document"
└───────────────────────────────
```

to give:

    CentreWindow_Doc9 ≙ (CenWin ∧ Success) ∨ ErrorTooNearTop

The second disjunction does not change *Doc9*, and the first changes only *OffsetY*, the pre-condition ensuring that the invariant is preserved, and noting our comments in Section 8.2 that *Doc8* together with the offsets uniquely define *Doc9*, we discharge PO 1.

#### 8.2.2 Promotion Of Doc8 Operations To The Doc9 State

Some of the *Doc8* operations will result in the cursor being moved to a position outside the current window, and the *Doc9* invariant requires that for such operations an appropriate window change is made in order to reposition the window to regain the cursor.

In general, if the operation leaves the cursor in the current window, it is desirable that there should be no window change, since a redisplay of the window in such cases would be both unnecessary, and tiresome for the user. However for some such operations the user would expect a window change (for example, *CursorDownPage* [?511]). therefore our promotion policy for a *Doc8* operation leaving the cursor in the window is non-deterministic, allowing a window change to be made.

We define an operation with pre-condition that the cursor is currently in the window, in which all *Doc8* components do not change but which allows the window offsets to change, providing that the new window position contains the cursor:

<!-- PDF p.125 / printed p.122 -->

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

When an operation moves the cursor outside the current window, we change the offsets (and, necessarily, the window cursor, but leaving all other components of *Doc9* unchanged), but, clearly, for a given unbounded display there is more than one window change which will reposition the window to regain a "lost" cursor.

Although we are not concerned with the implementation of the window-policy for *Doc8* operations that leave the cursor outside the window, we stipulate that if the cursor can be regained by a *Scroll* (a change in the vertical offset only) or a *Pan* (a change in the horizontal offset only), then that should be the window reposition operation utilised (thus preserving the same screen columns or lines respectively, enabling the user to locate the screen cursor more easily). We define:

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

It may not be possible to regain the cursor by either of these operations and so we define:

<!-- PDF p.126 / printed p.123 -->

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

to give a promotion operation which is the disjunction of these four window-change operations:

```
WindowPolicy ≙
        (CursorInWindow ∨ Scroll ∨ Pan ∨ ScrollAndPan) ∧ Doc9′
```

We note that the pre-conditions of the four disjunctions form a partition of the set of possible window states, and so the promotion operation is total: it satisfies the *Doc9* requirement that the cursor be in the window since each disjunction does; further, our comments of Section 8.2 indicate that *WindowLines* and the window cursor can be calculated from the operation. Thus *WindowPolicy* represents an operation in which none of the *Doc8* components may change, but allows the offsets (and hence *WindowLines* and the window cursor) to change in line with *Doc9*, and so post-sequential composition with the operation yields a state satisfying the *Doc9* invariant.

We use the set *EditOps4* of Section 7.6 to define the set of names:

    EditOps5 ≙ EditOps4 ∪ {DownSearch, UpSearch, Replace}

to give, for each operation *OP* in the set *EditOps5*:

    ∀ OP : EditOps5 • OP_Doc9 ≙ OP_Doc8 [?512] ; WindowPolicy

We thus discharge PO 1 for each *Doc8* operation.
