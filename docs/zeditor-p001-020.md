# From Z to C — transcription, PDF pages 1–20

Source: `../source/Zeditor.pdf` (Neilson, PRG-101, 1990). Transcribed from page images.

Conventions:
- `<!-- PDF p.N / printed p.M -->` marks each scanned page.
- `[?N]` marks a doubtful spot; N is the ID column in `corrections.csv`.
- Original spellings and typos are kept unless the sheet says otherwise.
- Z notation in Unicode. A vector of variables (an arrow over `AS`/`CS` in the original) is written `AS⃗`, `CS⃗`. Subscript-o variables are written `AS⃗₀` [?21].

---

<!-- PDF p.1 / title page -->

FROM Z TO C : ILLUSTRATION OF A RIGOROUS DEVELOPMENT METHOD

by

D.S. Neilson

Technical Monograph PRG-101
ISBN 0-902928-78-3 [?1]
Hilary 1990
Oxford University Computing Laboratory
Programming Research Group
11 Keble Road
Oxford OX1 3QD
England

<!-- PDF p.2 -->

Copyright © 1990 D.S. Neilson

Oxford University Computing Laboratory
Programming Research Group
11 Keble Road
Oxford OX1 3QD
England

<!-- PDF p.3 -->

**From Z To C: Illustration Of A Rigorous Development Method**

D. S. Neilson
Wolfson College, Oxford

<!-- PDF p.4 -->

# From Z To C: Illustration Of A Rigorous Development Method

## Contents

| | |
|---|---|
| Part One: Overview | 2 |
| Part Two: A Refinement Calculus For Z | 10 |
| Part Three: Z Specification Of A Full Screen Text Editor | 45 |
| Part Four: Hierarchical Refinement Of The Editor Specification | 124 |
| References | 222 |
| Appendix A: Summary Of Abstract State Hierarchies | |
| Appendix B: Summary Of Concrete State Hierarchies | |
| Appendix C: Implementation Of The Editor Specification | |

<!-- PDF p.5 / printed p.2 -->

# PART ONE — Overview

### Introduction

One of the most important developments in computer science has been that of data abstraction, which has enabled the specification of computer systems without regard to implementation detail, and has resulted in the development of many formal specification languages, for example [17], [28] [?3].

A formal specification will undoubtedly provide for a greater understanding of a computer system [22]. It should not, however, be regarded as an end in itself: it may be regarded as a contract between the customer and implementor of a system, and must ultimately be judged on whether it results in the production of better quality software or in the more efficient production of software [15].

Consequently, the process of transforming a formal specification into executable code has attracted attention of many theoreticians, and early work [12], [33] has more recently been supplemented by the production of refinement calculi [2], [5], [7], [14], [21], [23] [?4].

In the literature the examples illustrating the refinement techniques are, of necessity, modest in scope and size; usually the specification is presented in a single flat development upon which the method is then demonstrated.

Little investigation has been done into putting such theoretical results into practice in realistically-sized applications (examples are surveyed below). The main purpose of our work is to demonstrate that a suitable formal basis can be practically and usefully employed in the development of "real" software.

The vehicle for our illustration is a full screen text editor. Whilst this may not be regarded as a commercial-scale development, it is of a size (the specification comprises nearly ninety pages) sufficient to enable conclusions to be made regarding the "scaling-up" of the method to much larger applications.

We had to develop a technique that would cope with the problems of size, and the key factor in the development method is its hierarchical nature, enabling the refinement to proceed in manageable parts. The abstract state is composed of approximately thirty

<!-- PDF p.6 / printed p.3 -->

components having over twenty five invariant relationships, with the implementation comprising approximately the same, and consideration must be given to each of these constituent for each of the sixty operations that are specified and implemented. Even with a specification of modest size, the problems of complexity are considerable.

We propose a novel hierarchical approach to the specification/refinement process. We start with a simple mathematical model of the system and embellish this model in a series of steps (a hierarchy of levels, each one isolating and treating a particular aspect of the requirements) in such a way that each new level embeds the previous one. This specification style is illustrated in [8] [?5]. Note that we use the term "hierarchy" to mean a single level as well as the more normal meaning of a set of levels.

In such a specification only the top-level hierarchy will completely define the desired system. However intermediate levels will also be of significance, since it is possible to apply a refinement calculus at any level to produce a fully deterministic and implementable concrete data type corresponding to each hierarchy (or abstract data type) of the specification. The modularity so-achieved will make reasoning about the development a more manageable task.

It is, of course, possible that this approach might result in an inefficient implementation, since the structure of the design will not necessarily be compatible with that of the specification, but we feel that program transformation techniques [26] can remedy the situation (and, see our conclusions below).

A further advantage of the method concerns prototyping. A crucial problem in constructing any formal specification is to ensure correspondence with an initial (usually informal) set of requirements. One solution that has been proposed is to write the specification in an executable language [11], [31] [?7] enabling the specification to be tested as it is written. The nature of such declarative formulations, however, tend to be make [?6] them more difficult to read than those written in a non-executable specification language (since the latter need not provide the algorithmic solution that the former, by definition, requires) and necessarily compromises the data abstraction qualities of the specification process.

Whilst we support the view that a formal specification should contain a body of theory to help build confidence that it does indeed describe the informal model that it is meant to, we also feel that a rapid prototyping facility would considerably aid this task.

The refinement technique that we use provides for a complete implementation of a specification hierarchy, and this serves the same purpose as a rapid prototype, since we are able to test the specification against the requirements at each stage of the development. The benefit of our approach is that the code produced is not discarded: it forms an integral part of the final implementation.

The emergence of data abstraction is clearly advantageous in many respects (for example, allowing attention to be focused on the similarities of data types, rather than contrasting their differences) but it is not without its problems. When a specification is implemented it will be on hardware that does not have an infinite supply of resources, and although we

<!-- PDF p.7 / printed p.4 -->

do not wish to compromise the abstraction process by the inclusion of such considerations, they are of paramount importance in the implementation.

It is the job of the refinement calculus to bridge the gap between an abstract specification and its implementation: the calculus that we present extends the concept of refinement to permit the introduction of resource limit considerations by consideration of "acceptably" inadequate design decisions.

Of necessity this is a long, detailed and technical piece of work, which we present in four main parts. In this part (Part 1) we state our aims, conclusions and related comments. In Part 2 we present the refinement calculus which provides the formal basis that underpins our development method. We present the abstract specification of the editor in Part 3, and its refinement in Part 4. Appendices A and B summarise the hierarchies of Parts 3 and 4 respectively. The implementation is given in Appendix C.

Each part is, largely, self-contained, with its own introduction and contents sections. The advice we would give to the reader wishing to consider one particular part would be to start with its introduction, followed by the relevant appendix (in the case of Parts 3 or 4, to give an overall picture), before proceeding with the detail.

We assume a knowledge of Z [27], [28], [30] and the Schema Calculus [19], [20] [?2]. The numbering of definitions etc. is best explained by example: Lemma 3:1.4b refers to the second lemma appearing Section 1.4 of Part 3 [?8].

The size of the project has dictated our methodology and also affected our presentation. Although we are able to give the complete abstract specification of the editor, in order to keep the thesis down to a reasonable size, we do not present the refinement in full. We have been honest, however: the entire refinement has been developed rigorously in the manner that we illustrate.

The stimulus for the project was provided by [32] which closely followed the structure of the specification on which it was based [29]; the specification was presented in a hierarchy of three levels, and the implementation was similarly constructed with each level embedded in the next. Although the derivation of the implementation was completely informal, it was felt that the control achieved by using that structure was considerably greater than would otherwise have been the case.

We chose our implementation language, C [18], mainly for its speed and since it was readily available. Other high-level languages would have served the purpose equally well since the programming constructs that our refinement calculus requires (assignment, sequencing, "if" and "do" [5], [7]) are always provided. It is worth noting that languages more strongly typed than C would not provide a "safer" implementation: we place no type-checking requirement on the programming language.

### Conclusions And Further Work

<!-- PDF p.8 / printed p.5 -->

The accent on our approach throughout this project is on rigour rather than formality: for example, we indicate which rules are applicable rather than proving that the rules apply. However the development method does permit a completely formal derivation by virtue of the refinement calculus given in Part 2.

Our experience suggests that a lesser degree of formality could, where it was felt to be necessary, be adopted: each abstract data type will usually contain many operations, some of which will be broadly similar, and once one of a set of such operations has been refined to code, that for the other operations may reasonably safely be written down without recourse to the refinement calculus. Of course, such informality will result in code requiring thorough testing.

The abstract specification played a crucial role in ensuring a deep understanding of all aspects of the system. This has been the experience of many others (for example, [22]).

The development of the six chosen refinement hierarchies proceeded remarkably smoothly, the transition of the operations from specification to code presenting few problems. We recognize that even working within a completely formal framework of program development will not automatically ensure bug-free code. The errors that occurred in our implementation, however, have been of a trivial nature (typing errors and the like) and there have been no errors of a "serious" nature (requiring the re-writing of large parts of the implementation). Of course we have re-written parts of the implementation (there are many possible refinements of a given specification) in the quest for improvement, and the modular structure of the implementation has made this task easier than it would otherwise have been.

In order to simplify the description of operations involving i/o, we included a brief specification of our understanding of some operating system and terminal hardware operations (orthogonal to the main model). Although this formal statement of these operations was of considerable use in the construction of the editor interface, both in the specification and refinement phases, we estimate that interfacing the editor took at least fifty percent of the time spent on the implementation!

Whilst some of this time may be explained by our programming inexperience, the inherent problem of formal development within an operating system and hardware environment that is almost exclusively informal is considerable, and much investigation remains to be done.

The facility to test the specification against its requirements proved to be extremely valuable. Although it didn't uncover any major disparity, it did give rise to some fine-tuning of our requirements, the main one concerning cursor movement, and the orthogonal development of the *QP* state (Part 3, Section 4).

We did, in fact, partially implement the display of the editor (the *Doc9* hierarchy, Part 3, Section 8) at an early stage so that we could view lower-level hierarchies. This approach is made possible because of the independence of implementation hierarchies due to the "report-passing" style of programming adopted (see Part 4, Section 0 [?10]).

<!-- PDF p.9 / printed p.6 -->

We completed the specification before starting its refinement, and in some cases the (minor) changes made as a result of testing did percolate up through the specification hierarchies, which leads us to believe that for some programs, the simultaneous development of specification and implementation might be a very useful approach - the hierarchy under current construction will then be built on lower levels which are demonstrated to have met the informal requirements (through their implementation), minimising specification change.

A further advantage in adopting a simultaneous development strategy is that the development team would, at regular intervals, have something concrete for discussion with the client, permitting early feedback whilst also demonstrating that progress is being made!

The consideration of specification change is important since, although we can demonstrate to the client that the specification matches his/her requirements, the change may be forced by factors outside their immediate control.

We wished to demonstrate the impact of specification change on the refinement method by implementing a specification that we would then change and re-implement. In fact the specification that we present is the amended one; initially we did not permit the use of regular expressions in the search operations, and did not include the move-to-line operation (Part 3, sections 7.2 and 6.4.6 respectively). Space considerations prevent us from presenting the original specification and refinement.

The introduction of regular expressions necessitated the re-refinement of the two search operations (resulting in the introduction of the *CharMatched* routine of *ConcDoc9* (Appendix C, page xi [?11]). The addition of the move-to-line command necessitated its refinement in *ConcDoc8* (Appendix C, page xiii [?11]), but it could then be promoted in the same way as other operations on that state, and required no further work.

Further, after the implementation was complete we changed our notion of a line in the lowest-level hierarchy (we initially modeled a document line *Doc1* and a display line *Doc3* [?9] in the same way, and realised, at a very late stage, that they would be better modelled in a different way). The scope of this specification change was limited to the four line operations in *Doc1*, and, accordingly, our only change in the refinement concerned those four operations.

Clearly the hierarchical structure of the method limits the amount of work that has to be done as a result of specification change, considerably simplifying the task of software maintenance.

Another aspect of the modularity of the development method that we were not able to investigate, but feel that it would be worthwhile to do so, is the re-usability of the specification.

We feel it would be possible to add and refine specification hierarchies, in exactly the same way that we have done here, using the existing code; again, the "report-passing" implementation facilitates this approach.

<!-- PDF p.10 / printed p.7 -->

One example of re-use would be to regard the editor as the basis on which, say, a functional programming tool was to be built: by removing the display *Doc9* hierarchy (Part 3, Section 8), adding hierarchies to provide the necessary functionality (e.g. the addition of "fold" and "unfold" operations), promoting existing operations to the new hierarchies, and putting the display module back at the highest level would enable exactly the same method of implementation that we have used to be followed. The existing code would form an integral part of the extended implementation.

Critics of formal methods will point to the impossibly large number of proof obligations associated with any reasonably-sized program, and this has been the main reason for our rigorous, rather than formal, treatment.

Although we found the power of the Schema Calculus to be a considerable asset in the construction of the specification, but would welcome a tool for automatic schema expansion, [?12] the repeated use of schema inclusion in the construction of the specification means, particularly at higher levels, that the problems associated with the identification of proof obligations are severely compounded.

Since the completion of this thesis we have employed a proof-assistant [1] [?22], to identify and discharge the obligations associated with the *Doc1* specification hierarchy (Part 3, Section 1). Over one hundred proof obligations emerged. It is clear that any formal development of a large system without the aid of machine assistance would present considerable problems.

We strongly feel that there is a clear need for machine assistance, both in the identification and discharge of proof obligations. Parts of the refinement can be calculated and here, also, computer assistance would be most welcome. The provision of a support environment, for example, as described in [4], would certainly make the entire process more manageable and would, we feel, enable a more formal and less rigorous approach to be adopted.

We had anticipated that the performance of the editor would be inadequate, and, as indicated in the introductory section, that some program transformation would be necessary. To our pleasant surprise, however, we found that the editor's response times certainly matched that of the one that formed the basis for its requirements [32], and consequently we have left the implementation in a structure that exactly matches that of its specification. We have no reason to believe that our code is less efficient than would have been produced by more traditional means.

My design/programming inexperience was a major contribution to the duration of the project: correct refinement does not necessarily imply a good design! It is argued that intuition and experience are a computer scientist's most valuable tools, and any techniques used may, at best, be a supplement to them [24]. We feel, however, that there is considerable room for creativity in methodologies such as the one we present, and indeed that a design team would welcome a basis that enabled the determination that a particular implementation did exactly the job for which it was designed.

<!-- PDF p.11 / printed p.8 -->

### Related Work

As stated in our introduction, there are very few examples of large- and medium-scale formal development of software; this applied science is still very much in its infancy. Much interest has centered on "safety-critical" software (for example where peoples' lives may be endangered by software failure), but the nature of these projects is such that publication is restricted.

The Vienna Development Method, VDM [17], is the longest-established of the formal development methods, and has been used extensively in both academic and industrial courses. It is probably not now as widely used as other specification languages (notably Z), but it has been of fundamental importance in its influence of formal methods techniques.

VDM has been applied most notably in the areas of systems programming, where the complexity of the code is particularly suited to formalism, and programming language semantics, most notably the description of PL/1.

It is noted that the scale of such developments often renders the work unsuitable for normal publication [17], and if such work is to gain a wider audience than at present it is an area that clearly needs urgent attention.

Since 1984, IBM have been using formal methods in the development of CICS (Customer Information Control System) [16] [?13]. It is a large transaction processing system (comprising over 800,000 lines of code) and existed before the introduction of formal development, the later [?14] being used in the production new, rather than existing, modules.

The method is based on Z and the guarded command language; much emphasis is placed on the specification phase, which is used as the vehicle for discussion between the design team and the customer (the business planning/ technical sections of the company). Once the specification is agreed it becomes a record of commitment to be fulfilled by the development team.

The refinement of the specification into code is informal and achieved in two stages: a high-level Z document is first produced stating how the design will be implemented, followed by a low-level document written in the guarded command language. The code is written directly from the latter.

Refinement takes the form of "condensing out the simple parts immediately into guarded command language, and specifying the more complicated as schemas to be refined further". Experienced programmers are used and mathematical techniques (e.g. the use of loop invariants) employed only when the specification is complex.

In general, code is produced at a point at which it is felt to be "safe", and experienced programmers are found to be indispensable. Module testing is then performed before handing over to other groups for system testing. The specification is found to be

<!-- PDF p.12 / printed p.9 -->

invaluable as a reference document at this point.

The main benefits derived from the approach are felt to be that a greater understanding of the problem is achieved, enabling the team to "get it right" at an early point in the process, increased productivity, improved documentation, and the ability of newcomers to the project to come to terms with the problem quickly. Considerable benefits have been identified in the area of specification change, arising out of greater understanding of the functionality of the application. Further, there is strong evidence to suggest that there are fewer bugs in the resulting code than those present using traditional methods.

Much effort has gone into training, with the establishment of an in-house course. It is generally found that it takes a few months for someone, initially having no formal methods training, to become proficient.

The success of the above project has led to further studies in formal development being pursued at IBM [34] [?15]. The specification and target languages are again Z and that of guarded commands, but the transition from one to the other is on a more formal basis.

Data and operational refinement are treated separately, and the correctness criteria stem from a retrieve relation, and the identification of obligations to be discharged in a similar way to the VDM method (see above).

Emphasis is placed on the tabulation of particular aspects of the development (e.g. pre-conditions of partial operations), both to minimise errors and to serve as convenient summaries. The developer is also encouraged to review informal checklists at specific stages (e.g. whether or not sufficient use has been made of pre-existing data types). The aim is to provide a standard development method that has a formal basis.

Small-scale applications have proved successful, with the benefits resulting largely paralleling those stated above and it is noted that there is a need for automated assistance and stressed that the creative role of the programmer is not removed.

A formal methods approach has successfully been adopted to develop a floating point arithmetic routine for the transputer [3] [?15]. The routines were abstractly specified in Z, and the code formally derived with proofs of correctness given to show that it met its specification.

The significance of this project is not in the scale of the application, but in its complete formality and its relation to the hardware aspect of a computer system; it augurs well for the future.

<!-- PDF p.13 / printed p.10 -->

# PART TWO — A Refinement Calculus For Z

## Contents

| | | |
|---|---|---|
| 0 | **Introduction** | 11 |
| 0.1 | A Note Regarding Presentation | 12 |
| 1 | **Data Refinement On A General Abstract State** | 12 |
| 1.1 | The Concrete-Abstract Invariant Relation | 13 |
| 1.1.1 | The "Rel" Schemas | 13 |
| 2 | **Data Refinement Of A General Abstract Operation** | 17 |
| 2.1 | The Weakest Specification Of The Concrete Operation | 18 |
| 2.2 | Reconfiguring The Concrete State | 20 |
| 3 | **Operational Refinement** | 24 |
| 3.1 | The Logical Basis | 24 |
| 3.2 | Refinement Of One Operation By Another | 25 |
| 3.3 | A Disjunction Of Operations | 28 |
| 3.4 | A Sequentially-Composed Operation | 30 |

<!-- PDF p.14 / printed p.11 -->

| | | |
|---|---|---|
| 3.5 | Refinement To Program Constructs | 33 |
| 3.5.1 | The Guarded Expression | 33 |
| 3.5.2 | The Alternative Construct | 34 |
| 3.5.3 | The Loop Construct | 36 |
| 3.5.4 | The Assignment Statement | 38 |
| 4 | **Admitting Resource Constraints Into The Refinement** | 39 |
| 4.1 | ∞-Refinement [?16] | 42 |

## 0 Introduction

We establish a set of rules and proof obligations which will enable the construction of a formal proof that a proposed implementation of an abstract specification meets (i.e. is correct with respect to) its specification. We follow the approach of [17] in separating refinement of data from that of operations.

In Section 1 we consider data refinement on an abstract state (the implementation of a concrete data type for the abstract data type of the specification). We refer to this process as the taking the "design decision" since we are designing a data structure that can be implemented in a programming language. In fact, the change from abstract to concrete data types need not be accomplished in one step, but each step may be regarded as refining to a "more" concrete type, in the sense that the new type is "nearer" to being able to be implemented in a programming language; our rules permit such a stepwise approach.

In Section 2 we consider the implications of the design decision on the refinement of individual operations of the specification, establishing a method for calculating the specification of the weakest (i.e. most general) concrete operation corresponding to an abstract operation. We also show how a reconfiguration of the concrete state may be achieved once the design decision has been taken without incurring further proof obligations.

In Section 3, we establish a set of operation refinement rules based on the pre- and post-conditions inherent in the specification. We may then either adopt a *transformational* approach to operational refinement, since each result may be regarded as a correctness-preserving transformation of the operation and may be applied (without proof) in the refinement process, or we may, using our intuition and experience, produce what we *feel* is a refinement of the operation and use the rules to prove that it is so.

<!-- PDF p.15 / printed p.12 -->

The nature of an abstract specification is such that operational considerations such as resource limitations are usually ignored, since their inclusion would detract from the clarity and conciseness of the specification. In Section 4, we show how resource constraints may be admitted into the refinement process: existing theories of refinement do not allow such activity, and we motivate the need for the inclusion of such considerations, and extend our definition of refinement, establishing the proof obligations thereby incurred.

We use the symbol "⊑" to mean "is refined by" or "can be safely replaced with" in both data and operational refinement.

### 0.1 A Note Regarding Presentation

In order to aid readability, we use the convention that vertically aligned predicates imply their logical conjunction. Thus:

```
pred1
pred2
pred3 ∨ pred4
```

will be equivalent to:

    pred1 ∧ pred2 ∧ (pred3 ∨ pred4)

and:

```
pred1
    pred2   ⇒   pred3
                pred4
    pred5
∨
    pred6
```
[?17]

will be equivalent to:

    pred1 ∧ (((pred2 ⇒ (pred3 ∧ pred4)) ∧ pred5) ∨ pred6)

## 1 Data Refinement On A General Abstract State

Data refinement involves the implementation of a concrete data type to represent an abstract data type. In this section we consider the implementation of the concrete state for the abstract state. We assume a *fully abstract* state, by which we mean that each

<!-- PDF p.16 / printed p.13 -->

abstract representation is unique in the sense that for any two states there exists a sequence of operations (defined on the abstract state) which enable the two states to be distinguished (in [17] this property is referred to as "freedom from implementation bias").

### 1.1 The Concrete-Abstract Invariant Relation

We define a general abstract state which comprises the abstract object AS⃗ [?20] (a list of abstract variable signatures) together with an invariant predicate *absinv*:

    AbsState ≙ [ AS⃗ | absinv ]

We wish to data refine *AbsState*, and we assume a design decision in which the concrete state comprises the concrete object CS⃗ ( a list of concrete vaiable signatures) together with an invariant predicate *concinv*:

    ConcState ≙ [ CS⃗ | concinv ]

We require that each concrete state has an abstract counterpart: by doing so we considerably simplify proof obligations (obviating the need for existential quantification over abstract states), and note that this requirement does not inhibit our transformation from abstract specification into code (the refinement of the specification, Part 4): since we have a fully abstract representation, each concrete state will be associated with a unique abstract state.

In general, we also require that each abstract state has at least one concrete counterpart (i.e. that the design decision is adequate): without this requirement it is possible to admit a design decision which implements only a very small part of the abstract specification (the extreme case being an empty design decision), which, clearly, will be of limited practical use and is unlikely to satisfy the specifier of the system. This requirement is, however, too strict since the use of non-determinism in the specification may explicitly allow states for which no concrete counterpart is envisaged, the specifier allowing the designer the freedom of choice as to exactly which states are provided in the implementation. Since, when using this technique, the specifier may communicate his/her wishes only by informal means, we place proof obligations on the implementor and pursue this consideration in the next section.

#### 1.1.1 The "Rel" Schemas

The invariant relationship between the abstract and concrete states may be conveniently captured in a schema which is the conjunction of the abstract and concrete states together with a predicate, *invrel*, describing the relationship between the two states:

    Rel ≙ [ AbsState ∧ ConcState | invrel ]

<!-- PDF p.17 / printed p.14 -->

We may express the requirement that each concrete state corresponds to a unique abstract state using this schema:

**Definition** [⊑ 2 : 1.1.1a]

    ∀ ConcState • ∃₁ AbsState • Rel

■

It is useful to consider two further schemas in which the direction of the relationship is recognized (i.e. abstract to concrete, or concrete to abstract): the first, *DownRel*, relates a before-abstract state to an after-concrete one, and the second, *UpRel*, relates the two states in the reverse direction:

    DownRel ≙ Rel[CS⃗′ / CS⃗]
    UpRel   ≙ Rel[AS⃗′ / AS⃗]

The concrete representation for a particular abstract state will not, in general, be unique: in fact for each abstract state the design decision will define an equivalence class of concrete configurations, which may be determined by calculating *UpRel* (relating an arbitrary concrete state - through *absinv* - with the abstract state that it represents) composed with *DownRel* (relating that abstract state back to another concrete state), and we define:

    ConcRel ≙ UpRel ⨾ DownRel

which expands to give:

```
┌─ ConcRel ─────────────────────────
│ ΔConcState
├───────────────
│ ∃ AbsState₀ •
│     Rel[AS⃗₀ / AS⃗]
│     Rel[AS⃗₀, CS⃗′ / AS⃗, CS⃗]
└───────────────────────────────────
```

from which we obtain:

```
┌─ ConcRel ─────────────────────────
│ ΔConcState
├───────────────
│ ∃ AS⃗₀ •
│     absinv[AS⃗₀ / AS⃗]
│     invrel[AS⃗₀ / AS⃗]
│     invrel[AS⃗₀, CS⃗′ / AS⃗, CS⃗]
└───────────────────────────────────
```

<!-- PDF p.18 / printed p.15 -->

If [⊑ 2 : 1.1.1a] is satisfied, the unique existence of AS⃗₀ satisfying *absinv* (the first predicate) is guaranteed, since the second predicate associates AS⃗₀ with CS⃗ through *invrel*. The final two predicates relate AS⃗₀ to both CS⃗ and CS⃗′, and their simplification will define the relation between CS⃗ and CS⃗′ and, hence, the concrete state equivalence class.

For example, if *AbsState*, *ConcState* and *Rel* are as follows [?18]:

    AbsState  ≙ [ A : seq ℕ | # A ≤ N ]
    ConcState ≙ [ C : 1 .. N → ℕ ; P : 0 .. N ]
    Rel       ≙ [ AbsState ∧ ConcState | A = C for P ]

where:

```
╔═══════════════════════════════
║ _ for _ : seq X × ℕ → seq X
╟───────
║ S for N = 1 .. N ◁ S
╚═══════════════════════════════
```

We have:

```
┌─ ConcRel ─────────────────────────
│ ΔConcState
├───────────────
│ ∃ A₀ : seq ℕ •
│     # A₀ ≤ N
│     A₀ = C for P
│     A₀ = C′ for P′
└───────────────────────────────────
```

and since we may verify that [⊑ 2 : 1.1.1a] holds, we eliminate A₀ to get:

    ConcRel ≙ [ ΔConcState | C for P = C′ for P′ ]

which defines the equivalence class (in which any two members must have equal pointers, their arrays must agree up to those pointers, but can have any natural number values after their pointers).

We may regard *ConcRel* as the weakest specification for a concrete state reorganising operation, and we pursue this in Section 2.2.

We now return to the question of adequacy, and we may calculate the subset of the abstraction that the design decision implements by considering the above composition in the reverse order: we compute *DownRel* (relating an arbitrary abstract state - through

<!-- PDF p.19 / printed p.16 -->

*absinv* - with a concrete state) composed with *UpRel* (relating that concrete state back to an abstract state), and we define:

    AbsRel ≙ DownRel ⨾ UpRel

which expands to give:

```
┌─ AbsRel ──────────────────────────
│ ΔAbsState
├───────────────
│ ∃ ConcState₀ •
│     Rel[CS⃗₀ / CS⃗]
│     Rel[AS⃗′, CS⃗₀ / AS⃗, CS⃗]
└───────────────────────────────────
```

and we obtain:

```
┌─ AbsRel ──────────────────────────
│ ΔAbsState
├───────────────
│ ∃ CS⃗₀ •
│     concinv[CS⃗₀ / CS⃗]
│     invrel[CS⃗₀ / CS⃗]
│     invrel[AS⃗′, CS⃗₀ / AS⃗, CS⃗]
└───────────────────────────────────
```

This time the second predicate indicates that CS⃗₀ will exist only for those abstract states which have been implemented by the design decision, but if CS⃗₀ does exist the final two predicates relate both AS⃗ and AS⃗′ to CS⃗₀ through *invrel*, and if [⊑ 2 : 1.1.1a] also holds (when the first predicate will be assured), AS⃗ and AS⃗′ must be the same, and so *AbsRel* is defined on a no-change state:

```
┌─ AbsRel ──────────────────────────
│ ΞAbsState
├───────────────
│ ∃ CS⃗₀ •
│     concinv[CS⃗₀ / CS⃗]
│     invrel[CS⃗₀ / CS⃗]
└───────────────────────────────────
```

Hence we may interpret *AbsRel* as representing the identity operation on the subset of the abstract state for which concrete states exist; when the predicate part of *AbsRel* is true we have an adequate design decision.

Using the above example, we have:

<!-- PDF p.20 / printed p.17 -->

```
┌─ AbsRel ──────────────────────────
│ ΞAbsState
├───────────────
│ ∃ C₀ : 1 .. N → ℕ ; P₀ : 0 .. N • A = C₀ for P₀
└───────────────────────────────────
```

the predicate part of which is true, and so *AbsRel* is equivalent to *ΞAbsState* indicating an adequate design.

When each concrete state corresponds to a unique abstract state, and each abstract state has a representation in the design, *AbsState* can be safely replaced with *ConcState*:

**Definition** [⊑ 2 : 1.1.1b]

    Rel ≙ [ AbsState ∧ ConcState | absinv ]   [?19]
    ∀ ConcState • ∃₁ AbsState • Rel
    AbsRel ≙ ΞAbsState
    ⊢
    AbsState ⊑ ConcState

■

When the first requirement is satisfied but the second is not (*AbsRel* is not equivalent to *ΞAbsState*), we require that the designer has good reason for the partial implementation before we allow the concrete state to implement the abstract; we formalise the concept of "good reason" in Section 4, giving an alternative formulation of the above lemma.

## 2 Data Refinement Of A General Abstract Operation

In this section we consider the implementation of the conrrete operation for a general abstract operation.

We first demonstrate (Section 2.1) that, once the design decision has been taken, the weakest specification of the corresponding concrete operation may be calculated; the before- and after-state of the concrete operation will correspond to the before- and after-state of the abstract operation through the *Rel* schema.

However, efficiency considerations (for example) may dictate that the operation is best effected on a particular configuration of the concrete state. We know (Section 1.1.1) that a concrete state corresponding to an abstract state will not, in general, be unique, and it is therefore possible to transform the operation such that it is defined on the required concrete configuration.
