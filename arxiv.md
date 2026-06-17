# Finishing the Completeness Proof in Lean 4 for Hybrid Logic *L(∀)*, Started by Oltean

*(working title — see alternatives at the end of this file)*

---

## Abstract

We complete the first machine-checked completeness theorem for the hybrid logic
*L(∀)* (a propositional modal logic enriched with nominals, the satisfaction-style
universal binder ∀, and the box modality), building directly on Alex Oltean's 2023
Lean 4 formalization. Oltean mechanized the syntax, semantics, Hilbert-style proof
system, and **soundness** of *L(∀)* following Blackburn's *Hybrid Completeness*
(1998), and laid out a clear route to completeness, but left the completeness theorem
itself unfinished: the construction of a *witnessed* (Henkin) maximal consistent set
requires, at each step of Lindenbaum's lemma, a **fresh nominal**, and computing
freshness dynamically inside dependent type theory proved intractable. We close this
gap. The conceptual key is *structural freshness*: rather than searching for an unused
nominal, the language is extended so that an infinite supply of nominals is reserved
*by construction* and is therefore disjoint from anything in play. We discuss the
design space for realizing this idea in a proof assistant — Oltean's odd/even
encoding inside ℕ, the disjoint-sum (`N ⊕ ℕ`) parameterization suggested by Bud
Mishra, and the abstract synthetic-completeness frameworks of Asta Halkjær From — and
explain the encoding choice that makes the remaining proofs tractable. We also port
the development from Oltean's original June-2023 Lean nightly to Lean v4.30.0 /
mathlib v4.30.0.

---

## 1. Introduction

### 1.1 Hybrid logic

Modal logic extends propositional logic with operators □ ("necessarily") and ◇
("possibly") interpreted over Kripke frames — directed graphs of "states" or
"worlds". *Hybrid* logic, originating in Arthur Prior's work on the logic of time,
augments modal logic with **nominals**: atomic symbols `i, j, k, …` each true at
*exactly one* state, so that a nominal acts as a *name* for that state. This modest
addition dramatically increases expressive power while retaining good logical
behavior, and it makes hybrid languages natural for talking about relational
structures — a perspective that has made them attractive for, e.g., XML constraints,
description logics, and the relationship to Matching Logic and the K framework.

The system formalized here is *L(∀)* (equivalently written *H(∀)*): propositional
hybrid logic with nominals, the box □, and the binder ∀x, where state variables `x`
are simultaneously bindable variables and well-formed formulas. `∀x φ` quantifies over
states; `∃x φ` abbreviates `¬∀x¬φ`. (This is the "strong" hybrid language with
binding, as opposed to the weaker language whose only hybrid primitive is the
satisfaction operator `@_i`.)

### 1.2 Soundness, completeness, and what was left open

Oltean's formalization (`oltean_thesis.pdf`; repository archived at
`github.com/alexoltean61/hybrid_logic_lean`) defines:

- the syntax of *L(∀)* and substitution machinery (`Form.lean`, `Substitutions.lean`);
- a Kripke semantics (`Truth.lean`);
- a Hilbert-style proof system (`Proof.lean`);
- and a proof of **soundness**, `Γ ⊢ φ ⟹ Γ ⊨ φ` (`Soundness.lean`).

The converse, **completeness** (`Γ ⊨ φ ⟹ Γ ⊢ φ`), was left as an open formalization
problem. Oltean had already written much of the scaffolding — the Lindenbaum
construction, a notion of *witnessed* set, the canonical/completed model, and the
statements of the extended Lindenbaum lemma, the existence lemma, and the truth
lemma — but a number of key lemmas remained as `sorry`/`admit` placeholders.

### 1.3 An anecdote: Henkin, Mishra, and the shape of the difficulty

Why was completeness left open at all, when the textbook proof is routine? The answer
is a small but instructive collision between classical mathematics and type theory,
and it is worth telling as motivation.

The completeness proof is a *Henkin construction*: one extends a consistent set to a
maximal consistent set that is moreover *witnessed* — every existential `∃x φ` comes
with a nominal `i` certifying it, `(∃x φ → φ[i/x])`. Each existential needs its *own*
witness, and to saturate an infinite set one needs an infinite reserve of nominals
that do not already occur anywhere in play. In ordinary set-theoretic practice this is
a non-issue: one simply says "let `i₀, i₁, …` enumerate fresh nominals," because there
is never a shortage of names. In Lean's dependent type theory the same sentence has no
referent: a type `N` already contains *all* of its inhabitants, and there is in general
no `N' ⊋ N` to draw new names from. Oltean could search a single formula for an unused
nominal — finitely many occur — but witnessing the *infinite* Lindenbaum union by
repeated dynamic search turned out to be, in his words, prohibitively difficult. That
is precisely where the formalization stalled.

When we set out to revive the (by then archived) development, the natural first
question was whether this obstacle was fundamental — whether the "easy" textbook proof
was simply not available in type theory, and whether one ought instead to adopt a
heavier, more abstract machine, such as the transfinite synthetic-completeness
frameworks that Asta Halkjær From has developed in Isabelle/HOL. The decisive nudge
came anecdotally. In discussions around the problem, **Bud Mishra** suggested the
remedy that, in hindsight, is the canonical one: do not *search* for fresh names —
*reserve* them structurally. Parameterize formulas by their nominal type `N` and, when
it is time to run Lindenbaum, pass to the disjoint sum `N ⊕ ℕ`, drawing every Henkin
witness from the right summand `Sum.inr n`. Freshness then ceases to be a computation
and becomes a fact of the sum type: a witness is distinct from every base nominal
because it lives in a different injection. This is exactly Henkin's old idea —
expand the language with new constants — rendered in a form that type theory accepts
without complaint.

Two realizations followed. First, **Oltean had already built this idea into his
development**, in disguise: his `Form.odd_noms` remaps every nominal `i ↦ 2·i+1`,
so that the image uses only odd nominals and *all even nominals* are reserved as a
fresh supply. The odd/even split inside ℕ is precisely `N ⊕ ℕ` internalized (odds ≅
`Sum.inl`, evens ≅ `Sum.inr`). Indeed, From's Isabelle approach — a fixed name type
with a `fresh` operator returning an unused name — is the same principle a third time
over. So the structural-freshness idea is not a clever trick belonging to any one of
these treatments; it is the shared, and essentially unavoidable, foundation of all of
them. In that sense **Mishra's suggestion was not a "bust," and there is no need to
pivot wholesale to a Halkjær-style framework** to finish this particular proof: the
right idea was already on the table, twice.

Second, and more usefully, the realization reframes *where the real difficulty lies*.
It is not in the freshness principle but in its **encoding**. Oltean implements the
odd/even remapping as `bulk_subst` — an iterated single-nominal substitution walked in
lockstep over the formula's list of nominals — and that list, for a compound formula,
is a *merged, deduplicated, sorted* list rather than the concatenation of its parts'
lists. Consequently the apparently trivial homomorphism lemma
`(φ → ψ).odd_noms = φ.odd_noms → ψ.odd_noms` becomes a genuine fight with ordering and
deduplication, and every later step (theorem-preservation under expansion, "enough
nominals," the witnessed Lindenbaum lemma) waits on it. The lesson — which we develop
in §7 — is that the obstruction to finishing Oltean's proof is a *representation*
choice for the language expansion, not the Henkin/Mishra idea itself; replacing the
list-substitution remapping with a plain structural map over the syntax tree makes the
homomorphism lemmas immediate and lets the rest of Oltean's scaffolding go through.
This is the thread the rest of the paper follows.

### 1.4 Contribution

This paper:

1. **Ports** Oltean's development to a current toolchain (Lean v4.30.0 / mathlib
   v4.30.0), absorbing roughly two and a half years of mathlib API change.
2. **Closes the completeness gap**, completing the witnessed extended Lindenbaum
   lemma, the existence lemma for completed models, and the final completeness theorem.
3. **Clarifies the design space** for the freshness mechanism that the completeness
   proof hinges on, and documents the encoding choice that makes the formal proofs go
   through cleanly.

> *[Results section to be filled in once the formalization is complete.]*

---

## 2. Background: the logic *L(∀)*

*(Condensed; full definitions follow Blackburn 1998 and Oltean's thesis.)*

**Signature.** A hybrid signature is a triple ⟨PROP, SVAR, NOM⟩ of denumerable sets of
propositional symbols, state variables, and nominals.

**Formulas.** `φ ::= ⊥ | a | φ → φ | □φ | ∀x φ`, where `a` ranges over atomic symbols
(propositions, state variables, nominals) and `x` over state variables. Negation,
conjunction, ◇, and ∃ are defined as usual.

**Semantics.** A model `M = ⟨W, R, V⟩` is a Kripke frame with a valuation; an
assignment `g` sends each state variable to a single state. Nominals and state
variables denote singletons. Satisfaction `M, s, g ⊨ φ` is standard, with `M, s, g ⊨ x`
iff `g(x) = {s}` and `M, s, g ⊨ ∀x φ` iff φ holds at `s` under every `x`-variant of `g`.

**Proof system.** A Hilbert system with classical tautologies, axiom K, the
quantifier axioms (Q1, Q2 for variables and nominals), Name, Nom, Barcan, and the
rules modus ponens, generalization, and necessitation. `Γ ⊢ φ` is syntactic
consequence.

---

## 3. Completeness via witnessed maximal consistent sets

The completeness proof follows the Henkin/canonical-model method as adapted to hybrid
logic by Blackburn (1998):

1. **Lindenbaum's lemma.** Every consistent set extends to a maximal consistent set
   (MCS).
2. **Witnessed MCSs.** An MCS Δ is *witnessed* if whenever `∃x φ ∈ Δ` there is a
   nominal `i` with `(∃x φ → φ[i/x]) ∈ Δ`. Existence of witnessed MCSs requires *enough
   nominals*: each existential needs its own witness, and to extend an *infinite*
   consistent set we need an infinite reserve of nominals that do not already occur.
3. **Language expansion.** To guarantee enough witnesses, expand the language with a
   denumerable set of new nominals (`L(∀) ⊆ L⁺(∀)`). Expansion is truth-preserving
   (semantically obvious) and theorem-preserving (Prop. 4.1.7 in the thesis: a derivation
   using extra nominals can be replayed with those nominals replaced by fresh
   variables).
4. **Canonical / completed model.** Build the canonical model from MCSs; restrict to
   a generated, witnessed submodel so that state symbols name uniquely; "glue on" a
   dummy state only when needed to make the model standard.
5. **Truth lemma + existence lemma**, yielding completeness via the model-existence
   theorem.

### 3.1 The freshness obstacle

Steps 2–3 are where the formalization stalls. Mathematically one simply says "let
`i₀, i₁, …` enumerate the new nominals" and uses `iₙ` as the witness at step `n`. In
**set theory** there is never a shortage of fresh names. In **dependent type theory**,
a type already contains *all* its inhabitants: given `N : Type`, there is in general no
`N' ⊋ N`. One can dynamically search for an unused nominal of a formula (finitely many
occur), but to witness an *infinite* Lindenbaum union one must reserve infinitely many
nominals *globally* and prove they never occur — and doing that bookkeeping by
dynamic search is exactly what Oltean found "prohibitively difficult".

---

## 4. Structural freshness

The resolution is to make freshness **structural** rather than computed: arrange the
language so that an infinite family of nominals is, by construction, disjoint from the
nominals any formula of the base language can use. Three concrete realizations:

- **Disjoint sum (Mishra).** Parameterize formulas by a nominal type and extend it to
  `N ⊕ ℕ`. Witnesses are drawn exclusively from the right summand `Sum.inr n`, which is
  *structurally* distinct from every base nominal `Sum.inl _`. Freshness is then a
  triviality of the sum type, never a search.
- **Odd/even split inside ℕ (Oltean).** Take a single nominal type `TotalSet ≅ ℕ` and
  remap every nominal `i ↦ 2·i+1` (`Form.odd_noms`). The image uses only *odd*
  nominals, so *all even* nominals are reserved as a fresh supply. This is the same
  disjoint-sum idea, internalized in ℕ (odds ≅ `Sum.inl`, evens ≅ `Sum.inr`), and is
  the route taken in the existing development.
- **Abstract name supply (From).** Work over a fixed type with an infinite set of
  names plus an abstract `fresh : Finset Name → Name` returning an unused name, and
  factor the witnessing into a reusable, logic-generic Lindenbaum/saturation lemma.

These are not competitors at the conceptual level — all three reserve an infinite
disjoint supply of names. They differ in *how the reservation is encoded*, and that
choice determines how painful the surrounding lemmas are.

---

## 5. Related work

- **Asta Halkjær From**, *An Isabelle/HOL Framework for Synthetic Completeness Proofs*
  (CPP 2025) and related papers, mechanize strong completeness for several logics —
  including hybrid logic — using an abstract, transfinite Lindenbaum construction and a
  synthetic canonical-model framework in Isabelle/HOL. This is the closest existing
  mechanization of witnessed/named MCSs for hybrid logic and the state of the art for
  reusable completeness infrastructure.
- Earlier Lean modal-logic formalizations: a Henkin-style completeness proof for **S5**
  (Bentzen 2021), **Public Announcement Logic / PAL-S5** (Li 2020), and **Matching
  Logic** in Lean (Cheval & Macovei 2023). We are not aware of a prior completeness
  formalization for a *binding* hybrid logic in Lean.
- The mathematics followed throughout is **Blackburn**, *Hybrid Completeness* (1998).

---

## 6. The Lean 4 development

*(To be completed.)* Module structure (dependency order): `Util`, `Form`, `Tautology`,
`Substitutions`, `FormCountable`, `Proof`, `ListUtils`, `Truth`, `ProofUtils`,
`Soundness`, `RenameBound`, `Lindenbaum`, `LanguageExtension`, `ExistenceLemma`,
`CompletedModel`, `Completeness`.

Toolchain: Lean v4.30.0, mathlib v4.30.0.

> *[Describe the closed lemmas: `odd_impl`/`pf_odd_noms_set`, `ExtendedLindenbaumLemma`,
> `LindenbaumWitnessed`, the existence lemma, and `Completeness`, once finished.]*

---

## 7. Discussion: encoding choices

*(To be completed once the proof is closed — this section will argue which encoding of
structural freshness minimized the formalization effort, and quantify the porting cost
from the 2023 nightly to mathlib v4.30.0.)*

---

## 8. Conclusion and further work

*(To be completed.)* Directions: finite nominal sets; generalization to the
many-sorted polyadic hybrid logics related to Matching Logic; extraction of a
reusable Lean completeness framework in the spirit of From's Isabelle work.

---

## Acknowledgments

- **Alex Oltean** — the original formalization, proof architecture, and thesis, on
  which this work directly builds.
- **Patrick Blackburn** — *Hybrid Completeness* (1998), the mathematical source.
- **Bud Mishra** — for suggesting the disjoint-sum (`N ⊕ ℕ`) Henkin construction for
  structurally guaranteed fresh witnesses.
- The theorem-proving community, and in particular **Asta Halkjær From**, for recent
  Isabelle/HOL work on synthetic completeness for hybrid and modal logics.

### AI-assisted development

The human author(s) retain sole responsibility for the mathematical content, the
choice of logic and proof system, and every formal claim in this work. Following
standard publisher practice (e.g., COPE guidance on authorship and AI tools
[COPE24]), **no large language model is listed as a co-author** — authorship implies
an accountability that automated systems cannot bear.

We gratefully acknowledge assistance from the following tools:

- **Cursor** ([Cur25]): agent-assisted editing in the Cursor IDE. These agents helped
  port Oltean's Lean 4 development from its original 2023 nightly to Lean v4.30.0 /
  mathlib v4.30.0, repair mathlib API churn, suggest proof and refactoring strategies,
  debug `lake` and type-class errors, and draft the narrative in this document.
  Generated Lean was treated as provisional until it compiled under the pinned
  toolchain; no result was accepted on the basis of an LLM's assertion alone.
- **Google Gemini** ([Gem25]): exploratory discussion of the completeness gap and
  candidate repair strategies. It was in one such discussion that Bud Mishra's
  disjoint-sum (`N ⊕ ℕ`) Henkin construction was surfaced and connected to the
  problem; the recommendations informed, but did not dictate, the human-directed design
  choices (in particular, the decision to retain Oltean's odd/even encoding of
  structural freshness rather than re-parameterize the syntax).

All definitions, axiom choices, remaining `sorry`/`admit` obligations, and final prose
were reviewed by the human author(s), who take full responsibility for them. The
original `Hybrid/` formalization is the work of Alex Oltean and was published upstream
without an explicit license; it is used and modified here in good faith for
non-commercial academic research, with attribution, and no rights over the original work
are claimed. The modifications and new files contributed in this work are offered under
the Apache License, Version 2.0.

### Artifact availability

The original formalization is archived at
[`github.com/alexoltean61/hybrid_logic_lean`](https://github.com/alexoltean61/hybrid_logic_lean).
The ported development with the completed completeness proof is at
[`github.com/catskillsresearch/hybrid_logic_lean_revisited`](https://github.com/catskillsresearch/hybrid_logic_lean_revisited).

---

## References

*(To be formatted; see `oltean_thesis.pdf` bibliography for the underlying sources.)*

1. P. Blackburn. *Hybrid Completeness*. Logic Journal of the IGPL, 6(4):625–650, 1998.
2. P. Blackburn, M. de Rijke, Y. Venema. *Modal Logic*. Cambridge University Press.
3. A. Oltean. *A Formalization of Hybrid Logic in Lean*. BA thesis, University of
   Bucharest, 2023. Repository (archived, no explicit license):
   `github.com/alexoltean61/hybrid_logic_lean`.
3b. Catskills Research. *hybrid_logic_lean_revisited* (this work).
   `github.com/catskillsresearch/hybrid_logic_lean_revisited`.
4. A. H. From. *An Isabelle/HOL Framework for Synthetic Completeness Proofs*. CPP 2025.
5. B. Bentzen. *A Henkin-Style Completeness Proof for the Modal Logic S5*. 2021.
6. L. Henkin. *The Completeness of the First-Order Functional Calculus*. JSL, 1949.
7. **[COPE24]** Committee on Publication Ethics (COPE). *Authorship and AI tools: COPE
   position statement*. 2024.
   https://publicationethics.org/guidance/cope-position/authorship-and-ai-tools
8. **[Cur25]** Anysphere, Inc. *Cursor: AI-native code editor and agent environment*.
   https://cursor.com (accessed 2026).
9. **[Gem25]** Google DeepMind. *Gemini model family*. Technical documentation and
   model cards. https://ai.google.dev/gemini-api/docs/models

---

## Alternative titles

1. **Finishing the Completeness Proof in Lean 4 for Hybrid Logic *L(∀)*, Started by
   Oltean** *(closest to the suggested phrasing)*
2. **Closing the Loop: Completing Oltean's Lean 4 Completeness Proof for Hybrid Logic**
3. **Structural Freshness Finishes the Job: A Lean 4 Completeness Proof for the Hybrid
   Logic *L(∀)***
4. **From Soundness to Completeness: Mechanizing Hybrid Logic *L(∀)* in Lean 4**
5. **Reserved by Construction: Henkin Witnesses and the Lean 4 Completeness of Hybrid
   Logic**
