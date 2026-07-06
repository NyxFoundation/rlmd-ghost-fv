# rlmd-ghost-fv

Formal-verification notes and reference material for the **RLMD-GHOST**
consensus protocol.

## Source

Francesco D'Amato, Luca Zanolini —
*Recent Latest Message Driven GHOST: Balancing Dynamic Availability With
Asynchrony Resilience*

- arXiv: <https://arxiv.org/abs/2302.11326>
- IACR ePrint: <https://eprint.iacr.org/2023/279>
- Published at IEEE Computer Security Foundations Symposium (CSF) 2024
- Plain-language overview (single-slot-finality notes):
  <https://publish.obsidian.md/single-slot-finality/RLMD-GHOST>

RLMD-GHOST (Recent Latest Message Driven GHOST) is a propose-vote-merge
consensus protocol that generalizes both LMD-GHOST (`η = ∞`) and Goldfish
(`η = 1`) via a vote-expiry window `η`, trading dynamic availability against
resilience to bounded asynchrony. Results are proven in the paper's
**generalized sleepy model**.

> The source PDF is **not** committed to this repository. Download it from the
> links above and place it at `2302.11326.pdf` if you want the local copy that
> the notes reference (SHA-256
> `3e328cdccd6c4150a35f19e89942a97dbc0714226eb108ea9fa6fd7bd293f7fd`).

## Lean 4 formalization

The Lean project lives in `RLMDGhost/` (library root `RLMDGhost.lean`), built
with Lake against Mathlib (toolchain pinned in `lean-toolchain`):

```sh
lake exe cache get   # fetch the Mathlib build cache
lake build
```

Proof discipline, the barrier decisions, and the statement dependency DAG are
documented in `docs/formalization-strategy.md`. No `sorry` is ever used, and
**no axiom is declared**: every statement is proved from Lean's core axioms
alone, with external facts — the Lemma 2 pivot-slot good event
(`PivotEveryWindow`, `RLMDGhost/Axioms.lean`) and the idealized-cryptography
mechanics — threaded as explicit hypotheses. (An earlier `axiom lemma2` was
removed after being shown inconsistent; see `RLMDGhost/Axioms.lean` and
Barrier 1 of the strategy doc.)

Statement coverage — all 20 numbered statements are closed:

- **Track A** (§3.6, abstract propose-vote-merge framework): Lemma 1,
  Proposition 1, Theorems 1–2, under `RLMDGhost/ProposeVoteMerge/`; the Lemma 2
  good event is defined in `RLMDGhost/Axioms.lean` and threaded as a premise.
- **Track B** (§4, GHOST instantiations): Lemma 3 and Theorem 3, under
  `RLMDGhost/GhostInstantiations/`, on the GHOST weight layer of
  `RLMDGhost/Ghost.lean`.
- **Track C** (§5.2, RLMD-GHOST security): Lemma 4 and Theorems 6–8, under
  `RLMDGhost/Security/`, on the generalized sleepy model of
  `RLMDGhost/Model.lean` (per-slot honest/corrupted `Finset`s, the
  `η`-sleepiness and `(η, η−1)`-compliance inequalities) and the abstract
  RLMD filter interface of `RLMDGhost/Security/Basic.lean`.
- **Track D** (App. A + the §4 negative results, tightness): Theorems 4, 5, 9,
  10, 11, under `RLMDGhost/Tightness/`, on the reusable witness layer
  (`Witness.lean`/`WitnessBase.lean`): a concrete four-block tree, views as
  known-blocks × vote-tables, an operational `FIL_rlmd`, and GHOST fork choices
  proven to satisfy `GhostSelects` and the §2 consistency property. Theorem 9's
  witness is a *fully certified* RLMD-GHOST run (`Spec` + `RLMDGhostModel`),
  `τ`-compliant for every `τ < η`, reorged at slot `η + 1`; Theorem 10 draws
  the dynamic-availability consequence. Theorem 4 is a per-`τ` witness family
  for LMD-GHOST (full-history fork choice, corruption delayed past the
  `τ`-window); Theorems 5 and 11 certify their tpa witnesses at **every**
  sleepiness window simultaneously (the paper's `(∞, π)`-compliance).
- **Track E** (App. B, fast confirmations): Lemma 5 and Theorems 12–14, under
  `RLMDGhost/FastConfirmation/`. Theorem 12 composes Lemma 5 with Lemma 4
  through the shared reorg-resilience induction; Theorem 13 *proves* the safety
  of the combined κ-deep + fast rule by reduction to Theorems 12/6 and standard
  safety, and inherits liveness from Theorem 7; Theorem 14 derives full honest
  agreement from Lemma 1 at the pivot slot.
- **Phase 2** (the probabilistic content of Lemma 2): `RLMDGhost/Phase2/` —
  the product-Bernoulli proposer lottery, per-slot independence, the
  `(1 − p)^κ` per-window miss bound, the union bound over a polynomial window
  family, and negligibility of the failure probability. The identification of
  the abstract lottery with `E.pivot` of an execution is the remaining,
  documented Barrier-1 idealization.

## Contents

- `notes/paper-statements.md` — every numbered statement from the paper, each
  with its proof as it appears in the main body or appendices, plus a glossary
  of recurring notation. The paper uses flat numbering: **5 Lemmas (1–5),
  1 Proposition (1), and 14 Theorems (1–14)** — 20 items. It has **no** numbered
  Definitions, Assumptions, or Corollaries (the model is unnumbered §2 prose).
- `notes/_segments/` — the same statements split into one file per item
  (`lemma_NN`, `theorem_NN`, `proposition_NN`), each containing the statement
  text and its proof with source line references. Where a statement has no proof
  block at its location (Proposition 1; Theorem 5, whose proof precedes it;
  Theorems 6–7, which follow from Lemma 4), the segment records that explicitly.

Algorithms 1–5 (fork-choice / filter pseudocode), figures, and the prose of
§1–§5 and §6–§7 are intentionally omitted — they are protocol description and
commentary rather than statements to formalize.

## Goal

Build toward a machine-checked formalization of the RLMD-GHOST reorg-resilience,
dynamic-availability, and asynchrony-resilience results, using these extracted
statements as the specification target. The Lean 4 approach is recorded in
[`docs/formalization-strategy.md`](docs/formalization-strategy.md).
