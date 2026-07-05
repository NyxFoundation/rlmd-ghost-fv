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
documented in `docs/formalization-strategy.md`. No `sorry` is ever used; the
only declared axiom is the probabilistic pivot-slot fact of Lemma 2
(`RLMDGhost/Axioms.lean`, Barrier 1), threaded as a hypothesis into its
dependents.

Statement coverage so far:

- **Track A** (§3.6, abstract propose-vote-merge framework): Lemma 1, Lemma 2
  (axiom), Proposition 1, Theorems 1–2, under `RLMDGhost/ProposeVoteMerge/`.
- **Track B** (§4, GHOST instantiations): Lemma 3 and Theorem 3, under
  `RLMDGhost/GhostInstantiations/`, on the GHOST weight layer of
  `RLMDGhost/Ghost.lean`. The negative results (Theorems 4–5) additionally
  need concrete adversarial executions instantiating the interfaces.
- **Track D** (App. A, tightness) — *in progress.* The reusable witness layer
  (`RLMDGhost/Tightness/Witness.lean`) is complete: a concrete four-block tree,
  views as known-blocks × vote-tables, an operational `FIL_rlmd`, and a GHOST
  fork choice proven to satisfy `GhostSelects`, the §2 consistency property,
  and the `RLMDGhostBase` counting bookkeeping. The three impossibility
  theorems (9–11) instantiate this layer with the paper's adversarial
  schedules — that construction work is ongoing.
- **Track C** (§5.2, RLMD-GHOST security): Lemma 4 and Theorems 6–8, under
  `RLMDGhost/Security/`, on the generalized sleepy model of
  `RLMDGhost/Model.lean` (per-slot honest/corrupted `Finset`s, the
  `η`-sleepiness and `(η, η−1)`-compliance inequalities) and the abstract
  RLMD filter interface of `RLMDGhost/Security/Basic.lean`.

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
