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
