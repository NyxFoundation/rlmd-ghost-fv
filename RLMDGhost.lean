import RLMDGhost.Basic
import RLMDGhost.Model
import RLMDGhost.Protocol
import RLMDGhost.Axioms
import RLMDGhost.TrackA.Lemma1
import RLMDGhost.TrackA.Theorem1

/-!
# RLMD-GHOST — formalization root

Machine-checked formalization of *Recent Latest Message Driven GHOST*
(D'Amato & Zanolini, arXiv:2302.11326, CSF 2024). See `docs/formalization-strategy.md`
for the proof discipline (`sorry`-free; `axiom` + hypothesis threading only), the
five-track structure, and the per-statement dependency DAG.

Scaffolding modules:

* `RLMDGhost.Basic`    — slots/rounds, the block-tree prefix order, subtree weight `w`.
* `RLMDGhost.Model`    — the generalized sleepy model and `η`-compliance.
* `RLMDGhost.Protocol` — abstract propose-vote-merge / GHOST `Execution` + `Spec`.
* `RLMDGhost.Axioms`   — idealized cryptography and the Lemma 2 pivot-slot good event.

Track A (reorg-resilience backbone):

* `RLMDGhost.TrackA.Lemma1`   — view-merge: honest voters vote for the honest proposal.
* `RLMDGhost.TrackA.Theorem1` — reorg resilience by slot induction (given Proposition 1).
-/
