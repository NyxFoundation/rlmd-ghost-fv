import RLMDGhost.Basic
import RLMDGhost.Protocol
import RLMDGhost.Axioms
import RLMDGhost.Ledger
import RLMDGhost.ProposeVoteMerge.Lemma1
import RLMDGhost.ProposeVoteMerge.Proposition1
import RLMDGhost.ProposeVoteMerge.Theorem1
import RLMDGhost.ProposeVoteMerge.Theorem2

/-!
# RLMD-GHOST — Lean 4 formalization

Formalization of the numbered statements of *Recent Latest Message Driven
GHOST* (D'Amato & Zanolini, arXiv:2302.11326, CSF 2024), following
`docs/formalization-strategy.md`.

Track A (§3.6, the abstract propose-vote-merge framework): Lemma 1,
Lemma 2 (axiom, Barrier 1), Proposition 1, Theorem 1, Theorem 2.
-/
