import RLMDGhost.Basic
import RLMDGhost.Protocol
import RLMDGhost.Axioms
import RLMDGhost.Ledger
import RLMDGhost.Ghost
import RLMDGhost.ProposeVoteMerge.Lemma1
import RLMDGhost.ProposeVoteMerge.Proposition1
import RLMDGhost.ProposeVoteMerge.Theorem1
import RLMDGhost.ProposeVoteMerge.Theorem2
import RLMDGhost.GhostInstantiations.Lemma3
import RLMDGhost.GhostInstantiations.Theorem3
import RLMDGhost.Model
import RLMDGhost.Security.Basic
import RLMDGhost.Security.Lemma4
import RLMDGhost.Security.Theorem6
import RLMDGhost.Security.Theorem7
import RLMDGhost.Security.Theorem8
import RLMDGhost.Tightness.Witness
import RLMDGhost.Tightness.Theorem9Core
import RLMDGhost.Tightness.Theorem9Regimes
import RLMDGhost.Tightness.WitnessBase
import RLMDGhost.Tightness.Theorem9Close
import RLMDGhost.Tightness.Theorem11
import RLMDGhost.FastConfirmation.Basic
import RLMDGhost.FastConfirmation.Lemma5
import RLMDGhost.FastConfirmation.Theorem12
import RLMDGhost.FastConfirmation.Theorem13
import RLMDGhost.FastConfirmation.Theorem14

/-!
# RLMD-GHOST — Lean 4 formalization

Formalization of the numbered statements of *Recent Latest Message Driven
GHOST* (D'Amato & Zanolini, arXiv:2302.11326, CSF 2024), following
`docs/formalization-strategy.md`.

Track A (§3.6, the abstract propose-vote-merge framework): Lemma 1,
Lemma 2 (axiom, Barrier 1), Proposition 1, Theorem 1, Theorem 2.
-/
