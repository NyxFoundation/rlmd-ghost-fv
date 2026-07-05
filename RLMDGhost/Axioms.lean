import RLMDGhost.Protocol

/-!
# RLMD-GHOST — declared axioms

Per the proof discipline of `docs/formalization-strategy.md`, facts are never
`sorry`ed; the only unproven mechanisms are explicit `axiom`s and hypothesis
threading. This file declares the single Barrier-1 axiom:

* **Lemma 2** (pivot-slot good event) — the sole probabilistic statement of the
  paper. It holds *with overwhelming probability* via the fairness of the
  proposer-selection lottery and a union bound over the polynomial time horizon
  (paper, proof of Lemma 2). It is declared as an axiom so the deterministic
  dependents (Theorem 2, and later Track C/E results) can thread the good event
  `PivotEveryWindow` as a hypothesis. The measure-theoretic proof replacing the
  axiom is Phase 2, tracked by issue #21, and never blocks dependents.

The Barrier-2 idealized-cryptography axioms (`SignatureUnforgeable`,
proposer-lottery consistency/uniqueness) are stated over the equivocation
vocabulary of the RLMD filter family, which enters with Track C (Lemma 4); they
are declared alongside that vocabulary rather than as unusable stubs here.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]

/-- **Pivot-slot good event** (conclusion of Lemma 2): every slot interval of
length `κ` contains at least one pivot slot. -/
def PivotEveryWindow (E : Execution Block Validator View) (κ : ℕ) : Prop :=
  ∀ t : Slot, ∃ s : Slot, t ≤ s ∧ s < t + κ ∧ E.pivot s

/-- **Lemma 2** (arXiv:2302.11326). *With overwhelming probability, all slot
intervals of length `κ` contain at least a pivot slot.*

The fairness premise renders "the proposer of slot `t` is active at round `3∆t`
with probability `h_{3∆t}/n ≥ h₀/n > 0`": at every proposing round some honest
validator is active (`h_{3∆t} > 0`). Given fairness, a `(1 − h₀/n)^κ` bound per
window and a union bound over the `poly(κ)` horizon make the failure probability
negligible; the good event is declared to hold outright (Barrier 1, Phase 1).
Replaced by a measure-theoretic proof in Phase 2 (issue #21). -/
axiom lemma2 (E : Execution Block Validator View) {κ : ℕ} (hκ : 0 < κ)
    (hfair : ∀ t : Slot, ∃ v : Validator, E.active v (E.slotStart t)) :
    PivotEveryWindow E κ

end RLMDGhost
