import RLMDGhost.Protocol

/-!
# RLMD-GHOST — the Lemma 2 good event

Per the proof discipline of `docs/formalization-strategy.md`, facts are never
`sorry`ed; the only unproven mechanisms are explicit `axiom`s and hypothesis
threading. This file defines the **Lemma 2 good event** `PivotEveryWindow`,
which every dependent (Theorem 2, Theorem 7, Theorem 13) takes as an explicit
hypothesis.

**Why there is no `axiom lemma2`.** An earlier revision declared an axiom
`lemma2 (E : Execution Block Validator View) (hκ : 0 < κ) (hfair : ∀ t, ∃ v,
E.active v (E.slotStart t)) : PivotEveryWindow E κ`. That axiom is
*inconsistent*: `Execution.pivot` is an unconstrained field, not
tied to `active` or to any proposer lottery, so the axiom can be instantiated
at an execution with `pivot := fun t => t = 2` and `active := fun _ _ => True`
(e.g. the Track D witnesses), from which `False` is derivable. More
fundamentally, the paper's Lemma 2 is a *probabilistic* statement — the good
event holds with overwhelming probability over the proposer lottery, within a
polynomial time horizon — and no sound deterministic axiom over bare
`Execution`s can express it: a deterministic execution in which no honest
proposer is ever drawn is a measure-zero but definable object.

Lemma 2's content therefore lives in two sound places:

* **Hypothesis threading** — deterministic dependents take the good event
  `PivotEveryWindow E κ` as a premise and are fully proved ("good event ⇒
  security"). This matches the paper, whose security statements hold "with
  overwhelming probability" *because* they hold on the good event.
* **`RLMDGhost.Phase2`** — the probabilistic content of the paper's proof of
  Lemma 2, formalized over an abstract product-Bernoulli proposer lottery:
  per-slot independence (`lot_indep`), the per-window miss probability
  `(1 − p) ^ κ` (`lot_window`), the union bound over a window family
  (`lot_union_bound`), and negligibility of the failure probability under a
  polynomial horizon (`pivotEveryWindow_fail_negligible`,
  `pivotEveryWindow_failure_negligible`). The remaining idealization —
  identifying the abstract lottery coordinates with `E.pivot` of a protocol
  execution, i.e. giving executions probabilistic semantics — is the
  documented Barrier-1 boundary; it is *not* closed by an axiom.

The Barrier-2 idealized-cryptography assumptions (signature unforgeability,
proposer-lottery consistency/uniqueness) are likewise threaded as interface
hypotheses where the equivocation vocabulary exists: `honest_vote_counted` in
`RLMDGhost.Security.Basic` is their interface form (`E ⊆ H_{t−1} ∩ A_t`).
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]

/-- **Pivot-slot good event** (conclusion of Lemma 2): every slot interval of
length `κ` contains at least one pivot slot.

This is the paper's good event over an unbounded slot range; the paper works
within a time horizon `Thor = poly(κ)`, over which the event holds w.o.p.
(union bound, `RLMDGhost.Phase2`). Dependents thread this proposition as a
hypothesis, so their statements are the deterministic "good event ⇒ security"
conditionals. -/
def PivotEveryWindow (E : Execution Block Validator View) (κ : ℕ) : Prop :=
  ∀ t : Slot, ∃ s : Slot, t ≤ s ∧ s < t + κ ∧ E.pivot s

end RLMDGhost
