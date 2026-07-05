import RLMDGhost.FastConfirmation.Lemma5
import RLMDGhost.Security.Lemma4

/-!
# Theorem 12 — reorg resilience of fast confirmations

> **Theorem 12** (Reorg resilience of fast confirmations, arXiv:2302.11326).
> Consider an `η`-compliant execution of RLMD-GHOST. A block fast confirmed by
> an honest validator at a slot `t` after GST is always in the canonical chain
> of all active validators at rounds `≥ 3∆(t + 1) + ∆`.

The paper's proof "follows that of Theorem 1, using Lemma 5 instead of Lemma 1
as the base case; Proposition 1 (Lemma 4 for `η`-compliant RLMD-GHOST) is still
used for the inductive step." Accordingly the Lean proof feeds Lemma 5's
conclusion — all honest voters of slot `t + 1` vote for descendants of `B` —
into the shared `Persistence.canonical_from_base`, with `Persistence` supplied
by Lemma 4. The base slot is `t₀ = t + 1`, so canonicity holds at every
fork-choice round from `3∆(t + 1) + ∆` on.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η n₃ : ℕ}

/-- **Theorem 12 (Reorg resilience of fast confirmations).** In an `η`-compliant
execution, a block `B` fast confirmed by an honest validator at slot `t` is in
the canonical chain of every honest active validator at both fork-choice rounds
of every slot `≥ t + 1`. -/
theorem theorem12 (S : Spec E) (R : FastConfirmModel E SM η n₃)
    (hsleepy : SM.EtaSleepy η)
    {vc : Validator} {t : Slot} {B : Block} (hfc : R.fastConfirms vc t B) :
    (∀ s : Slot, t + 1 ≤ s → ∀ v : Validator, E.active v (E.voteRound s) →
      B ≤ E.chAt v (E.voteRound s)) ∧
    (∀ s : Slot, t + 1 < s → ∀ v : Validator, E.active v (E.slotStart s) →
      B ≤ E.chAt v (E.slotStart s)) :=
  Persistence.canonical_from_base (lemma4 S R.toRLMDGhostModel hsleepy) S (lemma5 S R hfc)

end RLMDGhost
