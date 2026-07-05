import RLMDGhost.Security.Lemma4
import RLMDGhost.ProposeVoteMerge.Theorem1

/-!
# Theorem 6 — RLMD-GHOST is `η`-reorg-resilient

> **Theorem 6** (Reorg resilience, arXiv:2302.11326). RLMD-GHOST is
> `η`-reorg-resilient.

The paper gives no separate proof: since Proposition 1 holds for RLMD-GHOST in
`η`-compliant executions (Lemma 4), Theorem 1 applies. Accordingly the Lean
proof is the composition `theorem1 ∘ lemma4`, with `η`-compliance threaded as
the `η`-sleepiness hypothesis plus the `Spec`/`RLMDGhostModel` mechanics. By
the hierarchy of sleepy models the result also holds for `τ ≥ η` (a
`τ`-sleepy environment for `τ ≥ η` is in particular `η`-sleepy). -/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η : ℕ}

/-- **Theorem 6 (Reorg resilience).** In an `η`-compliant execution,
RLMD-GHOST satisfies reorg resilience: every pivot-slot proposal stays
canonical at every later fork-choice round. -/
theorem theorem6 (S : Spec E) (R : RLMDGhostModel E SM η)
    (hsleepy : SM.EtaSleepy η) : ReorgResilient E :=
  theorem1 S (lemma4 S R hsleepy)

end RLMDGhost
