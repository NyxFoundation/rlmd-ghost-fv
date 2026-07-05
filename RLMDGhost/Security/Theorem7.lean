import RLMDGhost.Security.Theorem6
import RLMDGhost.ProposeVoteMerge.Theorem2

/-!
# Theorem 7 — RLMD-GHOST is `η`-dynamically-available

> **Theorem 7** (Dynamic availability, arXiv:2302.11326). RLMD-GHOST is
> `η`-dynamically-available.

The paper gives no separate proof: Lemma 4 discharges Proposition 1, so
Theorem 2 applies — reorg resilience (Theorem 6) plus the pivot-slot good event
of Lemma 2 give security with `Tconf = 2κ`. Accordingly the Lean proof is the
composition `theorem2 ∘ theorem6`, with the good event threaded as
`PivotEveryWindow` per the proof discipline (Theorem 7 itself does not depend
on the Lemma 2 axiom). -/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η : ℕ}

/-- **Theorem 7 (Dynamic availability).** In an `η`-compliant execution, given
the pivot-slot good event of Lemma 2, RLMD-GHOST is secure with
`Tconf = 2κ` slots for every confirmed-ledger assignment at depth `κ` with a
transaction model. -/
theorem theorem7 (S : Spec E) (R : RLMDGhostModel E SM η)
    (hsleepy : SM.EtaSleepy η) {κ : ℕ} (L : Ledger E κ) (TX : TxModel E)
    (hwin : PivotEveryWindow E κ) :
    L.Safe ∧ TX.Live L (2 * κ) :=
  theorem2 L TX hwin (theorem6 S R hsleepy)

end RLMDGhost
