import RLMDGhost.Protocol

/-!
# Lemma 1 — view-merge: honest voters vote for the honest proposal in a pivot slot

> **Lemma 1** (arXiv:2302.11326). Suppose that `t` is a pivot slot. Then, all
> honest voters of slot `t`, i.e., `H_t`, vote for the honest proposal `B` of
> slot `t`.

The paper's proof, step by step against the `Spec` fields:

1. The honest proposer `v_p` proposes `B` extending `FC(V_p, t)`
   (`proposal_extends`), so `FC(V_p ∪ {B}, t) = B` by the consistency property
   of `FC` (`fc_consistency`).
2. An honest voter `v_i ∈ H_t` was already active at round `3∆(t−1) − 2∆`
   (else it would still be in the joining protocol), so its pre-merge view `V_i`
   at round `3∆t + ∆` was delivered to the proposer by round `3∆t`: `V_i ⊆ V_p`
   (`voter_view_le`).
3. `v_i` merges the proposed view: `V_i ∪ (V_p ∪ {B}) = V_p ∪ {B}` (absorption,
   `sup_eq_right`), and its fork choice on the merged view is its canonical
   chain at the voting round (`chAt_pivot_merge`), which is therefore `B`.
4. `v_i` votes for that fork-choice output (`vote_chAt`), i.e., for `B`.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  {E : Execution Block Validator View}

/-- The canonical-chain form of Lemma 1: in a pivot slot `t`, the canonical
chain of every honest voter at the voting round `3∆t + ∆` is exactly the honest
proposal `B`. This is the form the base case of Theorem 1 consumes. -/
theorem lemma1_canonical (S : Spec E) {v : Validator} {t : Slot}
    (hpivot : E.pivot t) (hv : E.voter v t) :
    E.chAt v (E.voteRound t) = E.proposal t := by
  have hmerge : E.view v (E.voteRound t) ⊔ E.proposedView t = E.proposedView t :=
    sup_eq_right.mpr ((S.voter_view_le hpivot hv).trans le_sup_left)
  have hfc : E.FC (E.proposedView t) t = E.proposal t :=
    S.fc_consistency (E.proposerView t) t (E.proposal t) (S.proposal_extends hpivot)
  rw [S.chAt_pivot_merge hpivot hv, hmerge, hfc]

/-- **Lemma 1.** In a pivot slot `t`, every honest voter of slot `t` votes for
the honest proposal of slot `t`. -/
theorem lemma1 (S : Spec E) {v : Validator} {t : Slot}
    (hpivot : E.pivot t) (hv : E.voter v t) :
    E.votesFor v t (E.proposal t) :=
  lemma1_canonical S hpivot hv ▸ S.vote_chAt hv

end RLMDGhost
