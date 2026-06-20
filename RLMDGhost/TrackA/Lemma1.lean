import RLMDGhost.Protocol

/-!
# Lemma 1 — view-merge: honest voters vote for the honest proposal

> **Lemma 1** (arXiv:2302.11326). Suppose that `t` is a pivot slot. Then all
> honest voters of slot `t`, i.e. `H_t`, vote for the honest proposal `B` of
> slot `t`.

The paper's proof is the view-merge argument: the honest proposer `vp` proposes
`B` extending its own fork choice, so by the consistency of `FC` we have
`FC(V_p ∪ {B}, t) = B`; every honest voter merges `vp`'s proposed view before
voting, so its own vote-round fork choice is also `B`, and the voting rule makes
it vote for `B`. Those two mechanics are the `Spec` fields `pivot_forkChoice`
(view-merge + fork-choice consistency) and `vote_forkChoice` (the voting rule);
Lemma 1 composes them, so it is *fully proved* — no `sorry`, no axiom.
-/

namespace RLMDGhost

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Lemma 1.** At a pivot slot `t` with active honest eligible proposer `vp`,
every honest voter of slot `t` votes for `vp`'s proposal. -/
theorem lemma1 (S : Spec E) {vp : Validator} {t : Slot}
    (hprop : E.eligiblePropose vp t) (hhon : E.honestAt vp (E.slotStart t)) :
    ∀ id : Validator, E.honestVoter id t → E.votesFor id t (E.proposalBlock vp t) := by
  intro id hid
  obtain ⟨hah, helig⟩ := hid
  have hfc := S.pivot_forkChoice hprop hhon hah helig
  have hvote := S.vote_forkChoice hah helig
  rwa [hfc] at hvote

/-- Honest voters of a pivot slot vote for a *descendant* of the proposal — the
form consumed by the reorg-resilience induction (Theorem 1). -/
theorem lemma1_votesForDescendant (S : Spec E) {vp : Validator} {t : Slot}
    (hprop : E.eligiblePropose vp t) (hhon : E.honestAt vp (E.slotStart t)) :
    ∀ id : Validator, E.honestVoter id t →
      E.votesForDescendant id t (E.proposalBlock vp t) := by
  intro id hid
  exact E.votesForDescendant_of_votesFor (lemma1 S hprop hhon id hid)

end RLMDGhost
