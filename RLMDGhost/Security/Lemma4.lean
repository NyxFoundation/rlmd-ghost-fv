import RLMDGhost.Security.Basic
import RLMDGhost.ProposeVoteMerge.Proposition1

/-!
# Lemma 4 — Proposition 1 holds for RLMD-GHOST in `η`-compliant executions

> **Lemma 4** (arXiv:2302.11326). Proposition 1 holds for RLMD-GHOST in
> `η`-compliant executions.

The paper's counting argument, for the view `V` of an active validator at a
round `∈ {3∆t, 3∆t + ∆}` (here `s = t + 1`, previous slot `t`), given that all
honest voters of the previous slot voted for descendants of `B`:

* by synchrony and the buffer merge at `3∆t + 2∆`, all slot-`t` honest votes
  are in `V`, unexpired, and are their senders' latest messages
  (`honest_vote_counted`); the discounted equivocators
  `E ⊆ H_t ∩ A_{t+1}` contribute nothing;
* every counted vote not for a descendant of `B` comes from
  `A_{t+1} ∪ (H_{t+1−η,t−1} \ H_t)` (`counted_from_window`);
* `η`-sleepiness `|H_t| > |A_{t+1} ∪ (…)|` then makes the descendants of `B` a
  strict majority of the counted votes (`canonical_of_majority` carries out
  the paper's `|H_t| − |E|` vs `|…| − |E|` bookkeeping), and Lemma 3 concludes
  that the GHOST output — the canonical-chain tip (`chAt_fc`) — extends `B`.

This discharges the `Persistence` predicate (Proposition 1) threaded into
Theorems 1–2, yielding Theorems 6–7.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η : ℕ}

/-- The core of Lemma 4: `B` is canonical in the view held by an active
validator at either fork-choice round of slot `t + 1`. -/
private theorem canonical_at (S : Spec E) (R : RLMDGhostModel E SM η)
    (hsleepy : SM.EtaSleepy η) {t : Slot} {B : Block}
    (hvotes : ∀ u : Validator, E.voter u t → E.votesForDescendant u t B)
    {v : Validator} {r : Round} (hact : E.active v r)
    (hr : r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1)) :
    B ≤ E.chAt v r := by
  classical
  -- an `H t` member's actual slot-`t` vote extends `B`
  have hHvote : ∀ u ∈ SM.H t, ∀ b, E.votesFor u t b → B ≤ b := by
    intro u hu b hb
    obtain ⟨b', hBb', hb'⟩ := hvotes u (SM.H_voter hu)
    have : b = b' := S.vote_unique (SM.H_voter hu) hb hb'
    rw [this]; exact hBb'
  rw [R.chAt_fc hact hr]
  apply canonical_of_majority R.toRLMDGhostBase (SM.H t)
    (SM.A (t + 1) ∪ (SM.Hwindow η (t + 1) \ SM.H t)) ?_ ?_ (hsleepy t)
  · -- every `H t` member contributes its slot-`t` vote, or is discounted
    intro u hu
    rcases R.honest_vote_counted hact hr u hu with ⟨b, hb, hvb⟩ | ⟨hn, hA⟩
    · exact Or.inl ⟨b, hb, hHvote u hu b hvb⟩
    · exact Or.inr ⟨hn, Finset.mem_union_left _ hA⟩
  · -- provenance of counted votes
    intro u b hb _
    rcases R.counted_from_window hact hr u b hb with hH | hA | hW
    · exact Or.inl hH
    · exact Or.inr (Finset.mem_union_left _ hA)
    · by_cases huH : u ∈ SM.H t
      · exact Or.inl huH
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hW, huH⟩))

/-- **Lemma 4.** In an `η`-compliant execution (η-sleepiness threaded as
`hsleepy`; synchrony and the filter mechanics in `Spec`/`RLMDGhostModel`),
RLMD-GHOST satisfies Proposition 1 (`Persistence`). -/
theorem lemma4 (S : Spec E) (R : RLMDGhostModel E SM η)
    (hsleepy : SM.EtaSleepy η) : Persistence E :=
  fun _t _B hvotes _v =>
    ⟨fun hact => canonical_at S R hsleepy hvotes hact (Or.inl rfl),
     fun hact => canonical_at S R hsleepy hvotes hact (Or.inr rfl)⟩

end RLMDGhost
