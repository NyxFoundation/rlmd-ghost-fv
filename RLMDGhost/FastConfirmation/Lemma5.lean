import RLMDGhost.FastConfirmation.Basic
import RLMDGhost.GhostInstantiations.Lemma3

/-!
# Lemma 5 — synchrony in a slot voting window ⇒ honest votes carry

> **Lemma 5** (arXiv:2302.11326). Suppose network synchrony holds for rounds
> `[3∆t + ∆, 3∆t + 2∆]`, and that an honest validator fast confirms block `B`
> at slot `t`. Suppose also that, in the view of any active validator at slot
> `t + 1`, `< n/3` validators are seen as equivocators. Then, all honest voters
> of slot `t + 1` vote for descendants of `B`.

The paper's counting argument, packaged over the `FastConfirmModel` interface:

* the fast-confirmation quorum broadcasts `≥ 2n/3` slot-`t` votes for `B`, which
  synchrony delivers into every slot-`(t+1)` view; at most `< n/3` are
  discounted as equivocators, so `w(B, ·) ≥ |quorum \ equiv| > 2n₃ − n₃ = n₃`
  (`quorum_counted` + `count_le_weight`);
* every counted vote conflicting with `B` comes from a non-quorum contributor,
  and those number `< n₃`, so `w(B′, ·) ≤ |offB| < n₃` for every conflicting
  `B′` (`counted_offB` + `weight_le_contrib`);
* `w(B) > n₃ > w(B′)` for every conflicting `B′`, and `w(B) > 0`, so
  `canonical_of_conflict_lt` makes `B` canonical in the view — the honest voter
  votes for its canonical-chain tip, a descendant of `B`.

The conclusion `∀ w, voter w (t+1) → votesForDescendant w (t+1) B` is exactly
the base case Theorem 12 feeds into the shared `canonical_from_base`.
-/

namespace RLMDGhost

open BlockTree

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η n₃ : ℕ}

/-- The canonical-chain form of Lemma 5: `B` is canonical in the view held by
an active validator at either fork-choice round of slot `t + 1`. -/
private theorem canonical_at (R : FastConfirmModel E SM η n₃)
    {vc : Validator} {t : Slot} {B : Block} (hfc : R.fastConfirms vc t B)
    {w : Validator} {r : Round} (hact : E.active w r)
    (hr : r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1)) :
    B ≤ E.FC (R.effView w r) (t + 1) := by
  classical
  -- lower bound: `w(B) ≥ |quorum \ equiv| ≥ 2n₃ − |equiv|`
  have hlow : (R.quorum t \ R.equiv t).card
      ≤ weight B (R.votes (R.effView w r) (t + 1)) := by
    apply R.count_le_weight
    intro u hu
    rw [Finset.mem_sdiff] at hu
    obtain ⟨b, hb, hBb⟩ := R.quorum_counted hfc hact hr u hu.1 hu.2
    exact ⟨b, hBb, hb⟩
  have hsdiff : (R.quorum t).card - (R.equiv t).card ≤ (R.quorum t \ R.equiv t).card :=
    Finset.le_card_sdiff _ _
  have hq : 2 * n₃ ≤ (R.quorum t).card := R.quorum_card hfc
  have he : (R.equiv t).card < n₃ := R.lowEquiv hfc
  have ho : (R.offB t).card < n₃ := R.offB_card hfc
  refine canonical_of_conflict_lt (by omega) (fun B' hconf => ?_)
    (R.fc_ghost (R.effView w r) (t + 1))
  -- upper bound: `w(B′) ≤ |offB| < n₃ < w(B)` for conflicting `B′`
  have hwB' : weight B' (R.votes (R.effView w r) (t + 1)) ≤ (R.offB t).card := by
    apply R.weight_le_contrib
    intro u b hb hB'b
    have hnB : ¬B ≤ b := fun hBb => hconf (consistent_of_le_of_le hBb hB'b)
    exact R.counted_offB hfc hact hr u b hb hnB
  omega

/-- **Lemma 5.** If an honest validator fast confirms `B` at slot `t` (with
synchrony over the slot's voting window and `< n/3` equivocators seen in every
slot-`(t+1)` view), then every honest voter of slot `t + 1` votes for a
descendant of `B`. -/
theorem lemma5 (S : Spec E) (R : FastConfirmModel E SM η n₃)
    {vc : Validator} {t : Slot} {B : Block} (hfc : R.fastConfirms vc t B) :
    ∀ w : Validator, E.voter w (t + 1) → E.votesForDescendant w (t + 1) B := by
  intro w hw
  refine ⟨E.chAt w (E.voteRound (t + 1)), ?_, S.vote_chAt hw⟩
  have hcanon := canonical_at R hfc hw (Or.inr rfl)
  rwa [← R.chAt_fc hw (Or.inr rfl)] at hcanon

end RLMDGhost
