import RLMDGhost.TrackA.Lemma1

/-!
# Theorem 1 — reorg resilience

> **Theorem 1 (Reorg resilience).** Consider an execution of a propose-vote-merge
> protocol in which Proposition 1 holds. Then this execution satisfies reorg
> resilience.

The paper proves it by induction on the slot. With `B` the honest proposal of
slot `t`:

* **Base** (`s = t`): Lemma 1 — every honest voter of slot `t` votes for `B`.
* **Step**: if every honest voter of slot `s` votes for a descendant of `B`,
  then Proposition 1 (instantiated at slot `s+1`, whose previous slot is `s`)
  makes `B` canonical at slot `s+1`; the voting rule then makes every honest
  voter of slot `s+1` vote for the fork-choice output, which has `B` as a prefix.

We thread Proposition 1 in as the hypothesis `Proposition1Holds E` (established
per protocol — for RLMD-GHOST by Lemma 4), so Theorem 1 is fully proved with no
`sorry` and no axiom: "Proposition 1 ⇒ reorg resilience".
-/

namespace RLMDGhost

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- The slot invariant carried by the induction: every honest voter of slot `s`
votes for a descendant of `B`. Holds for every slot `s ≥ t`. -/
theorem honestVotes_persist (S : Spec E) (hp1 : Proposition1Holds E)
    {vp : Validator} {t : Slot}
    (hprop : E.eligiblePropose vp t) (hhon : E.honestAt vp (E.slotStart t)) :
    ∀ s : Slot, t ≤ s → ∀ id : Validator, E.honestVoter id s →
      E.votesForDescendant id s (E.proposalBlock vp t) := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base => exact lemma1_votesForDescendant S hprop hhon
  | succ s _ ih =>
    -- Proposition 1 at slot `s+1`: its previous slot is `s`, where `ih` applies.
    have hprev : ∀ id : Validator, E.honestVoter id (s + 1 - 1) →
        E.votesForDescendant id (s + 1 - 1) (E.proposalBlock vp t) := by
      simpa using ih
    have hcanon := (hp1 (E.proposalBlock vp t) (s + 1) hprev).2
    intro id hid
    exact Execution.votesForDescendant_of_canonical S hcanon hid

/-- **Theorem 1.** In an execution satisfying Proposition 1, the honest proposal
of any pivot slot `t` is reorg resilient: every honest voter of slot `t` votes
for it and it stays canonical in every active validator's view at every later
slot. -/
theorem theorem1 (S : Spec E) (hp1 : Proposition1Holds E)
    {vp : Validator} {t : Slot}
    (hprop : E.eligiblePropose vp t) (hhon : E.honestAt vp (E.slotStart t)) :
    ReorgResilient E (E.proposalBlock vp t) t := by
  refine ⟨lemma1_votesForDescendant S hprop hhon, ?_⟩
  intro s hts
  -- `t < s` ⇒ `s = s' + 1` with `t ≤ s'`; Proposition 1 at slot `s` gives canonicity.
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 :=
    ⟨s - 1, (Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (Nat.zero_le t) hts)).symm⟩
  have hts' : t ≤ s' := Nat.lt_succ_iff.mp hts
  have hprev : ∀ id : Validator, E.honestVoter id (s' + 1 - 1) →
      E.votesForDescendant id (s' + 1 - 1) (E.proposalBlock vp t) := by
    simpa using honestVotes_persist S hp1 hprop hhon s' hts'
  exact (hp1 (E.proposalBlock vp t) (s' + 1) hprev).2

end RLMDGhost
