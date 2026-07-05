import RLMDGhost.ProposeVoteMerge.Lemma1
import RLMDGhost.ProposeVoteMerge.Proposition1

/-!
# Theorem 1 — reorg resilience: an honest proposal is never reorged

> **Theorem 1** (Reorg resilience, arXiv:2302.11326). Let us consider an
> execution of a propose-vote-merge protocol in which Proposition 1 holds.
> Then, this execution satisfies reorg resilience.

The paper's induction on slots `s ≥ t`, for an honest (pivot-slot) proposal `B`
of slot `t`:

* **Base case** `s = t`: Lemma 1 applies — all honest voters of slot `t` vote
  for `B`, which is in particular (exactly) their canonical chain at the voting
  round (`lemma1_canonical`).
* **Inductive step**: if `B` is canonical for every honest voter of slot `s`,
  then by the voting rule they all vote for descendants of `B`, and
  Proposition 1 carries `B` into the canonical chains at both fork-choice
  rounds of slot `s + 1`.

Validators only update their canonical chain at the rounds `{3∆s, 3∆s + ∆}`, so
the statement over those rounds is reorg resilience (`ReorgResilient`).
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  {E : Execution Block Validator View}

/-- **Theorem 1 (Reorg resilience).** An execution of a propose-vote-merge
protocol in which Proposition 1 (`Persistence`) holds satisfies reorg
resilience. -/
theorem theorem1 (S : Spec E) (hP : Persistence E) : ReorgResilient E := by
  intro t hpivot
  have key : ∀ s : Slot, t ≤ s → ∀ v : Validator, E.active v (E.voteRound s) →
      E.proposal t ≤ E.chAt v (E.voteRound s) := by
    intro s hts
    induction s, hts using Nat.le_induction with
    | base => exact fun v hv => (lemma1_canonical S hpivot hv).ge
    | succ s _ ih =>
      intro v hv
      have hvotes : ∀ u : Validator, E.voter u s → E.votesForDescendant u s (E.proposal t) :=
        fun u hu => ⟨E.chAt u (E.voteRound s), ih u hu, S.vote_chAt hu⟩
      exact (hP s (E.proposal t) hvotes v).2 hv
  refine ⟨key, fun s hts v hv => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 :=
    ⟨s - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt t.zero_le hts)).symm⟩
  have hvotes : ∀ u : Validator, E.voter u s → E.votesForDescendant u s (E.proposal t) :=
    fun u hu =>
      ⟨E.chAt u (E.voteRound s), key s (Nat.lt_succ_iff.mp hts) u hu, S.vote_chAt hu⟩
  exact (hP s (E.proposal t) hvotes v).1 hv

end RLMDGhost
