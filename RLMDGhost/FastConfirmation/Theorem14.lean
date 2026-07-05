import RLMDGhost.FastConfirmation.Basic
import RLMDGhost.ProposeVoteMerge.Lemma1

/-!
# Theorem 14 — liveness of fast confirmations

> **Theorem 14** (Liveness of fast confirmations, arXiv:2302.11326). An honest
> proposal `B` from a slot `t` after `GST + ∆` in which `|H_t| ≥ 2n/3` and
> network latency is `≤ ∆/2` is fast confirmed by all active validators at
> round `3∆t + ∆`.

The paper's proof: validators in `H_t` are active throughout `[3∆t1 + 2∆,
3∆t + ∆]` (else the joining protocol would keep them inactive), so with latency
`≤ ∆/2` they all receive the honest proposal by `3∆t + ∆/2`; by the view-merge
property (Lemma 1) they all vote for `B`; latency again delivers those votes by
`3∆t + ∆`, so each `H_t` view holds `|H_t| ≥ 2n/3` slot-`t` votes for `B` and
`B` is fast confirmed.

Formalisation over the interfaces: the low-latency / full-participation
hypotheses are the premise `2·n₃ ≤ |H_t|` together with a `FastLivenessSpec`
bundling exactly the two delivery mechanics the proof uses —

* `all_vote` — under the hypotheses, *every* honest voter of the pivot slot `t`
  votes for `B` (this is Lemma 1 applied at the pivot slot, plus the latency
  bound that keeps `H_t` awake through the voting round; `Spec.toFastLiveness`
  discharges it from `Spec` + Lemma 1);
* `fastConfirm_of_quorum` — the fast-confirmation rule: if every member of a
  `Finset` of size `≥ 2n₃` casts a slot-`t` vote for `B` and those are all
  delivered (latency `≤ ∆/2`), then every active validator fast confirms `B`.

The theorem then chains them. -/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η n₃ : ℕ}

/-- The extra delivery mechanics Theorem 14 needs, beyond `FastConfirmModel`:
the view-merge conclusion at the pivot slot and the fast-confirmation rule under
low latency. Both are protocol mechanics (Lemma 1 + Alg. B), not numbered
results. -/
structure FastLivenessSpec (R : FastConfirmModel E SM η n₃) (t : Slot) : Prop where
  /-- **Full honest agreement at the pivot slot** (Lemma 1 + latency keeps `H_t`
  awake through `3∆t + ∆`): every member of `H_t` votes for the honest proposal
  `B = proposal t`. -/
  all_vote : ∀ u ∈ SM.H t, E.votesFor u t (E.proposal t)
  /-- **Fast-confirmation rule** (Alg. B, latency `≤ ∆/2`): if a set `Q` of size
  `≥ 2n₃` all cast slot-`t` votes for `B`, every active validator `w` at round
  `3∆t + ∆` fast confirms `B`. -/
  fastConfirm_of_quorum :
    ∀ {B : Block} (Q : Finset Validator), 2 * n₃ ≤ Q.card →
      (∀ u ∈ Q, E.votesFor u t B) →
      ∀ {w : Validator}, E.active w (E.voteRound t) → R.fastConfirms w t B

/-- **Theorem 14 (Liveness of fast confirmations).** If the honest voters of a
pivot slot `t` number at least `2n/3` (`2·n₃ ≤ |H_t|`) — full participation with
low latency — then every active validator fast confirms the honest proposal of
slot `t`. -/
theorem theorem14 (R : FastConfirmModel E SM η n₃) {t : Slot}
    (FL : FastLivenessSpec R t) (hquorum : 2 * n₃ ≤ (SM.H t).card)
    {w : Validator} (hact : E.active w (E.voteRound t)) :
    R.fastConfirms w t (E.proposal t) :=
  FL.fastConfirm_of_quorum (SM.H t) hquorum FL.all_vote hact

end RLMDGhost
