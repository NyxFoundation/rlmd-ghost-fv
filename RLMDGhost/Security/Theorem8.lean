import RLMDGhost.Security.Basic
import RLMDGhost.ProposeVoteMerge.Lemma1

/-!
# Theorem 8 — RLMD-GHOST is `(η, η−1)`-asynchrony-resilient

> **Theorem 8** (Asynchrony resilience, arXiv:2302.11326). RLMD-GHOST is
> `(η, η−1)`-asynchrony-resilient.

Definitions (§2.1.2, transcribed from the source paper since §2 is not in the
notes): a *tpa* `(t1, t2)` is an interval in which synchrony does not hold,
a `π`-tpa one with `t2 − t1 ≤ π`; a validator is *aware* at a round `r` of a
slot `s ∈ (t1, t2]` if it is active at `r` and belongs to `H_{t1}`, and aware
at any other round simply if it is active (`Aware` below). A `(τ, π)`-compliant
execution (Definition 3) has a `π`-tpa `(t1, t2)` and satisfies

* `τ`-sleepiness at every slot `∉ (t1, t2]` (`EtaSleepyOutside`),
* `|H_{t1} \ A_s| > |A_s ∪ (H_{s−τ,s−1} \ H_{t1})|` for `s ∈ (t1, t2 + 1]`
  (`TpaSleepy`),
* `H_{t1}` awake at round `3∆t1 + 2∆` (absorbed into `tpa_vote_counted`).

*Asynchrony resilience* (Definition 7): any honest proposal from a slot
`t ≤ t1` is always in the canonical chain of all aware validators at rounds
`≥ 3∆t + ∆`.

An execution with a tpa does **not** satisfy the synchronous interfaces
globally: the delivery fields of `RLMDGhostModel` (and the view-merge fields
of `Spec`) fail inside the tpa. Theorem 8 therefore assumes only

* `TpaSpec` — the synchrony-independent voting mechanics plus Lemma 1's
  conclusion at the proposal slot `t` (synchrony holds through slot `t1 ≥ t`,
  so Lemma 1 applies there; `Spec.toTpaSpec` derives it in the fully
  synchronous reading), and
* `TpaModel` — the delivery mechanics restricted to the synchronous slots,
  plus the two tpa-specific facts the paper's proof uses.

The proof is the paper's strong induction on the slot `s`, with the generic
counting core `canonical_of_majority` discharging every case:

* `s = t`: Lemma 1 (via `TpaSpec.base`).
* `t < s ≤ t1` and `s > t2 + 1`: the synchronous (Lemma 4 / Proposition 1)
  step — honest voters of `s − 1` vote descendants of `B` by the induction
  hypothesis, and `η`-sleepiness outside the tpa gives the majority
  (`sync_step`).
* `t1 < s ≤ t2 + 1`: the aware view contains, for each `u ∈ H_{t1} \ A_s`, a
  counted latest vote which is one of `u`'s own honest votes from `[t1, s−1]`
  (delivery of slot-`t1` votes since `H_{t1}` was awake at the `3∆t1 + 2∆`
  merge — for `s = t2 + 1`, synchrony from slot `t2` — and no expiry since
  `t2 ≤ t1 + η − 1`); by the induction hypothesis those votes extend `B`, and
  the Definition 3 inequality gives the majority.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]

/-- *Aware* (§2.1.2): at a (fork-choice) round `r` of a slot `s ∈ (t1, t2]`, a
validator is aware if it is active and in `H_{t1}`; at rounds of any other slot,
aware coincides with active. -/
def Aware (E : Execution Block Validator View) (SM : SleepyModel E)
    (t1 t2 : Slot) (v : Validator) (s : Slot) (r : Round) : Prop :=
  E.active v r ∧ (t1 < s → s ≤ t2 → v ∈ SM.H t1)

variable {E : Execution Block Validator View}

/-- The fragment of the protocol specification that an execution with a tpa
still satisfies, and which Theorem 8 consumes: the synchrony-independent
voting mechanics of `Spec`, plus the conclusion of Lemma 1 at the proposal
slot `t` (available because synchrony holds through slot `t1 ≥ t`). -/
structure TpaSpec (E : Execution Block Validator View) (t : Slot) : Prop where
  /-- Voting rule (synchrony-free): honest voters vote their canonical-chain
  tip at the voting round. -/
  vote_chAt :
    ∀ {v : Validator} {s : Slot}, E.voter v s →
      E.votesFor v s (E.chAt v (E.voteRound s))
  /-- Honest non-equivocation (synchrony-free). -/
  vote_unique :
    ∀ {v : Validator} {s : Slot} {b b' : Block},
      E.voter v s → E.votesFor v s b → E.votesFor v s b' → b = b'
  /-- Lemma 1 at the proposal slot `t` (synchrony holds through `t1 ≥ t`). -/
  base :
    ∀ {v : Validator}, E.voter v t →
      E.chAt v (E.voteRound t) = E.proposal t

omit [FiniteAncestors Block] [DecidableEq Validator] in
/-- In the fully synchronous reading, `TpaSpec` is a consequence of `Spec` and
Lemma 1 at a pivot slot. -/
theorem Spec.toTpaSpec (S : Spec E) {t : Slot} (hpivot : E.pivot t) :
    TpaSpec E t :=
  ⟨fun h => S.vote_chAt h, fun h => S.vote_unique h,
   fun hv => lemma1_canonical S hpivot hv⟩

/-- The tpa-execution mechanics for Theorem 8 (Barrier 4), over the base
RLMD-GHOST interface: the synchronous delivery facts restricted to slots
outside `(t1, t2 + 1]`, and the two tpa-specific facts of the paper's proof.

* `tpa_vote_counted` — in the effective view of an *aware* validator at a
  fork-choice round of a slot `s ∈ (t1, t2 + 1]`, each `u ∈ H_{t1} \ A_s` has
  its latest own honest vote (from some slot in `[t1, s−1]`) counted: `H_{t1}`
  was awake at the `3∆t1 + 2∆` merge (Definition 3) so its slot-`t1` votes
  reached every aware view (for `s = t2 + 1`, synchrony from slot `t2` delivers
  the latest ones), `t2 ≤ t1 + η − 1` keeps slot-`t1` votes unexpired, and
  members of `H_{t1} \ A_s` are not corrupted by round `3∆s + ∆`, hence not
  equivocators (Barrier 2 unforgeability) — the paper's "all validators in
  `Ht1 \ As` are not equivocators in `Vi`, therefore their latest votes in `Vi`
  all count". Corrupted members of `H_{t1} ∩ A_s` are *not* constrained: the
  adversary may broadcast fresh votes from them, and the counting places all
  such votes on the `A_s` side of the Definition 3 inequality.
* `tpa_from_window` — `η`-expiry: counted votes at slot `s` are from
  `[s−η, s−1]`, so their senders are corrupted or in `H_{s−η,s−1}`. -/
structure TpaModel (E : Execution Block Validator View) (SM : SleepyModel E)
    (η : ℕ) (R : RLMDGhostBase E) (t1 t2 : Slot) where
  /-- The tpa interval is ordered. -/
  t1_le_t2 : t1 ≤ t2
  /-- `(η−1)`-tpa: `t2 − t1 ≤ η − 1`, subtraction-free. -/
  span : t2 + 1 ≤ t1 + η
  /-- `honest_vote_counted` of `RLMDGhostModel`, restricted to the synchronous
  concluding slots `t + 1 ≤ t1` and `t + 1 ≥ t2 + 2`. -/
  honest_vote_counted_sync :
    ∀ {v : Validator} {t : Slot} {r : Round},
      t + 1 ≤ t1 ∨ t2 + 2 ≤ t + 1 → E.active v r →
      r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1) →
      ∀ u ∈ SM.H t,
        (∃ b, R.voteOf (R.effView v r) (t + 1) u = some b ∧ E.votesFor u t b) ∨
        (R.voteOf (R.effView v r) (t + 1) u = none ∧ u ∈ SM.A (t + 1))
  /-- `counted_from_window` of `RLMDGhostModel`, restricted to the synchronous
  concluding slots. -/
  counted_from_window_sync :
    ∀ {v : Validator} {t : Slot} {r : Round},
      t + 1 ≤ t1 ∨ t2 + 2 ≤ t + 1 → E.active v r →
      r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1) →
      ∀ u b, R.voteOf (R.effView v r) (t + 1) u = some b →
        u ∈ SM.H t ∨ u ∈ SM.A (t + 1) ∨ u ∈ SM.Hwindow η (t + 1)
  /-- Delivery inside the tpa, for the still-honest `H_{t1} \ A_s`; see the
  structure docstring. -/
  tpa_vote_counted :
    ∀ {v : Validator} {s : Slot} {r : Round}, t1 < s → s ≤ t2 + 1 →
      Aware E SM t1 t2 v s r → (r = E.slotStart s ∨ r = E.voteRound s) →
      ∀ u ∈ SM.H t1, u ∉ SM.A s →
        ∃ s' b, t1 ≤ s' ∧ s' + 1 ≤ s ∧ E.voter u s' ∧ E.votesFor u s' b ∧
          R.voteOf (R.effView v r) s u = some b
  /-- Expiry provenance inside the tpa; see the structure docstring. -/
  tpa_from_window :
    ∀ {v : Validator} {s : Slot} {r : Round}, t1 < s → s ≤ t2 + 1 →
      Aware E SM t1 t2 v s r → (r = E.slotStart s ∨ r = E.voteRound s) →
      ∀ u b, R.voteOf (R.effView v r) s u = some b →
        u ∈ SM.A s ∨ u ∈ SM.HwindowIncl η s

variable {SM : SleepyModel E} {η : ℕ} {R : RLMDGhostBase E} {t1 t2 : Slot}

/-- The synchronous induction step of Theorem 8 (the Lemma 4 counting, from
the restricted delivery fields): if all honest voters of slot `u` voted for
descendants of `B` and slot `u + 1` is outside `(t1, t2 + 1]`, then `B` is
canonical for active validators at the fork-choice rounds of slot `u + 1`. -/
private theorem sync_step {t : Slot} (T : TpaModel E SM η R t1 t2)
    (TS : TpaSpec E t) (hout : SM.EtaSleepyOutside η t1 t2)
    {u : Slot} {B : Block} (hslot : u + 1 ≤ t1 ∨ t2 + 2 ≤ u + 1)
    (hvotes : ∀ w : Validator, E.voter w u → E.votesForDescendant w u B)
    {v : Validator} {r : Round} (hact : E.active v r)
    (hr : r = E.slotStart (u + 1) ∨ r = E.voteRound (u + 1)) :
    B ≤ E.chAt v r := by
  classical
  have hHvote : ∀ w ∈ SM.H u, ∀ b, E.votesFor w u b → B ≤ b := by
    intro w hw b hb
    obtain ⟨b', hBb', hb'⟩ := hvotes w (SM.H_voter hw)
    have : b = b' := TS.vote_unique (SM.H_voter hw) hb hb'
    rw [this]; exact hBb'
  rw [R.chAt_fc hact hr]
  apply canonical_of_majority R (SM.H u)
    (SM.A (u + 1) ∪ (SM.Hwindow η (u + 1) \ SM.H u)) ?_ ?_
    (hout u (hslot.imp id Nat.le_of_succ_le))
  · intro w hw
    rcases T.honest_vote_counted_sync hslot hact hr w hw with ⟨b, hb, hvb⟩ | ⟨hn, hA⟩
    · exact Or.inl ⟨b, hb, hHvote w hw b hvb⟩
    · exact Or.inr ⟨hn, Finset.mem_union_left _ hA⟩
  · intro w b hb _
    rcases T.counted_from_window_sync hslot hact hr w b hb with hH | hA | hW
    · exact Or.inl hH
    · exact Or.inr (Finset.mem_union_left _ hA)
    · by_cases hwH : w ∈ SM.H u
      · exact Or.inl hwH
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hW, hwH⟩))

/-- **Theorem 8 (Asynchrony resilience).** In an `(η, η−1)`-compliant
execution — Definition 3 threaded as `EtaSleepyOutside` + `TpaSleepy` + the
`TpaModel`/`TpaSpec` mechanics — the proposal of a slot `t ≤ t1` is in the
canonical chain of every aware validator at every fork-choice round from
`3∆t + ∆` on (Definition 7). -/
theorem theorem8 (T : TpaModel E SM η R t1 t2) {t : Slot} (TS : TpaSpec E t)
    (hout : SM.EtaSleepyOutside η t1 t2) (htpa : SM.TpaSleepy η t1 t2)
    (htt1 : t ≤ t1) :
    (∀ s : Slot, t ≤ s → ∀ v : Validator,
      Aware E SM t1 t2 v s (E.voteRound s) →
        E.proposal t ≤ E.chAt v (E.voteRound s)) ∧
    (∀ s : Slot, t < s → ∀ v : Validator,
      Aware E SM t1 t2 v s (E.slotStart s) →
        E.proposal t ≤ E.chAt v (E.slotStart s)) := by
  have main : ∀ s : Slot, t ≤ s → ∀ (r : Round) (v : Validator),
      ((r = E.slotStart s ∧ t < s) ∨ r = E.voteRound s) →
      Aware E SM t1 t2 v s r → E.proposal t ≤ E.chAt v r := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hts r v hr haw
      rcases Nat.eq_or_lt_of_le hts with rfl | hlt
      · -- base: the proposal slot itself, voting round only
        rcases hr with ⟨-, habs⟩ | rfl
        · exact absurd habs (lt_irrefl _)
        · exact (TS.base haw.1).ge
      · have hrr : r = E.slotStart s ∨ r = E.voteRound s := hr.imp And.left id
        rcases Nat.lt_or_ge t1 s with ht1s | hst1
        · rcases (Nat.lt_or_ge (t2 + 1) s).symm with hst2 | ht2s
          · -- tpa case: t1 < s ≤ t2 + 1
            rw [R.chAt_fc haw.1 hrr]
            apply canonical_of_majority R (SM.H t1 \ SM.A s)
              (SM.A s ∪ (SM.HwindowIncl η s \ SM.H t1)) ?_ ?_ (htpa s ht1s hst2)
            · -- H_{t1} \ A_s members' counted latest votes extend B (IH)
              intro u hu
              rw [Finset.mem_sdiff] at hu
              obtain ⟨s', b, hs'1, hs'2, hvoter, hvfor, hvoteOf⟩ :=
                T.tpa_vote_counted ht1s hst2 haw hrr u hu.1 hu.2
              refine Or.inl ⟨b, hvoteOf, ?_⟩
              have hawu : Aware E SM t1 t2 u s' (E.voteRound s') :=
                ⟨hvoter, fun _ _ => hu.1⟩
              have hchain := ih s' (Nat.lt_of_succ_le hs'2)
                (le_trans htt1 hs'1) _ u (Or.inr rfl) hawu
              have : b = E.chAt u (E.voteRound s') :=
                TS.vote_unique hvoter hvfor (TS.vote_chAt hvoter)
              rw [this]; exact hchain
            · -- provenance during the tpa
              intro u b hb _
              rcases T.tpa_from_window ht1s hst2 haw hrr u b hb with hA | hW
              · exact Or.inr (Finset.mem_union_left _ hA)
              · by_cases huA : u ∈ SM.A s
                · exact Or.inr (Finset.mem_union_left _ huA)
                · by_cases huH : u ∈ SM.H t1
                  · exact Or.inl (Finset.mem_sdiff.mpr ⟨huH, huA⟩)
                  · exact Or.inr
                      (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hW, huH⟩))
          · -- post-tpa synchronous case: s ≥ t2 + 2
            obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 :=
              ⟨s - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt t.zero_le hlt)).symm⟩
            have hvac : ∀ _ : t1 < u, u ≤ t2 → False := fun _ h2 =>
              absurd h2 (not_le.mpr (Nat.lt_of_succ_le (Nat.succ_le_succ_iff.mp ht2s)))
            have hvoters : ∀ w : Validator, E.voter w u →
                E.votesForDescendant w u (E.proposal t) := by
              intro w hw
              have hawu : Aware E SM t1 t2 w u (E.voteRound u) :=
                ⟨hw, fun h1 h2 => (hvac h1 h2).elim⟩
              exact ⟨_, ih u (Nat.lt_succ_self u) (Nat.lt_succ_iff.mp hlt) _ w
                (Or.inr rfl) hawu, TS.vote_chAt hw⟩
            exact sync_step T TS hout (Or.inr ht2s) hvoters haw.1 hrr
        · -- pre-tpa synchronous case: s ≤ t1
          obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 :=
            ⟨s - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt t.zero_le hlt)).symm⟩
          have hvac : ∀ _ : t1 < u, u ≤ t2 → False := fun h1 _ =>
            absurd h1 (not_lt.mpr (Nat.le_of_succ_le hst1))
          have hvoters : ∀ w : Validator, E.voter w u →
              E.votesForDescendant w u (E.proposal t) := by
            intro w hw
            have hawu : Aware E SM t1 t2 w u (E.voteRound u) :=
              ⟨hw, fun h1 h2 => (hvac h1 h2).elim⟩
            exact ⟨_, ih u (Nat.lt_succ_self u) (Nat.lt_succ_iff.mp hlt) _ w
              (Or.inr rfl) hawu, TS.vote_chAt hw⟩
          exact sync_step T TS hout (Or.inl hst1) hvoters haw.1 hrr
  exact ⟨fun s hts v hv => main s hts _ v (Or.inr rfl) hv,
         fun s hts v hv => main s (le_of_lt hts) _ v (Or.inl ⟨rfl, hts⟩) hv⟩

/-- **Asynchrony resilience** (Definition 7): in an execution with a tpa
`(t1, t2)`, every honest proposal `B` from a pivot slot `t ≤ t1` is in the
canonical chain of all *aware* validators at every fork-choice round from
`3∆t + ∆` on. This is exactly the conclusion `theorem8` establishes for
`(η, η−1)`-compliant executions; `theorem11` exhibits an `(∞, η)`-compliant
execution for which it *fails*. -/
def AsynchronyResilient (E : Execution Block Validator View) (SM : SleepyModel E)
    (t1 t2 : Slot) : Prop :=
  ∀ t : Slot, t ≤ t1 → E.pivot t →
    (∀ s : Slot, t ≤ s → ∀ v : Validator,
      Aware E SM t1 t2 v s (E.voteRound s) →
        E.proposal t ≤ E.chAt v (E.voteRound s)) ∧
    (∀ s : Slot, t < s → ∀ v : Validator,
      Aware E SM t1 t2 v s (E.slotStart s) →
        E.proposal t ≤ E.chAt v (E.slotStart s))

end RLMDGhost
