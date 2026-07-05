import RLMDGhost.Model
import RLMDGhost.GhostInstantiations.Lemma3

/-!
# RLMD-GHOST — the RLMD instantiation interface (§5)

RLMD-GHOST is `GHOST ∘ FIL_rlmd` with
`FIL_rlmd = FIL_lmd ∘ FIL_η-exp ∘ FIL_eq`: the fork choice of view `V` at slot
`s` runs the GHOST descent over the votes that survive equivocation
discounting, `η`-expiry (only slots `[s−η, s−1]` count) and latest-message
filtering. Per Barrier 4 this is an abstract interface, split in two:

* `RLMDGhostBase` — the synchrony-*free* mechanics: `votes V s` is the
  counted-vote multiset, `voteOf V s u` the (at most one) counted vote of
  validator `u`, the fork choice is the GHOST descent on the counted votes
  (`fc_ghost`, `chAt_fc`), and the two counting bookkeeping facts
  (`count_le_weight`, `card_le_weight_add` — each validator contributes at
  most one counted vote). These hold in *any* execution, including one with a
  temporary period of asynchrony (Theorem 8).
* `RLMDGhostModel` — additionally the synchrony-dependent delivery facts for
  every slot (`honest_vote_counted`, `counted_from_window`), i.e. the fully
  synchronous setting of Lemma 4 and Theorems 6–7. A tpa execution does *not*
  satisfy these globally; Theorem 8 instead assumes their restrictions to the
  synchronous slots (`TpaModel`).

`canonical_of_majority` is the generic counting core shared by Lemma 4 and all
three cases of Theorem 8: if every member of a `Finset` `HS` either contributes
a counted vote for a descendant of `B` or is discounted into `X`, every counted
vote not for a descendant of `B` comes from `HS ∪ X`, and `|X| < |HS|`, then
the counted votes for descendants of `B` are a strict majority (the paper's
`|H| − |E|` vs `|… | − |E|` bookkeeping) and Lemma 3 makes `B` canonical.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  [DecidableEq Validator]

/-- The synchrony-free part of the RLMD-GHOST instantiation (Barrier 4): the
counted-vote layer of `FIL_rlmd`, the GHOST descent, and the per-validator
counting bookkeeping. See the module docstring. -/
structure RLMDGhostBase (E : Execution Block Validator View) where
  /-- `FIL_rlmd(V, s)`: the votes counted by the fork choice of view `V` at
  slot `s`. -/
  votes : View → Slot → Multiset Block
  /-- `voteOf V s u`: the counted (latest, non-expired, non-equivocating) vote
  of validator `u` in view `V` at slot `s`, if any. -/
  voteOf : View → Slot → Validator → Option Block
  /-- The view a validator's fork choice runs on at round `r` (after the
  round's merge events). -/
  effView : Validator → Round → View
  /-- RLMD-GHOST fork choice: a GHOST descent over the counted votes. -/
  fc_ghost : ∀ (V : View) (s : Slot), GhostSelects (votes V s) (E.FC V s)
  /-- At the fork-choice rounds `{3∆s, 3∆s + ∆}`, an active validator's
  canonical chain is its fork-choice output on its effective view. -/
  chAt_fc :
    ∀ {v : Validator} {s : Slot} {r : Round}, E.active v r →
      r = E.slotStart s ∨ r = E.voteRound s →
      E.chAt v r = E.FC (effView v r) s
  /-- Bookkeeping (one counted vote per validator): validators with counted
  votes for descendants of `B` bound `w(B, ·)` from below. -/
  count_le_weight :
    ∀ (V : View) (s : Slot) (B : Block) (A : Finset Validator),
      (∀ v ∈ A, ∃ b, B ≤ b ∧ voteOf V s v = some b) →
      A.card ≤ weight B (votes V s)
  /-- Bookkeeping: if every counted vote not for a descendant of `B` comes from
  a validator in `A`, the total count is bounded by `w(B, ·) + |A|`. -/
  card_le_weight_add :
    ∀ (V : View) (s : Slot) (B : Block) (A : Finset Validator),
      (∀ v b, voteOf V s v = some b → ¬B ≤ b → v ∈ A) →
      (votes V s).card ≤ weight B (votes V s) + A.card
  /-- Bookkeeping (one counted vote per validator, upper bound): if every
  counted vote for a descendant of `B` comes from a validator in `A`, then
  `w(B, ·) ≤ |A|`. Dual of `count_le_weight`. -/
  weight_le_contrib :
    ∀ (V : View) (s : Slot) (B : Block) (A : Finset Validator),
      (∀ v b, voteOf V s v = some b → B ≤ b → v ∈ A) →
      weight B (votes V s) ≤ A.card

/-- The fully synchronous RLMD-GHOST instantiation (Lemma 4, Theorems 6–7):
the base mechanics plus the per-slot delivery facts. Field provenance:

* `honest_vote_counted` — synchrony + the buffer merge at `3∆t + 2∆` put every
  slot-`t` honest vote into the views held at the fork-choice rounds of slot
  `t + 1`, where it is not expired (`t ∈ [t+1−η, t]` for `η ≥ 1`) and is its
  sender's latest message; so a slot-`t` honest voter's counted vote is its
  slot-`t` vote — unless the sender is discounted as an equivocator, which by
  **signature unforgeability (Barrier 2)** requires a second signed slot-`t`
  message and hence that the sender has been corrupted (`u ∈ A_{t+1}`). This
  field is the interface form of the idealized-cryptography assumption; it is
  the paper's `E ⊆ H_{t−1} ∩ A_t`.
* `counted_from_window` — `η`-expiry: a counted vote at slot `t + 1` is from a
  slot in `[t+1−η, t]`, so its sender was an honest voter of slot `t`, an
  honest voter of an earlier window slot (`Hwindow η (t+1)`), or corrupted. -/
structure RLMDGhostModel (E : Execution Block Validator View)
    (SM : SleepyModel E) (η : ℕ) extends RLMDGhostBase E where
  /-- Synchrony + buffer merge + `η`-expiry + unforgeability (Barrier 2); see
  the structure docstring. -/
  honest_vote_counted :
    ∀ {v : Validator} {t : Slot} {r : Round}, E.active v r →
      r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1) →
      ∀ u ∈ SM.H t,
        (∃ b, voteOf (effView v r) (t + 1) u = some b ∧ E.votesFor u t b) ∨
        (voteOf (effView v r) (t + 1) u = none ∧ u ∈ SM.A (t + 1))
  /-- `η`-expiry provenance; see the structure docstring. -/
  counted_from_window :
    ∀ {v : Validator} {t : Slot} {r : Round}, E.active v r →
      r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1) →
      ∀ u b, voteOf (effView v r) (t + 1) u = some b →
        u ∈ SM.H t ∨ u ∈ SM.A (t + 1) ∨ u ∈ SM.Hwindow η (t + 1)

/-- **Generic majority counting** (the shared core of Lemma 4 and the three
cases of Theorem 8). If every member of `HS` either contributes a counted vote
for a descendant of `B` or contributes nothing and lies in `X` (the discounted
equivocators `E ⊆ H ∩ A` of the paper), every counted vote not for a
descendant of `B` comes from `HS ∪ X`, and `|X| < |HS|`, then the votes for
descendants of `B` are a strict majority of the counted votes
(`≥ |HS| − |D|` vs `≤ |X| − |D|` for the discounted `D ⊆ X`), and Lemma 3
forces the GHOST output to extend `B`. -/
theorem canonical_of_majority [FiniteAncestors Block]
    {E : Execution Block Validator View} (R : RLMDGhostBase E)
    {V : View} {s : Slot} {B : Block} (HS X : Finset Validator)
    (hHS : ∀ u ∈ HS,
      (∃ b, R.voteOf V s u = some b ∧ B ≤ b) ∨ (R.voteOf V s u = none ∧ u ∈ X))
    (hprov : ∀ u b, R.voteOf V s u = some b → ¬B ≤ b → u ∈ HS ∨ u ∈ X)
    (hcard : X.card < HS.card) :
    B ≤ E.FC V s := by
  classical
  set M := R.votes V s with hM
  -- D: the discounted members of HS (the paper's E)
  set D := HS.filter (fun u => R.voteOf V s u = none) with hD
  have hDsubH : D ⊆ HS := Finset.filter_subset _ _
  have hDsubX : D ⊆ X := by
    intro u hu
    rw [hD, Finset.mem_filter] at hu
    rcases hHS u hu.1 with ⟨b, hb, -⟩ | ⟨-, hX⟩
    · rw [hu.2] at hb; exact absurd hb (by simp)
    · exact hX
  -- lower bound: every undiscounted member of HS contributes a B-descendant
  have h1 : (HS \ D).card ≤ weight B M := by
    apply R.count_le_weight
    intro u hu
    rw [Finset.mem_sdiff, hD, Finset.mem_filter, not_and] at hu
    rcases hHS u hu.1 with ⟨b, hb, hBb⟩ | ⟨hn, -⟩
    · exact ⟨b, hBb, hb⟩
    · exact absurd hn (hu.2 hu.1)
  -- upper bound: counted non-B votes come from X \ D
  have h2 : M.card ≤ weight B M + (X \ D).card := by
    apply R.card_le_weight_add
    intro u b hb hnB
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rcases hprov u b hb hnB with hH | hX
      · rcases hHS u hH with ⟨b', hb', hBb'⟩ | ⟨hn, -⟩
        · have hbb : b = b' := by rw [hb] at hb'; exact Option.some.inj hb'
          exact absurd (show B ≤ b by rw [hbb]; exact hBb') hnB
        · rw [hb] at hn; exact absurd hn (by simp)
      · exact hX
    · rw [hD, Finset.mem_filter]
      rintro ⟨-, hn⟩
      rw [hb] at hn
      exact absurd hn (by simp)
  -- cardinal arithmetic: |X| < |HS| forces a strict majority
  have hcard1 : (HS \ D).card = HS.card - D.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hDsubH]
  have hcard2 : (X \ D).card = X.card - D.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hDsubX]
  have hDH : D.card ≤ HS.card := Finset.card_le_card hDsubH
  have hDX : D.card ≤ X.card := Finset.card_le_card hDsubX
  have hmaj : M.card < 2 * weight B M := by omega
  exact lemma3 hmaj (R.fc_ghost V s)

end RLMDGhost
