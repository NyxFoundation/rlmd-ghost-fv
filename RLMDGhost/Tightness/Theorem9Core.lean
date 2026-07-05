import RLMDGhost.Tightness.Witness

/-!
# Theorem 9 — the reorg computation

The mathematical heart of Theorem 9 (RLMD-GHOST is not `τ`-reorg-resilient for
`1 ≤ τ < η`): in the paper's adversarial execution, at slot `η + 1` the honest
proposal `bC` (extending `bA`) is *reorged out* — the RLMD fork choice of the
honest majority's view outputs `bB` instead.

This file verifies that fork-choice computation over the concrete witness layer
(`RLMDGhost.Tightness.Witness`), for `n = 11`, `m = 5`, at the reorg slot
`s = η + 1` with expiry window `η ≥ 2`:

* validator `0` (`v1`, adversary) broadcasts a late slot-`η` vote for `bB`;
* validators `1, 2` (`v2, v3`, corrupted after the slot-`η` voting round)
  equivocate at slot `η` (`{bC, bB}`), so they are discounted;
* validators `3–6` (the honest remainder of `V2`) have their latest counted
  vote `bC` (from slot `η`);
* validators `7–10` (`V3`, asleep since slot 1) have their latest counted vote
  `bB` — from slot 1, still inside the expiry window `[1, η]`.

Counted votes: `bB` from `{0, 7, 8, 9, 10}` (weight 5), `bC` (the `bA` branch)
from `{3, 4, 5, 6}` (weight 4). Since `5 > 4`, the GHOST fork choice descends to
`bB`, so the honest `bC` is not canonical — the reorg. `fcV_reorg` is that
computation; `not_bC_le_reorg` is the reorg conclusion.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-- The 11 validators of the Theorem 9 execution. -/
abbrev V9 : Type := Fin 11

/-- The vote table as seen in a slot-`(η + 1)` view: the votes each validator is
observed to have cast at each past slot, after the adversary's late slot-`η`
`bB` votes have been delivered. -/
def tab9 (η : ℕ) (u : V9) (u' : Slot) : Finset Blk :=
  if u.val = 0 then (if u' = η then {bB} else ∅)
  else if u.val ≤ 2 then
    (if u' = 1 then {bA} else if u' = η then {bC, bB}
     else if 2 ≤ u' ∧ u' < η then {bC} else ∅)
  else if u.val ≤ 6 then
    (if u' = 1 then {bA} else if 2 ≤ u' ∧ u' ≤ η then {bC} else ∅)
  else (if u' = 1 then {bB} else ∅)

/-- The honest majority's effective view at the reorg slot: every block is seen
(`bC` proposal merged), carrying `tab9`. -/
def view9 (η : ℕ) : Vw V9 := (({gen, bA, bB, bC} : Finset Blk), tab9 η)

/-- The counted vote of each validator at slot `η + 1`, computed. -/
def expected9 (u : V9) : Option Blk :=
  if u.val = 0 then some bB
  else if u.val ≤ 2 then none
  else if u.val ≤ 6 then some bC
  else some bB

theorem view9_fst (η : ℕ) : (view9 η).1 = ({gen, bA, bB, bC} : Finset Blk) := rfl

theorem okBlk_bA_view9 (η : ℕ) : okBlk (view9 η).1 bA := by rw [view9_fst]; decide
theorem okBlk_bB_view9 (η : ℕ) : okBlk (view9 η).1 bB := by rw [view9_fst]; decide
theorem okBlk_bC_view9 (η : ℕ) : okBlk (view9 η).1 bC := by rw [view9_fst]; decide

/-- Membership in the slot-`(η + 1)` candidate set. -/
theorem mem_cand9 {η : ℕ} {u : V9} {u' : ℕ} :
    u' ∈ cand (tab9 η u) η (η + 1) ↔ 1 ≤ u' ∧ u' ≤ η ∧ tab9 η u u' ≠ ∅ := by
  rw [mem_cand]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩

/-- Every candidate slot is `≤ η` (the top of the expiry window). -/
theorem cand9_le {η : ℕ} {u : V9} : ∀ u' ∈ cand (tab9 η u) η (η + 1), u' ≤ η :=
  fun _ hu' => (mem_cand9.mp hu').2.1

/-! ## The counted vote of each validator class -/

theorem voteOf_adv {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : u.val = 0) :
    voteOfV (view9 η) η (η + 1) u = some bB := by
  unfold voteOfV
  have hTη : tab9 η u η = {bB} := by unfold tab9; rw [if_pos h, if_pos rfl]
  refine voteOf1_eq_some ?_ cand9_le hTη (okBlk_bB_view9 η)
  exact mem_cand9.mpr ⟨by omega, le_rfl, by rw [hTη]; simp⟩

theorem voteOf_equiv {η : ℕ} (hη : 2 ≤ η) {u : V9} (h1 : 1 ≤ u.val) (h2 : u.val ≤ 2) :
    voteOfV (view9 η) η (η + 1) u = none := by
  unfold voteOfV
  have hne : u.val ≠ 0 := by omega
  have hTη : tab9 η u η = {bC, bB} := by
    unfold tab9
    rw [if_neg hne, if_pos h2, if_neg (by omega : ¬ η = 1), if_pos rfl]
  refine voteOf1_eq_none (mem_cand9.mpr ⟨by omega, le_rfl, by rw [hTη]; decide⟩)
    cand9_le ?_
  intro b hab
  obtain ⟨hb, -⟩ := hab
  have hb2 : tab9 η u η = {b} := hb
  rw [hTη] at hb2
  have hc : ({bC, bB} : Finset Blk).card = 1 := by rw [hb2]; simp
  simp at hc

theorem voteOf_v2 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h1 : 3 ≤ u.val) (h2 : u.val ≤ 6) :
    voteOfV (view9 η) η (η + 1) u = some bC := by
  unfold voteOfV
  have hne : u.val ≠ 0 := by omega
  have hle2 : ¬ u.val ≤ 2 := by omega
  have hTη : tab9 η u η = {bC} := by
    unfold tab9
    rw [if_neg hne, if_neg hle2, if_pos h2, if_neg (by omega : ¬ η = 1),
      if_pos (by omega : 2 ≤ η ∧ η ≤ η)]
  refine voteOf1_eq_some ?_ cand9_le hTη (okBlk_bC_view9 η)
  exact mem_cand9.mpr ⟨by omega, le_rfl, by rw [hTη]; decide⟩

theorem voteOf_v3 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : 7 ≤ u.val) :
    voteOfV (view9 η) η (η + 1) u = some bB := by
  unfold voteOfV
  have hne : u.val ≠ 0 := by omega
  have hle2 : ¬ u.val ≤ 2 := by omega
  have hle6 : ¬ u.val ≤ 6 := by omega
  have hT1 : tab9 η u 1 = {bB} := by
    unfold tab9; rw [if_neg hne, if_neg hle2, if_neg hle6, if_pos rfl]
  -- for V3, only slot 1 is nonempty in-window, so it is the max candidate
  have hmax : ∀ u' ∈ cand (tab9 η u) η (η + 1), u' ≤ 1 := by
    intro u' hu'
    obtain ⟨h1', -, hne'⟩ := mem_cand9.mp hu'
    by_contra hlt
    apply hne'
    unfold tab9
    rw [if_neg hne, if_neg hle2, if_neg hle6, if_neg (by omega : ¬ u' = 1)]
  refine voteOf1_eq_some ?_ hmax hT1 (okBlk_bB_view9 η)
  exact mem_cand9.mpr ⟨le_rfl, by omega, by rw [hT1]; decide⟩

/-- The counted vote of every validator, packaged. -/
theorem voteOfV_eq_expected {η : ℕ} (hη : 2 ≤ η) (u : V9) :
    voteOfV (view9 η) η (η + 1) u = expected9 u := by
  unfold expected9
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf_adv hη h0]
  · rw [if_neg h0]
    by_cases h2 : u.val ≤ 2
    · rw [if_pos h2, voteOf_equiv hη (by omega) h2]
    · rw [if_neg h2]
      by_cases h6 : u.val ≤ 6
      · rw [if_pos h6, voteOf_v2 hη (by omega) h6]
      · rw [if_neg h6, voteOf_v3 hη (by omega)]

/-! ## The weights and the reorg -/

theorem weight_bB_view9 {η : ℕ} (hη : 2 ≤ η) :
    weight bB (votesV (view9 η) η (η + 1)) = 5 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (view9 η) η (η + 1) u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expected9 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr
    intro u _
    rw [voteOfV_eq_expected hη u]
  rw [this]; decide

theorem weight_bA_view9 {η : ℕ} (hη : 2 ≤ η) :
    weight bA (votesV (view9 η) η (η + 1)) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (view9 η) η (η + 1) u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expected9 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr
    intro u _
    rw [voteOfV_eq_expected hη u]
  rw [this]; decide

/-- **The reorg.** At slot `η + 1` the RLMD fork choice of the honest majority's
view outputs `bB`: the descendants of `bA` (weight 4) are outvoted by `bB`
(weight 5), so the GHOST descent leaves the `bA` branch. -/
theorem fcV_reorg {η : ℕ} (hη : 2 ≤ η) : fcV (view9 η) η (η + 1) = bB := by
  unfold fcV
  rw [if_neg, if_pos (okBlk_bB_view9 η)]
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨?_, okBlk_bB_view9 η⟩
  rw [weight_bA_view9 hη, weight_bB_view9 hη]
  omega

/-- The honest proposal `bC` is **reorged**: it is not a prefix of the slot-`η+1`
fork-choice output `bB`. -/
theorem not_bC_le_reorg {η : ℕ} (hη : 2 ≤ η) : ¬ bC ≤ fcV (view9 η) η (η + 1) := by
  rw [fcV_reorg hη]
  decide

/-! ## The pre-reorg state: the honest chain is `bC` at the pivot slot

Complementing the reorg at slot `η + 1`, the same view yields the honest
proposal `bC` as the canonical chain at the pivot slot `2`: there the only
counted votes are the slot-1 votes, with the `bA` branch (`{1,…,6}`, weight 6)
outvoting `bB` (`{7,…,10}`, weight 4), so the GHOST descent follows `bA` and,
`bC` being the only seen block extending it, outputs `bC`. Together with
`fcV_reorg`, this shows the canonical chain is `bC` at slot 2 and flips to `bB`
at slot `η + 1` — the reorg dynamics. -/

/-- The counted vote of each validator at slot `2` (only slot-1 votes are in
window). -/
def expected2 (u : V9) : Option Blk :=
  if u.val = 0 then none
  else if u.val ≤ 6 then some bA
  else some bB

theorem voteOf_slot2_low {η : ℕ} (hη : 2 ≤ η) {u : V9} (h1 : 1 ≤ u.val) (h2 : u.val ≤ 6) :
    voteOfV (view9 η) η 2 u = some bA := by
  unfold voteOfV
  have hne : u.val ≠ 0 := by omega
  have hT1 : tab9 η u 1 = {bA} := by
    unfold tab9
    rw [if_neg hne]
    by_cases hle2 : u.val ≤ 2
    · rw [if_pos hle2, if_pos rfl]
    · rw [if_neg hle2, if_pos (by omega : u.val ≤ 6), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tab9 η u) η 2, u' ≤ 1 := by
    intro u' hu'
    rw [mem_cand] at hu'; omega
  refine voteOf1_eq_some ?_ hmax hT1 (okBlk_bA_view9 η)
  rw [mem_cand]
  exact ⟨by omega, by omega, by show tab9 η u 1 ≠ ∅; rw [hT1]; decide⟩

theorem voteOf_slot2_high {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : 7 ≤ u.val) :
    voteOfV (view9 η) η 2 u = some bB := by
  unfold voteOfV
  have hne : u.val ≠ 0 := by omega
  have hle2 : ¬ u.val ≤ 2 := by omega
  have hle6 : ¬ u.val ≤ 6 := by omega
  have hT1 : tab9 η u 1 = {bB} := by
    unfold tab9; rw [if_neg hne, if_neg hle2, if_neg hle6, if_pos rfl]
  have hmax : ∀ u' ∈ cand (tab9 η u) η 2, u' ≤ 1 := by
    intro u' hu'
    rw [mem_cand] at hu'; omega
  refine voteOf1_eq_some ?_ hmax hT1 (okBlk_bB_view9 η)
  rw [mem_cand]
  exact ⟨by omega, by omega, by show tab9 η u 1 ≠ ∅; rw [hT1]; decide⟩

theorem voteOf_slot2_adv {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : u.val = 0) :
    voteOfV (view9 η) η 2 u = none := by
  unfold voteOfV
  apply voteOf1_eq_none_of_empty
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u' hu'
  rw [mem_cand] at hu'
  obtain ⟨h1, h2, h3⟩ := hu'
  apply h3
  show tab9 η u u' = ∅
  unfold tab9; rw [if_pos h, if_neg (by omega : ¬ u' = η)]

theorem voteOfV_eq_expected2 {η : ℕ} (hη : 2 ≤ η) (u : V9) :
    voteOfV (view9 η) η 2 u = expected2 u := by
  unfold expected2
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf_slot2_adv hη h0]
  · rw [if_neg h0]
    by_cases h6 : u.val ≤ 6
    · rw [if_pos h6, voteOf_slot2_low hη (by omega) h6]
    · rw [if_neg h6, voteOf_slot2_high hη (by omega)]

theorem weight_bA_slot2 {η : ℕ} (hη : 2 ≤ η) :
    weight bA (votesV (view9 η) η 2) = 6 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (view9 η) η 2 u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expected2 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected2 hη u]
  rw [this]; decide

theorem weight_bB_slot2 {η : ℕ} (hη : 2 ≤ η) :
    weight bB (votesV (view9 η) η 2) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (view9 η) η 2 u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expected2 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected2 hη u]
  rw [this]; decide

/-- **The pre-reorg state.** At the pivot slot `2` the honest proposal `bC` is
canonical: the `bA` branch (weight 6) outvotes `bB` (weight 4), so the GHOST
descent follows `bA` to its only seen extension `bC`. -/
theorem fcV_honest_pivot {η : ℕ} (hη : 2 ≤ η) : fcV (view9 η) η 2 = bC := by
  unfold fcV
  rw [if_pos, if_pos (okBlk_bC_view9 η)]
  refine ⟨okBlk_bA_view9 η, ?_⟩
  rw [weight_bA_slot2 hη, weight_bB_slot2 hη]
  rintro ⟨hlt, -⟩
  omega

end Tightness

end RLMDGhost
