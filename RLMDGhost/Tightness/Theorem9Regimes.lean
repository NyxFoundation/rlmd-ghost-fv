import RLMDGhost.Tightness.Theorem9Core

/-!
# Theorem 9 — the fork choice at every slot

`Theorem9Core` verified the fork choice at the two endpoints of the reorg (`bC`
at the pivot slot 2, `bB` at the reorg slot `η + 1`). This file extends that to
the whole timeline over a table `tabF` that carries the post-reorg tail, so the
canonical chain is pinned at *every* slot:

* `bC` throughout `[2, η]` (the honest chain, before the reorg);
* `bB` throughout `[η + 1, ∞)` (after the reorg, the flip is sticky — everyone
  votes `bB` and, by latest-message counting, `bB` dominates for good).

`tabF` extends `tab9` (which it equals on the window `[1, η]`) with slot-0
genesis votes and a `bB` tail from slot `η + 1` on. The tail computation uses
the general latest-message lemma `voteOf1_at_prev`: at any tail slot every
validator's counted vote is its slot-`(s−1)` `bB` vote.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-- The full timeline table: `tab9` on `[1, η]`, genesis at slot 0, and a `bB`
tail from slot `η + 1` on (everyone votes `bB` after the reorg). -/
def tabF (η : ℕ) (u : V9) (u' : Slot) : Finset Blk :=
  if η + 1 ≤ u' then {bB}
  else if u' = 0 then {gen}
  else tab9 η u u'

/-- The common view over the full timeline (all four blocks seen). -/
def viewF (η : ℕ) : Vw V9 := (({gen, bA, bB, bC} : Finset Blk), tabF η)

theorem viewF_fst (η : ℕ) : (viewF η).1 = ({gen, bA, bB, bC} : Finset Blk) := rfl

theorem okBlk_bA_viewF (η : ℕ) : okBlk (viewF η).1 bA := by rw [viewF_fst]; decide
theorem okBlk_bB_viewF (η : ℕ) : okBlk (viewF η).1 bB := by rw [viewF_fst]; decide
theorem okBlk_bC_viewF (η : ℕ) : okBlk (viewF η).1 bC := by rw [viewF_fst]; decide
theorem okBlk_gen_viewF (η : ℕ) : okBlk (viewF η).1 gen := by rw [viewF_fst]; decide

/-- `tabF` agrees with `tab9` on the expiry window `[1, η]`. -/
theorem tabF_eq_tab9 {η : ℕ} {u : V9} {u' : ℕ} (h1 : 1 ≤ u') (h2 : u' ≤ η) :
    tabF η u u' = tab9 η u u' := by
  unfold tabF
  rw [if_neg (Nat.not_le.mpr (Nat.lt_succ_of_le h2)),
    if_neg (Nat.one_le_iff_ne_zero.mp h1)]

/-- `tabF` at a tail slot: everyone votes `bB`. -/
theorem tabF_tail {η : ℕ} {u : V9} {u' : ℕ} (h : η + 1 ≤ u') :
    tabF η u u' = {bB} := by
  unfold tabF; rw [if_pos h]

/-! ## The tail regime: the reorg is sticky -/

/-- At any post-reorg slot `s ≥ η + 2`, every validator's counted vote is its
slot-`(s−1)` `bB` vote (latest-message). -/
theorem voteOf_tail {η s : ℕ} (hη : 2 ≤ η) (hs : η + 2 ≤ s) (u : V9) :
    voteOfV (viewF η) η s u = some bB := by
  have hs1 : 1 ≤ s := by omega
  unfold voteOfV
  refine voteOf1_at_prev hs1 (by omega) ?_ (okBlk_bB_viewF η)
  show tabF η u (s - 1) = {bB}
  exact tabF_tail (Nat.le_sub_of_add_le hs)

theorem weight_bB_tail {η s : ℕ} (hη : 2 ≤ η) (hs : η + 2 ≤ s) :
    weight bB (votesV (viewF η) η s) = 11 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η s u = some b ∧ bB ≤ b) = Finset.univ := by
    rw [Finset.filter_eq_self]
    intro u _
    exact ⟨bB, voteOf_tail hη hs u, le_refl _⟩
  rw [this]; decide

theorem weight_bA_tail {η s : ℕ} (hη : 2 ≤ η) (hs : η + 2 ≤ s) :
    weight bA (votesV (viewF η) η s) = 0 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η s u = some b ∧ bA ≤ b) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro u _
    rw [voteOf_tail hη hs u]
    rintro ⟨b, hb, hab⟩
    rw [Option.some.injEq] at hb
    exact absurd (hb ▸ hab) (by decide)
  rw [this]; simp

/-- **The reorg is sticky.** At every slot `s ≥ η + 2` the canonical chain stays
`bB`: everyone votes `bB` (weight 11) and the `bA` branch has weight 0, so the
GHOST descent goes to `bB`. -/
theorem fcV_tail {η s : ℕ} (hη : 2 ≤ η) (hs : η + 2 ≤ s) : fcV (viewF η) η s = bB := by
  unfold fcV
  rw [if_neg, if_pos (okBlk_bB_viewF η)]
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨?_, okBlk_bB_viewF η⟩
  rw [weight_bA_tail hη hs, weight_bB_tail hη hs]
  omega

/-! ## The mid regime: the honest chain `bC` through `[3, η]` -/

/-- `{1,…,6}` (honest `V2` and the not-yet-corrupt `v2, v3`) have their latest
counted vote `bC` at every slot `s ∈ [3, η]`. -/
theorem voteOf_mid_v2 {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) {u : V9}
    (h1 : 1 ≤ u.val) (h2 : u.val ≤ 6) : voteOfV (viewF η) η s u = some bC := by
  have hs1 : 1 ≤ s := by omega
  unfold voteOfV
  refine voteOf1_at_prev hs1 (by omega) ?_ (okBlk_bC_viewF η)
  show tabF η u (s - 1) = {bC}
  rw [tabF_eq_tab9 (u' := s - 1) (by omega) (by omega)]
  unfold tab9
  rw [if_neg (by omega : ¬ u.val = 0)]
  by_cases hle2 : u.val ≤ 2
  · rw [if_pos hle2, if_neg (by omega : ¬ s - 1 = 1), if_neg (by omega : ¬ s - 1 = η),
      if_pos (by omega : 2 ≤ s - 1 ∧ s - 1 < η)]
  · rw [if_neg hle2, if_pos h2, if_neg (by omega : ¬ s - 1 = 1),
      if_pos (by omega : 2 ≤ s - 1 ∧ s - 1 ≤ η)]

/-- `V3` (asleep since slot 1) contributes its stale slot-1 `bB` vote at every
slot `s ∈ [3, η]` — still inside the expiry window `[s−η, s−1]`. -/
theorem voteOf_mid_v3 {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) {u : V9}
    (h : 7 ≤ u.val) : voteOfV (viewF η) η s u = some bB := by
  unfold voteOfV
  have hT1 : tabF η u 1 = {bB} := by
    rw [tabF_eq_tab9 (u' := 1) (by omega) (by omega)]
    unfold tab9
    rw [if_neg (by omega : ¬ u.val = 0), if_neg (by omega : ¬ u.val ≤ 2),
      if_neg (by omega : ¬ u.val ≤ 6), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tabF η u) η s, u' ≤ 1 := by
    intro u' hu'
    rw [mem_cand] at hu'
    obtain ⟨hlt, hwin, hne⟩ := hu'
    by_contra hgt
    apply hne
    rw [tabF_eq_tab9 (u' := u') (by omega) (by omega)]
    unfold tab9
    rw [if_neg (by omega : ¬ u.val = 0), if_neg (by omega : ¬ u.val ≤ 2),
      if_neg (by omega : ¬ u.val ≤ 6), if_neg (by omega : ¬ u' = 1)]
  refine voteOf1_eq_some ?_ hmax hT1 (okBlk_bB_viewF η)
  rw [mem_cand]; refine ⟨by omega, by omega, ?_⟩
  show tabF η u 1 ≠ ∅; rw [hT1]; decide

/-- The adversary contributes only a slot-0 genesis vote in `[3, η]` (its late
`bB` is at slot `η`, out of window). -/
theorem voteOf_mid_adv {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) {u : V9}
    (h : u.val = 0) : voteOfV (viewF η) η s u = some gen := by
  unfold voteOfV
  have hT0 : tabF η u 0 = {gen} := by unfold tabF; rw [if_neg (by omega), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tabF η u) η s, u' ≤ 0 := by
    intro u' hu'
    rw [mem_cand] at hu'
    obtain ⟨hlt, hwin, hne⟩ := hu'
    by_contra hgt
    apply hne
    rw [tabF_eq_tab9 (u' := u') (by omega) (by omega)]
    unfold tab9
    rw [if_pos h, if_neg (by omega : ¬ u' = η)]
  refine voteOf1_eq_some ?_ hmax hT0 (okBlk_gen_viewF η)
  rw [mem_cand]; refine ⟨by omega, by omega, ?_⟩
  show tabF η u 0 ≠ ∅; rw [hT0]; decide

/-- The counted vote of each validator in `[3, η]`. -/
def expectedMid (u : V9) : Option Blk :=
  if u.val = 0 then some gen else if u.val ≤ 6 then some bC else some bB

theorem voteOfV_eq_expectedMid {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) (u : V9) :
    voteOfV (viewF η) η s u = expectedMid u := by
  unfold expectedMid
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf_mid_adv hs3 hsη h0]
  · rw [if_neg h0]
    by_cases h6 : u.val ≤ 6
    · rw [if_pos h6, voteOf_mid_v2 hs3 hsη (by omega) h6]
    · rw [if_neg h6, voteOf_mid_v3 hs3 hsη (by omega)]

theorem weight_bA_mid {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) :
    weight bA (votesV (viewF η) η s) = 6 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η s u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expectedMid u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expectedMid hs3 hsη u]
  rw [this]; decide

theorem weight_bB_mid {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) :
    weight bB (votesV (viewF η) η s) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η s u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expectedMid u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expectedMid hs3 hsη u]
  rw [this]; decide

/-- **The honest chain holds through `[3, η]`.** At every such slot the honest
`bA` branch (weight 6, carried by `{1,…,6}`'s `bC` votes) outvotes `bB`
(weight 4, `V3`'s stale slot-1 votes), so the GHOST descent reaches `bC`. -/
theorem fcV_mid {η s : ℕ} (hs3 : 3 ≤ s) (hsη : s ≤ η) : fcV (viewF η) η s = bC := by
  unfold fcV
  rw [if_pos, if_pos (okBlk_bC_viewF η)]
  refine ⟨okBlk_bA_viewF η, ?_⟩
  rw [weight_bA_mid hs3 hsη, weight_bB_mid hs3 hsη]
  rintro ⟨hlt, -⟩
  omega

end Tightness

end RLMDGhost
