import RLMDGhost.Tightness.Witness

/-!
# Theorem 11 — RLMD-GHOST is not `(τ, π)`-asynchrony-resilient for `τ > π ≥ max(η, 2)`

The tightness of Theorem 8: a `(η, η−1)`-tpa is tolerated, but a length-`η` tpa
(`π = η`) is not. In the `(∞, η)`-compliant witness, a temporary period of
asynchrony of length `η` lets *all* votes for the honest chain expire, after
which the adversary's genesis-extension `bB` — proposed inside the tpa — is
tiebreak-selected and reorgs the honest proposal.

The fork-choice tiebreak in RLMD-GHOST is adversarial (`GhostSelects.choice_max`
compares with `≤`, so either child may be chosen on a tie). This file provides
`fcVB`, the tiebreak-toward-`bB` fork choice, mirroring the witness `fcV`
(tiebreak-toward-`bA`); both satisfy `GhostSelects` and the §2 consistency
property. `fcVB` is what the Theorem 11 execution uses.
-/

namespace RLMDGhost

namespace Tightness

open Blk

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- GHOST on the four-block tree with the genesis-fork tiebreak toward `bB`:
`bB` wins unless strictly outweighed by `bA`. -/
noncomputable def fcVB (W : Vw V) (η s : ℕ) : Blk :=
  if okBlk W.1 bB ∧
      ¬(weight bB (votesV W η s) < weight bA (votesV W η s) ∧ okBlk W.1 bA) then bB
  else if okBlk W.1 bA then (if okBlk W.1 bC then bC else bA) else gen

/-- The tiebreak-toward-`bB` fork choice satisfies the GHOST-descent property. -/
theorem fcVB_ghost (W : Vw V) (η s : ℕ) :
    GhostSelects (votesV W η s) (fcVB W η s) := by
  classical
  constructor
  · intro P B' B'' hc' hc'' hle
    rcases covBy_cases hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases covBy_cases hc'' with ⟨hP2, rfl⟩ | ⟨hP2, rfl⟩ | ⟨hP2, rfl⟩
    · exact le_refl _
    · -- B' = bA, B'' = bB: descent went to bB; need w(bA) ≤ w(bB)
      have hout : fcVB W η s = bB := le_bB_iff.mp hle
      by_cases hB : okBlk W.1 bB ∧
          ¬(weight bB (votesV W η s) < weight bA (votesV W η s) ∧ okBlk W.1 bA)
      · by_cases hA : okBlk W.1 bA
        · exact Nat.le_of_not_lt fun hlt => hB.2 ⟨hlt, hA⟩
        · rw [weight_eq_zero_of_not_ok hA]; exact Nat.zero_le _
      · unfold fcVB at hout
        rw [if_neg hB] at hout
        split_ifs at hout <;> exact absurd hout (by decide)
    · exact absurd hP2 (by decide)
    · -- B' = bB, B'' = bA: descent went to the bA side; need w(bB) ≤ w(bA)
      have hout : fcVB W η s = bA ∨ fcVB W η s = bC := le_bA_iff.mp hle
      have hnB : ¬(okBlk W.1 bB ∧
          ¬(weight bB (votesV W η s) < weight bA (votesV W η s) ∧ okBlk W.1 bA)) := by
        intro hB
        unfold fcVB at hout
        rw [if_pos hB] at hout
        rcases hout with hout | hout <;> exact absurd hout (by decide)
      rw [not_and_or, not_not] at hnB
      rcases hnB with hnB | hnB
      · rw [weight_eq_zero_of_not_ok hnB]; exact Nat.zero_le _
      · exact le_of_lt hnB.1
    · exact le_refl _
    · exact absurd hP2 (by decide)
    · exact absurd hP2 (by decide)
    · exact absurd hP2 (by decide)
    · exact le_refl _
  · intro Y hc
    rcases covBy_cases hc with ⟨hP, rfl⟩ | ⟨hP, rfl⟩ | ⟨hP, rfl⟩
    · -- output gen, cover bA
      unfold fcVB at hP
      by_cases hB : okBlk W.1 bB ∧
          ¬(weight bB (votesV W η s) < weight bA (votesV W η s) ∧ okBlk W.1 bA)
      · rw [if_pos hB] at hP; exact absurd hP (by decide)
      · rw [if_neg hB] at hP
        by_cases hA : okBlk W.1 bA
        · rw [if_pos hA] at hP; split_ifs at hP <;> exact absurd hP (by decide)
        · exact weight_eq_zero_of_not_ok hA
    · -- output gen, cover bB
      unfold fcVB at hP
      by_cases hB : okBlk W.1 bB ∧
          ¬(weight bB (votesV W η s) < weight bA (votesV W η s) ∧ okBlk W.1 bA)
      · rw [if_pos hB] at hP; exact absurd hP (by decide)
      · rw [if_neg hB] at hP
        by_cases hA : okBlk W.1 bA
        · rw [if_pos hA] at hP; split_ifs at hP <;> exact absurd hP (by decide)
        · rw [not_and_or, not_not] at hB
          rcases hB with hB | hB
          · exact weight_eq_zero_of_not_ok hB
          · exact absurd hB.2 hA
    · -- output bA, cover bC
      unfold fcVB at hP
      by_cases hB : okBlk W.1 bB ∧
          ¬(weight bB (votesV W η s) < weight bA (votesV W η s) ∧ okBlk W.1 bA)
      · rw [if_pos hB] at hP; exact absurd hP (by decide)
      · rw [if_neg hB] at hP
        by_cases hA : okBlk W.1 bA
        · rw [if_pos hA] at hP
          by_cases hC : okBlk W.1 bC
          · rw [if_pos hC] at hP; exact absurd hP (by decide)
          · exact weight_eq_zero_of_not_ok hC
        · rw [if_neg hA] at hP; exact absurd hP (by decide)

/-! ## The 3-validator tpa execution -/

/-- The three validators `v1, v2, v3`. -/
abbrev V3 : Type := Fin 3

/-- The vote table. Honest chain `bA` proposed at the pivot slot 2; `v0` (`v1`)
votes `bA` at slot 2 then sleeps through the tpa; `v1` (`v2`) always awake,
votes `bA`; `v2` (`v3`), asleep, wakes and proposes/votes the genesis-extension
`bB` from slot `2 + η` on. -/
def tab11 (η : ℕ) (u : V3) (u' : ℕ) : Finset Blk :=
  if u' ≤ 1 then {gen}
  else if u.val = 0 then (if u' = 2 then {bA} else ∅)
  else if u.val = 1 then {bA}
  else (if 2 + η ≤ u' then {bB} else ∅)

/-- The common view (genesis, `bA`, `bB` seen; `bC` never appears). -/
def view11 (η : ℕ) : Vw V3 := (({gen, bA, bB} : Finset Blk), tab11 η)

theorem view11_fst (η : ℕ) : (view11 η).1 = ({gen, bA, bB} : Finset Blk) := rfl

theorem okBlk_bA_view11 (η : ℕ) : okBlk (view11 η).1 bA := by rw [view11_fst]; decide
theorem okBlk_bB_view11 (η : ℕ) : okBlk (view11 η).1 bB := by rw [view11_fst]; decide

/-! ### The counted votes at the reorg slot `η + 3` -/

/-- `v1` (index 1) votes `bA`; its latest slot-`(η+2)` vote is counted. -/
theorem voteOf11_v1 {η : ℕ} (hη : 2 ≤ η) {u : V3} (h : u.val = 1) :
    voteOfV (view11 η) η (η + 3) u = some bA := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bA_view11 η)
  show tab11 η u (η + 3 - 1) = {bA}
  have he : η + 3 - 1 = η + 2 := by omega
  rw [he]; unfold tab11
  rw [if_neg (by omega : ¬ η + 2 ≤ 1), if_neg (by omega : ¬ u.val = 0), if_pos h]

/-- `v2` (index 2) votes `bB` from slot `η + 2`; its latest such vote is counted. -/
theorem voteOf11_v2 {η : ℕ} (hη : 2 ≤ η) {u : V3} (h : u.val = 2) :
    voteOfV (view11 η) η (η + 3) u = some bB := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bB_view11 η)
  show tab11 η u (η + 3 - 1) = {bB}
  have he : η + 3 - 1 = η + 2 := by omega
  rw [he]; unfold tab11
  rw [if_neg (by omega : ¬ η + 2 ≤ 1), if_neg (by omega : ¬ u.val = 0),
    if_neg (by omega : ¬ u.val = 1), if_pos (by omega : 2 + η ≤ η + 2)]

/-- `v0` (index 0), asleep through the tpa, has its slot-2 `bA` vote *expired* at
slot `η + 3`: no vote of `v0` lies in the window `[3, η + 2]`. -/
theorem voteOf11_v0 {η : ℕ} (hη : 2 ≤ η) {u : V3} (h : u.val = 0) :
    voteOfV (view11 η) η (η + 3) u = none := by
  unfold voteOfV
  apply voteOf1_eq_none_of_empty
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u' hu'
  rw [mem_cand] at hu'
  obtain ⟨hlt, hwin, hne⟩ := hu'
  apply hne
  show tab11 η u u' = ∅
  unfold tab11
  rw [if_neg (by omega : ¬ u' ≤ 1), if_pos h, if_neg (by omega : ¬ u' = 2)]

def expected11 (u : V3) : Option Blk :=
  if u.val = 0 then none else if u.val = 1 then some bA else some bB

theorem voteOfV_eq_expected11 {η : ℕ} (hη : 2 ≤ η) (u : V3) :
    voteOfV (view11 η) η (η + 3) u = expected11 u := by
  unfold expected11
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf11_v0 hη h0]
  · rw [if_neg h0]
    by_cases h1 : u.val = 1
    · rw [if_pos h1, voteOf11_v1 hη h1]
    · rw [if_neg h1, voteOf11_v2 hη (by omega)]

theorem weight_bA_reorg11 {η : ℕ} (hη : 2 ≤ η) :
    weight bA (votesV (view11 η) η (η + 3)) = 1 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V3 =>
      ∃ b, voteOfV (view11 η) η (η + 3) u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V3 => ∃ b, expected11 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected11 hη u]
  rw [this]; decide

theorem weight_bB_reorg11 {η : ℕ} (hη : 2 ≤ η) :
    weight bB (votesV (view11 η) η (η + 3)) = 1 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V3 =>
      ∃ b, voteOfV (view11 η) η (η + 3) u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V3 => ∃ b, expected11 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected11 hη u]
  rw [this]; decide

/-- **The asynchrony reorg.** At slot `η + 3` the fork choice outputs `bB`: the
honest `bA` and the adversarial genesis-extension `bB` are tied (weight 1 each,
`v0`'s `bA` having expired), and the adversarial tiebreak (`fcVB`) resolves to
`bB`, reorging the honest proposal. -/
theorem fcVB_reorg11 {η : ℕ} (hη : 2 ≤ η) : fcVB (view11 η) η (η + 3) = bB := by
  unfold fcVB
  rw [if_pos]
  refine ⟨okBlk_bB_view11 η, ?_⟩
  rw [weight_bA_reorg11 hη, weight_bB_reorg11 hη]
  rintro ⟨hlt, -⟩; omega

theorem not_bA_le_reorg11 {η : ℕ} (hη : 2 ≤ η) : ¬ bA ≤ fcVB (view11 η) η (η + 3) := by
  rw [fcVB_reorg11 hη]; decide

end Tightness

end RLMDGhost
