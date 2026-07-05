import RLMDGhost.Tightness.WitnessBase
import RLMDGhost.ProposeVoteMerge.Theorem1

/-!
# Theorem 4 — LMD-GHOST is not `τ`-dynamically-available for any finite `τ`

LMD-GHOST is RLMD-GHOST with `η = ∞`: votes never expire, so a validator's
*latest* vote counts forever. This lets the adversary keep an old minority vote
alive and, with a single corruption, flip the fork-choice majority and reorg the
honest chain — violating reorg resilience and hence dynamic availability.

The witness (`n = 5 = 2·2 + 1`, `V1 = {v0}` adversarial, `V2 = {v1,v2,v3}`,
`V3 = {v4}`): at the pivot slot 2 the adversary delivers the honest proposal
`bA` to `V2` and a conflicting `bB` to `V3`; `V2` votes `bA`, `v4` votes `bB`
then sleeps. `bA` is canonical while `V2`'s majority holds. Then `v0` corrupts
`v1`, and both vote `bB`: since `v4`'s `bB` never expired (`η = ∞`), `bB` now has
3 votes (`{v0, v1, v4}`) against `bA`'s 2 (`{v2, v3}`), so `bB` is canonical and
reorgs `bA`. `η = ∞` is modelled by an expiry window (`η = 5`) larger than the
finite horizon of the execution.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-- The five validators. `0 = v0` (adversary), `1 = v1` (corrupted at slot 3),
`2, 3 = v2, v3` (honest `V2` core), `4 = v4` (honest `V3`, asleep after slot 2). -/
abbrev V5 : Type := Fin 5

/-- The LMD vote table. `η = ∞` modelled by a large window. -/
def tab4 (u : V5) (u' : ℕ) : Finset Blk :=
  if u' ≤ 1 then {gen}
  else if u.val = 0 then (if 3 ≤ u' then {bB} else ∅)
  else if u.val = 1 then (if u' = 2 then {bA} else {bB})
  else if u.val ≤ 3 then {bA}
  else (if u' = 2 then {bB} else ∅)

/-- The common view. -/
def view4 : Vw V5 := (({gen, bA, bB} : Finset Blk), tab4)

theorem view4_fst : (view4).1 = ({gen, bA, bB} : Finset Blk) := rfl
theorem okBlk_bA_view4 : okBlk (view4).1 bA := by rw [view4_fst]; decide
theorem okBlk_bB_view4 : okBlk (view4).1 bB := by rw [view4_fst]; decide

/-! ### Counted votes at the reorg slot 4 (`η = 5`, no expiry) -/

/-- `v0` and `v1` (indices 0, 1) vote `bB` at slot 3; their latest vote is `bB`. -/
theorem voteOf4_bB3 {u : V5} (h : u.val = 0 ∨ u.val = 1) :
    voteOfV view4 5 4 u = some bB := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ okBlk_bB_view4
  show tab4 u (4 - 1) = {bB}
  rw [show (4 - 1) = 3 from rfl]; unfold tab4
  rcases h with h | h
  · rw [if_neg (by omega : ¬ (3:ℕ) ≤ 1), if_pos h, if_pos (by omega : (3:ℕ) ≤ 3)]
  · rw [if_neg (by omega : ¬ (3:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0), if_pos h,
      if_neg (by omega : ¬ (3:ℕ) = 2)]

/-- `v2, v3` (indices 2, 3) vote `bA`; their latest vote is `bA`. -/
theorem voteOf4_bA {u : V5} (h : u.val = 2 ∨ u.val = 3) :
    voteOfV view4 5 4 u = some bA := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ okBlk_bA_view4
  show tab4 u (4 - 1) = {bA}
  rw [show (4 - 1) = 3 from rfl]; unfold tab4
  rw [if_neg (by omega : ¬ (3:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0),
    if_neg (by omega : ¬ u.val = 1), if_pos (by omega : u.val ≤ 3)]

/-- `v4` (index 4), asleep since slot 2, has its slot-2 `bB` vote still counted
(`η = ∞`, never expires): it is the latest in the window `[0, 3]`. -/
theorem voteOf4_v4 {u : V5} (h : u.val = 4) : voteOfV view4 5 4 u = some bB := by
  unfold voteOfV
  have hT2 : tab4 u 2 = {bB} := by
    unfold tab4
    rw [if_neg (by omega : ¬ (2:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0),
      if_neg (by omega : ¬ u.val = 1), if_neg (by omega : ¬ u.val ≤ 3), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tab4 u) 5 4, u' ≤ 2 := by
    intro u' hu'
    rw [mem_cand] at hu'
    obtain ⟨hlt, hwin, hne⟩ := hu'
    by_contra hgt
    apply hne
    unfold tab4
    rw [if_neg (by omega : ¬ u' ≤ 1), if_neg (by omega : ¬ u.val = 0),
      if_neg (by omega : ¬ u.val = 1), if_neg (by omega : ¬ u.val ≤ 3),
      if_neg (by omega : ¬ u' = 2)]
  refine voteOf1_eq_some ?_ hmax hT2 okBlk_bB_view4
  rw [mem_cand]; refine ⟨by omega, by omega, ?_⟩
  show tab4 u 2 ≠ ∅; rw [hT2]; decide

def expected4 (u : V5) : Option Blk :=
  if u.val ≤ 1 then some bB else if u.val ≤ 3 then some bA else some bB

theorem voteOfV_eq_expected4 (u : V5) : voteOfV view4 5 4 u = expected4 u := by
  unfold expected4
  by_cases h1 : u.val ≤ 1
  · rw [if_pos h1, voteOf4_bB3 (by omega)]
  · rw [if_neg h1]
    by_cases h3 : u.val ≤ 3
    · rw [if_pos h3, voteOf4_bA (by omega)]
    · rw [if_neg h3, voteOf4_v4 (by omega)]

theorem weight_bA_reorg4 : weight bA (votesV view4 5 4) = 2 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V5 => ∃ b, voteOfV view4 5 4 u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V5 => ∃ b, expected4 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected4 u]
  rw [this]; decide

theorem weight_bB_reorg4 : weight bB (votesV view4 5 4) = 3 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V5 => ∃ b, voteOfV view4 5 4 u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V5 => ∃ b, expected4 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected4 u]
  rw [this]; decide

/-- **The LMD reorg.** At slot 4 the fork choice outputs `bB`: the never-expiring
`v4` vote plus the two corrupted votes give `bB` a strict majority (weight 3)
over `bA` (weight 2), reorging the honest chain. -/
theorem fcV_reorg4 : fcV view4 5 4 = bB := by
  unfold fcV
  rw [if_neg, if_pos okBlk_bB_view4]
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨?_, okBlk_bB_view4⟩
  rw [weight_bA_reorg4, weight_bB_reorg4]; omega

end Tightness

end RLMDGhost
