import RLMDGhost.Tightness.WitnessBase
import RLMDGhost.ProposeVoteMerge.Theorem1

/-!
# Theorem 4 — LMD-GHOST is not `τ`-dynamically-available for any finite `τ`

LMD-GHOST is RLMD-GHOST with `η = ∞`: votes never expire, so a validator's
*latest* vote counts forever. This lets the adversary keep an old minority vote
alive and, with a single corruption, flip the fork-choice majority and reorg the
honest chain — violating reorg resilience and hence dynamic availability.

The witness (`n = 7 = 2·3 + 1`, `V1 = {v0}` adversarial, `V2 = {v1,…,v4}`,
`V3 = {v5, v6}`): at the pivot slot 2 the adversary delivers the honest proposal
`bA` to `V2` and a conflicting `bB` to `V3`; `V2` votes `bA`, `v4` votes `bB`
then sleeps. `bA` is canonical while `V2`'s majority holds. Then `v0` corrupts
`v1`, and both vote `bB`: since `v4`'s `bB` never expired (`η = ∞`), `bB` now has
4 votes (`{v0, v1, v5, v6}`) against `bA`'s 3 (`{v2, v3, v4}`), so `bB` is canonical and
reorgs `bA`. `η = ∞` is modelled by an expiry window (`η = 7`) larger than the
finite horizon of the execution.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-- The five validators. `0 = v0` (adversary), `1 = v1` (corrupted at slot 3),
`2,3,4` (honest `V2` core), `5,6` (honest `V3`, asleep after slot 2). -/
abbrev V5 : Type := Fin 7

/-- The LMD vote table. `η = ∞` modelled by a large window. -/
def tab4 (u : V5) (u' : ℕ) : Finset Blk :=
  if u' ≤ 1 then {gen}
  else if u.val = 0 then (if 3 ≤ u' then {bB} else ∅)
  else if u.val = 1 then (if u' = 2 then {bA} else {bB})
  else if u.val ≤ 4 then {bA}
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
theorem voteOf4_bA {u : V5} (h : 2 ≤ u.val ∧ u.val ≤ 4) :
    voteOfV view4 5 4 u = some bA := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ okBlk_bA_view4
  show tab4 u (4 - 1) = {bA}
  rw [show (4 - 1) = 3 from rfl]; unfold tab4
  rw [if_neg (by omega : ¬ (3:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0),
    if_neg (by omega : ¬ u.val = 1), if_pos (by omega : u.val ≤ 4)]

/-- `v4` (index 4), asleep since slot 2, has its slot-2 `bB` vote still counted
(`η = ∞`, never expires): it is the latest in the window `[0, 3]`. -/
theorem voteOf4_v4 {u : V5} (h : 5 ≤ u.val) : voteOfV view4 5 4 u = some bB := by
  unfold voteOfV
  have hT2 : tab4 u 2 = {bB} := by
    unfold tab4
    rw [if_neg (by omega : ¬ (2:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0),
      if_neg (by omega : ¬ u.val = 1), if_neg (by omega : ¬ u.val ≤ 4), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tab4 u) 5 4, u' ≤ 2 := by
    intro u' hu'
    rw [mem_cand] at hu'
    obtain ⟨hlt, hwin, hne⟩ := hu'
    by_contra hgt
    apply hne
    unfold tab4
    rw [if_neg (by omega : ¬ u' ≤ 1), if_neg (by omega : ¬ u.val = 0),
      if_neg (by omega : ¬ u.val = 1), if_neg (by omega : ¬ u.val ≤ 4),
      if_neg (by omega : ¬ u' = 2)]
  refine voteOf1_eq_some ?_ hmax hT2 okBlk_bB_view4
  rw [mem_cand]; refine ⟨by omega, by omega, ?_⟩
  show tab4 u 2 ≠ ∅; rw [hT2]; decide

def expected4 (u : V5) : Option Blk :=
  if u.val ≤ 1 then some bB else if u.val ≤ 4 then some bA else some bB

theorem voteOfV_eq_expected4 (u : V5) : voteOfV view4 5 4 u = expected4 u := by
  unfold expected4
  by_cases h1 : u.val ≤ 1
  · rw [if_pos h1, voteOf4_bB3 (by omega)]
  · rw [if_neg h1]
    by_cases h4 : u.val ≤ 4
    · rw [if_pos h4, voteOf4_bA ⟨by omega, by omega⟩]
    · rw [if_neg h4, voteOf4_v4 (by omega)]

theorem weight_bA_reorg4 : weight bA (votesV view4 5 4) = 3 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V5 => ∃ b, voteOfV view4 5 4 u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V5 => ∃ b, expected4 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected4 u]
  rw [this]; decide

theorem weight_bB_reorg4 : weight bB (votesV view4 5 4) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V5 => ∃ b, voteOfV view4 5 4 u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V5 => ∃ b, expected4 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected4 u]
  rw [this]; decide

/-- **The LMD reorg.** At slot 4 the fork choice outputs `bB`: the never-expiring
`v4` vote plus the two corrupted votes give `bB` a strict majority (weight 4)
over `bA` (weight 3), reorging the honest chain. -/
theorem fcV_reorg4 : fcV view4 5 4 = bB := by
  unfold fcV
  rw [if_neg, if_pos okBlk_bB_view4]
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨?_, okBlk_bB_view4⟩
  rw [weight_bA_reorg4, weight_bB_reorg4]; omega

/-! ## The execution, `τ`-compliance and the theorem -/

private theorem l_d3ma (s : ℕ) : (3 * s + 1) / 3 = s := by omega
private theorem l_d3m (s : ℕ) : (3 * s) / 3 = s := by omega
private theorem l_t3 (s : ℕ) : 3 * 1 * s = 3 * s := by omega
private theorem l_t31 (t : ℕ) : 3 * 1 * t + 1 = 3 * t + 1 := by omega

/-- The LMD witnessing execution (`η = ∞` modelled by window `η = 5`, standard
fork choice `fcV`). -/
noncomputable def E4 : Execution Blk V5 (Vw V5) where
  Δ := 1
  Δ_pos := one_pos
  view _ _ := view4
  active _ _ := True
  pivot t := t = 2
  proposerView _ := view4
  proposal t := if t = 2 then bA else gen
  blockView b := blockViewV V5 b
  FC W s := fcV W 5 s
  votesFor u t b := b = fcV view4 5 ((3 * 1 * t + 1) / 3)
  chAt u r := fcV view4 5 (r / 3)

theorem E4_voteRound (t : ℕ) : (E4).voteRound t = 3 * t + 1 := l_t31 t

/-- The LMD sleepy model. `v0` adversarial always; `v1` corrupted from slot 3;
`V3 = {v5, v6}` awake only at slot 2 (their `bB` votes then persist forever under
`η = ∞`). -/
def SM4 : SleepyModel E4 where
  H t := if t ≤ 2 then {1, 2, 3, 4, 5, 6} else {2, 3, 4}
  A t := if t ≤ 2 then {0} else {0, 1}
  H_voter := fun _ => trivial

/-- With `τ = 1` the sleepiness window `[t+1−1, t−1]` is empty, so `Hwindow 1`
carries nothing. -/
private theorem hw1_contra {u' s : ℕ} (h1 : s ≤ u' + 1) (h2 : u' + 2 ≤ s) : False := by omega

theorem Hwindow_one_empty (s : ℕ) : (SM4).Hwindow 1 s = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [SleepyModel.mem_Hwindow] at hv
  obtain ⟨u', h1, h2, -⟩ := hv
  exact hw1_contra h1 h2

/-- **`E4` is `1`-compliant.** With `A_{t+1}` at most two adversaries and `H_t`
at least three honest validators, `τ = 1`-sleepiness holds. -/
theorem SM4_EtaSleepy : (SM4).EtaSleepy 1 := by
  intro t
  rw [Hwindow_one_empty]
  simp only [Finset.empty_sdiff, Finset.union_empty]
  simp only [SM4]
  by_cases ht : t + 1 ≤ 2
  · rw [if_pos ht, if_pos (Nat.le_succ_of_le (Nat.le_of_succ_le_succ ht))]; decide
  · rw [if_neg ht]
    by_cases ht2 : t ≤ 2
    · rw [if_pos ht2]; decide
    · rw [if_neg ht2]; decide

/-- **`E4` reorgs the honest proposal.** Slot 2 is a pivot proposing `bA`, yet at
slot 4 the canonical chain of every active validator is `bB`. -/
theorem E4_not_reorgResilient : ¬ ReorgResilient E4 := by
  intro hRR
  obtain ⟨hc1, -⟩ := hRR 2 rfl
  have hle := hc1 4 (by decide) 0 trivial
  have hprop : (E4).proposal 2 = bA := by show (if (2:Slot) = 2 then bA else gen) = bA; rfl
  rw [hprop] at hle
  have hch : (E4).chAt (0 : V5) ((E4).voteRound 4) = bB := by
    show fcV view4 5 (((E4).voteRound 4) / 3) = bB
    rw [E4_voteRound]; show fcV view4 5 ((3 * 4 + 1) / 3) = bB
    rw [l_d3ma, fcV_reorg4]
  rw [hch] at hle
  exact absurd hle (by decide)

/-- **Theorem 4.** LMD-GHOST (RLMD-GHOST with `η = ∞`) is not
`τ`-dynamically-available for any finite `τ`. Witness: a `1`-compliant execution
(hence `τ`-compliant for every `τ ≥ 1` by the sleepy-model hierarchy) whose
honest pivot proposal `bA` is reorged to `bB` at slot 4 — the never-expiring `V3`
votes plus a single corruption flip the majority. A reorged honest proposal
cannot be safely confirmed, so no confirmation rule makes the execution both safe
and live. -/
theorem theorem4 :
    ∃ (E : Execution Blk V5 (Vw V5)) (SM : SleepyModel E),
      Nonempty (RLMDGhostBase E) ∧ SM.EtaSleepy 1 ∧ ¬ ReorgResilient E :=
  ⟨E4, SM4, ⟨witnessBase E4 5 (fun _ _ => rfl) (fun _ _ => view4) (by
      intro u s r _ hr
      have hrs : r / 3 = s := by
        rcases hr with h | h
        · rw [h]; show (3 * 1 * s) / 3 = s; rw [l_t3 s]; exact l_d3m s
        · rw [h]; show (3 * 1 * s + 1) / 3 = s; rw [l_t31 s]; exact l_d3ma s
      show fcV view4 5 (r / 3) = fcV view4 5 s
      rw [hrs])⟩,
    SM4_EtaSleepy, E4_not_reorgResilient⟩

end Tightness

end RLMDGhost
