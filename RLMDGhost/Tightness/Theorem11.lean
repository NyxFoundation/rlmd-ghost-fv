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

end Tightness

end RLMDGhost
