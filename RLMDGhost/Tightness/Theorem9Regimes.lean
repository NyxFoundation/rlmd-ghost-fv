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

theorem okBlk_bB_viewF (η : ℕ) : okBlk (viewF η).1 bB := by rw [viewF_fst]; decide

/-- `tabF` agrees with `tab9` on the expiry window `[1, η]`. -/
theorem tabF_eq_tab9 {η : ℕ} {u : V9} {u' : Slot} (h1 : 1 ≤ u') (h2 : u' ≤ η) :
    tabF η u u' = tab9 η u u' := by
  unfold tabF
  rw [if_neg (Nat.not_le.mpr (Nat.lt_succ_of_le h2)),
    if_neg (Nat.one_le_iff_ne_zero.mp h1)]

/-- `tabF` at a tail slot: everyone votes `bB`. -/
theorem tabF_tail {η : ℕ} {u : V9} {u' : Slot} (h : η + 1 ≤ u') :
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

end Tightness

end RLMDGhost
