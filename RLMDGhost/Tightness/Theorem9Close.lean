import RLMDGhost.Tightness.Theorem9Regimes
import RLMDGhost.Tightness.WitnessBase
import RLMDGhost.ProposeVoteMerge.Theorem1

/-!
# Theorem 9 — the full execution instance

Assembles the concrete RLMD-GHOST execution witnessing that the protocol is
**not** `τ`-reorg-resilient for `1 ≤ τ < η`, from the fork-choice computations
of `Theorem9Core`/`Theorem9Regimes` (`fcV = bC` on `[2, η]`, `bB` on
`[η+1, ∞)`), the witness bundler (`witnessBase`) and the latest-message delivery
lemma (`voteOf1_at_prev`).

The boundary slots use *selective-delivery* views: at slot 0 only genesis is
known, at slot 1 each group sees only its own proposal (`{gen, bA}` for `V2`,
`{gen, bB}` for `V3`), and from slot 2 on every block is seen (`viewF`). This
reproduces the ex-ante fork: `V2` votes `bA`, `V3` votes `bB`, and their views
merge into the common `viewF` used from the pivot slot 2 onward.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-! ## Boundary views and their fork choices -/

/-- The view a validator's fork choice runs on at slot `s`: genesis-only at
slot 0, the selectively-delivered proposal at slot 1, and the common `viewF`
from slot 2 on. -/
def effV (η : ℕ) (u : V9) (s : Slot) : Vw V9 :=
  if s = 0 then (({gen} : Finset Blk), tabF η)
  else if s = 1 then (({gen} ∪ (if 7 ≤ u.val then {bB} else {bA}) : Finset Blk), tabF η)
  else viewF η

-- η-free `okBlk` facts about the boundary known sets
theorem okBlk_gen_bA : ¬ okBlk ({gen} : Finset Blk) bA := by decide
theorem okBlk_gen_bB : ¬ okBlk ({gen} : Finset Blk) bB := by decide
theorem okBlk_genbA_bA : okBlk ({gen, bA} : Finset Blk) bA := by decide
theorem okBlk_genbA_bB : ¬ okBlk ({gen, bA} : Finset Blk) bB := by decide
theorem okBlk_genbA_bC : ¬ okBlk ({gen, bA} : Finset Blk) bC := by decide
theorem okBlk_genbB_bA : ¬ okBlk ({gen, bB} : Finset Blk) bA := by decide
theorem okBlk_genbB_bB : okBlk ({gen, bB} : Finset Blk) bB := by decide

theorem fcV_slot0 (η : ℕ) (u : V9) : fcV (effV η u 0) η 0 = gen := by
  unfold fcV effV
  rw [if_pos rfl]
  rw [if_neg (fun h => okBlk_gen_bA h.1), if_neg okBlk_gen_bB]

theorem fcV_slot1_v2 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : u.val ≤ 6) :
    fcV (effV η u 1) η 1 = bA := by
  have hview : effV η u 1 = (({gen, bA} : Finset Blk), tabF η) := by
    unfold effV; rw [if_neg (by decide), if_pos rfl, if_neg (by omega : ¬ 7 ≤ u.val)]; rfl
  rw [hview]
  unfold fcV
  rw [if_pos ⟨okBlk_genbA_bA, fun h => okBlk_genbA_bB h.2⟩, if_neg okBlk_genbA_bC]

theorem fcV_slot1_v3 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : 7 ≤ u.val) :
    fcV (effV η u 1) η 1 = bB := by
  have hview : effV η u 1 = (({gen, bB} : Finset Blk), tabF η) := by
    unfold effV; rw [if_neg (by decide), if_pos rfl, if_pos h]; rfl
  rw [hview]
  unfold fcV
  rw [if_neg (fun h => okBlk_genbB_bA h.1), if_pos okBlk_genbB_bB]

/-! ### The pivot fork choice over `viewF` (slot 2) -/

theorem voteOf_pivotF_v2 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h1 : 1 ≤ u.val) (h2 : u.val ≤ 6) :
    voteOfV (viewF η) η 2 u = some bA := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bA_viewF η)
  show tabF η u (2 - 1) = {bA}
  rw [show (2 - 1) = 1 from rfl, tabF_eq_tab9 (u' := 1) (by omega) (by omega)]
  unfold tab9
  rw [if_neg (by omega : ¬ u.val = 0)]
  by_cases hle2 : u.val ≤ 2
  · rw [if_pos hle2, if_pos rfl]
  · rw [if_neg hle2, if_pos h2, if_pos rfl]

theorem voteOf_pivotF_v3 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : 7 ≤ u.val) :
    voteOfV (viewF η) η 2 u = some bB := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bB_viewF η)
  show tabF η u (2 - 1) = {bB}
  rw [show (2 - 1) = 1 from rfl, tabF_eq_tab9 (u' := 1) (by omega) (by omega)]
  unfold tab9
  rw [if_neg (by omega : ¬ u.val = 0), if_neg (by omega : ¬ u.val ≤ 2),
    if_neg (by omega : ¬ u.val ≤ 6), if_pos rfl]

theorem voteOf_pivotF_adv {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : u.val = 0) :
    voteOfV (viewF η) η 2 u = some gen := by
  unfold voteOfV
  have hT0 : tabF η u 0 = {gen} := by unfold tabF; rw [if_neg (by omega), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tabF η u) η 2, u' ≤ 0 := by
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

/-- The counted vote of each validator at the pivot slot 2. -/
def expectedPivot (u : V9) : Option Blk :=
  if u.val = 0 then some gen else if u.val ≤ 6 then some bA else some bB

theorem voteOfV_eq_expectedPivot {η : ℕ} (hη : 2 ≤ η) (u : V9) :
    voteOfV (viewF η) η 2 u = expectedPivot u := by
  unfold expectedPivot
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf_pivotF_adv hη h0]
  · rw [if_neg h0]
    by_cases h6 : u.val ≤ 6
    · rw [if_pos h6, voteOf_pivotF_v2 hη (by omega) h6]
    · rw [if_neg h6, voteOf_pivotF_v3 hη (by omega)]

theorem weight_bA_pivotF {η : ℕ} (hη : 2 ≤ η) :
    weight bA (votesV (viewF η) η 2) = 6 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η 2 u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expectedPivot u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expectedPivot hη u]
  rw [this]; decide

theorem weight_bB_pivotF {η : ℕ} (hη : 2 ≤ η) :
    weight bB (votesV (viewF η) η 2) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η 2 u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expectedPivot u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expectedPivot hη u]
  rw [this]; decide

/-- The honest chain `bC` at the pivot slot 2 over `viewF`. -/
theorem fcV_pivotF {η : ℕ} (hη : 2 ≤ η) : fcV (viewF η) η 2 = bC := by
  unfold fcV
  rw [if_pos, if_pos (okBlk_bC_viewF η)]
  refine ⟨okBlk_bA_viewF η, ?_⟩
  rw [weight_bA_pivotF hη, weight_bB_pivotF hη]
  rintro ⟨hlt, -⟩; omega

/-! ## The execution -/

private theorem div3_mul (s : ℕ) : (3 * s) / 3 = s := by omega
private theorem div3_mul_add (s : ℕ) : (3 * s + 1) / 3 = s := by omega
private theorem three_one_mul (t : ℕ) : 3 * 1 * t = 3 * t := by omega
private theorem three_one_mul_add (t : ℕ) : 3 * 1 * t + 1 = 3 * t + 1 := by omega

/-! ### The reorg fork choice over `viewF` -/

/-- The counted vote of each validator at the reorg slot `η + 1` over `viewF`
(identical to the `view9` computation, since `tabF = tab9` on the window
`[1, η]`). -/
theorem voteOf_reorgF_adv {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : u.val = 0) :
    voteOfV (viewF η) η (η + 1) u = some bB := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bB_viewF η)
  show tabF η u (η + 1 - 1) = {bB}
  have he : η + 1 - 1 = η := by omega
  rw [he, tabF_eq_tab9 (u' := η) (by omega) (by omega)]
  unfold tab9; rw [if_pos h, if_pos rfl]

theorem voteOf_reorgF_v2 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h1 : 3 ≤ u.val) (h2 : u.val ≤ 6) :
    voteOfV (viewF η) η (η + 1) u = some bC := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bC_viewF η)
  show tabF η u (η + 1 - 1) = {bC}
  have he : η + 1 - 1 = η := by omega
  rw [he, tabF_eq_tab9 (u' := η) (by omega) (by omega)]
  unfold tab9
  rw [if_neg (by omega : ¬ u.val = 0), if_neg (by omega : ¬ u.val ≤ 2), if_pos h2,
    if_neg (by omega : ¬ η = 1), if_pos (by omega : 2 ≤ η ∧ η ≤ η)]

theorem voteOf_reorgF_equiv {η : ℕ} (hη : 2 ≤ η) {u : V9} (h1 : 1 ≤ u.val) (h2 : u.val ≤ 2) :
    voteOfV (viewF η) η (η + 1) u = none := by
  unfold voteOfV
  have he : η + 1 - 1 = η := by omega
  have hT : tabF η u η = {bC, bB} := by
    rw [tabF_eq_tab9 (u' := η) (by omega) (by omega)]
    unfold tab9
    rw [if_neg (by omega : ¬ u.val = 0), if_pos h2, if_neg (by omega : ¬ η = 1), if_pos rfl]
  refine voteOf1_at_prev_none (by omega) (by omega) ?_ ?_
  · rw [he]; show tabF η u η ≠ ∅; rw [hT]; decide
  · intro b; rw [he]; show tabF η u η ≠ {b}; rw [hT]
    rcases b with _ | _ | _ | _ <;> decide

theorem voteOf_reorgF_v3 {η : ℕ} (hη : 2 ≤ η) {u : V9} (h : 7 ≤ u.val) :
    voteOfV (viewF η) η (η + 1) u = some bB := by
  unfold voteOfV
  have hT1 : tabF η u 1 = {bB} := by
    rw [tabF_eq_tab9 (u' := 1) (by omega) (by omega)]
    unfold tab9
    rw [if_neg (by omega : ¬ u.val = 0), if_neg (by omega : ¬ u.val ≤ 2),
      if_neg (by omega : ¬ u.val ≤ 6), if_pos rfl]
  have hmax : ∀ u' ∈ cand (tabF η u) η (η + 1), u' ≤ 1 := by
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

/-- The counted vote of each validator at the reorg slot. -/
def expectedReorg (u : V9) : Option Blk :=
  if u.val = 0 then some bB
  else if u.val ≤ 2 then none
  else if u.val ≤ 6 then some bC
  else some bB

theorem voteOfV_eq_expectedReorg {η : ℕ} (hη : 2 ≤ η) (u : V9) :
    voteOfV (viewF η) η (η + 1) u = expectedReorg u := by
  unfold expectedReorg
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf_reorgF_adv hη h0]
  · rw [if_neg h0]
    by_cases h2 : u.val ≤ 2
    · rw [if_pos h2, voteOf_reorgF_equiv hη (by omega) h2]
    · rw [if_neg h2]
      by_cases h6 : u.val ≤ 6
      · rw [if_pos h6, voteOf_reorgF_v2 hη (by omega) h6]
      · rw [if_neg h6, voteOf_reorgF_v3 hη (by omega)]

theorem weight_bB_reorgF {η : ℕ} (hη : 2 ≤ η) :
    weight bB (votesV (viewF η) η (η + 1)) = 5 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η (η + 1) u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expectedReorg u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expectedReorg hη u]
  rw [this]; decide

theorem weight_bA_reorgF {η : ℕ} (hη : 2 ≤ η) :
    weight bA (votesV (viewF η) η (η + 1)) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V9 =>
      ∃ b, voteOfV (viewF η) η (η + 1) u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V9 => ∃ b, expectedReorg u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expectedReorg hη u]
  rw [this]; decide

/-- The reorg over `viewF`: at slot `η + 1` the fork choice is `bB`. -/
theorem fcV_reorgF {η : ℕ} (hη : 2 ≤ η) : fcV (viewF η) η (η + 1) = bB := by
  unfold fcV
  rw [if_neg, if_pos (okBlk_bB_viewF η)]
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨?_, okBlk_bB_viewF η⟩
  rw [weight_bA_reorgF hη, weight_bB_reorgF hη]
  omega

/-- The witnessing execution. `Δ = 1`, the fork choice is `fcV`, and each
validator's canonical chain at a fork-choice round is `fcV` on its
selectively-delivered effective view. -/
noncomputable def E9 (η : ℕ) : Execution Blk V9 (Vw V9) where
  Δ := 1
  Δ_pos := one_pos
  view _ _ := viewF η
  active _ _ := True
  pivot t := t = 2
  proposerView _ := viewF η
  proposal t := if t = 2 then bC else gen
  blockView b := blockViewV V9 b
  FC W s := fcV W η s
  votesFor u t b := b = fcV (effV η u ((3 * 1 * t + 1) / 3)) η ((3 * 1 * t + 1) / 3)
  chAt u r := fcV (effV η u (r / 3)) η (r / 3)

theorem E9_voteRound (η : ℕ) (t : Slot) : (E9 η).voteRound t = 3 * t + 1 :=
  three_one_mul_add t

theorem E9_slotStart (η : ℕ) (t : Slot) : (E9 η).slotStart t = 3 * t :=
  three_one_mul t

theorem E9_chAt (η : ℕ) (u : V9) (r : Round) :
    (E9 η).chAt u r = fcV (effV η u (r / 3)) η (r / 3) := rfl

/-- The canonical chain at a fork-choice round of slot `s` is `fcV` on the
slot-`s` effective view. -/
theorem E9_chAt_slot (η : ℕ) (u : V9) {s : Slot} {r : Round}
    (hr : r = (E9 η).slotStart s ∨ r = (E9 η).voteRound s) :
    (E9 η).chAt u r = fcV (effV η u s) η s := by
  have hrs : r / 3 = s := by
    rcases hr with h | h
    · rw [h, E9_slotStart]; exact div3_mul s
    · rw [h, E9_voteRound]; exact div3_mul_add s
  rw [E9_chAt, hrs]

/-! ## `¬ ReorgResilient`: the honest proposal `bC` is reorged -/

/-- **The reorg.** `E9 η` (for `η ≥ 2`) does not satisfy reorg resilience: slot 2
is a pivot with honest proposal `bC`, yet at slot `η + 1` the canonical chain of
every active validator is `bB`, not a descendant of `bC`. -/
theorem E9_not_reorgResilient {η : ℕ} (hη : 2 ≤ η) : ¬ ReorgResilient (E9 η) := by
  intro hRR
  obtain ⟨hvote, -⟩ := hRR 2 rfl
  have hact : (E9 η).active (0 : V9) ((E9 η).voteRound (η + 1)) := trivial
  have hle := hvote (η + 1) (le_trans hη (Nat.le_succ η)) 0 hact
  -- proposal 2 = bC; chAt at slot η+1 = fcV viewF (η+1) = bB
  have hprop : (E9 η).proposal 2 = bC := by show (if (2:Slot) = 2 then bC else gen) = bC; rfl
  rw [hprop, E9_chAt_slot η 0 (Or.inr rfl)] at hle
  have hview : effV η 0 (η + 1) = viewF η := by
    unfold effV
    rw [if_neg (Nat.succ_ne_zero η), if_neg (by omega : ¬ η + 1 = 1)]
  rw [hview, fcV_reorgF hη] at hle
  exact absurd hle (by decide)

/-! ## The `Spec` instance -/

theorem effV_ge2 {η : ℕ} {u : V9} {s : ℕ} (hs : 2 ≤ s) : effV η u s = viewF η := by
  unfold effV
  rw [if_neg (fun h => by simp only [h] at hs; exact absurd hs (by decide)),
    if_neg (fun h => by simp only [h] at hs; exact absurd hs (by decide))]

/-- Merging the honest proposal `bC` into `viewF` leaves it unchanged (its
history is already seen and it carries no votes). -/
theorem viewF_sup_bC (η : ℕ) : viewF η ⊔ blockViewV V9 bC = viewF η := by
  apply Prod.ext
  · show (viewF η).1 ∪ (blockViewV V9 bC).1 = (viewF η).1
    rw [viewF_fst]
    show ({gen, bA, bB, bC} : Finset Blk) ∪ Blk.down bC = {gen, bA, bB, bC}
    decide
  · funext u u'
    show (viewF η).2 u u' ∪ (blockViewV V9 bC).2 u u' = (viewF η).2 u u'
    exact Finset.union_empty _

theorem E9_spec {η : ℕ} (hη : 2 ≤ η) : Spec (E9 η) where
  fc_consistency V t B h := fcV_consistency V η t B h
  proposal_extends {t} hpivot := by
    have ht : t = 2 := hpivot
    subst ht
    show fcV (viewF η) η 2 ≤ (if (2 : Slot) = 2 then bC else gen)
    rw [if_pos rfl, fcV_pivotF hη]
  voter_view_le {v t} _ _ := le_refl _
  chAt_pivot_merge {v t} hpivot _ := by
    have ht : t = 2 := hpivot
    subst ht
    rw [E9_chAt_slot η v (Or.inr rfl), effV_ge2 (le_refl 2)]
    show fcV (viewF η) η 2 = fcV (viewF η ⊔ (viewF η ⊔ blockViewV V9 bC)) η 2
    rw [viewF_sup_bC, sup_idem]
  vote_chAt {v t} _ := rfl
  vote_unique {v t b b'} _ hb hb' := hb.trans hb'.symm

/-! ## The sleepy model and the delivery fields -/

/-- The honest-voter and corrupted sets. Honest active: all of `{1,…,10}`
through slot 1; `{1,…,6}` while `V3` sleeps (`[2, η]`); `{3,…,10}` after the
reorg (`V3` woken, `v2, v3` corrupted). Corrupted: `{0}` through slot `η`, then
`{0, 1, 2}`. -/
def SM9 (η : ℕ) : SleepyModel (E9 η) where
  H t := if t ≤ 1 then {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    else if t ≤ η then {1, 2, 3, 4, 5, 6} else {3, 4, 5, 6, 7, 8, 9, 10}
  A t := if t ≤ η then {0} else {0, 1, 2}
  H_voter := fun _ => trivial

/-- The counted vote of `u` at slot 1 over any slot-1 group view is genesis
(every validator's only in-window vote is its slot-0 genesis vote). -/
theorem voteOf_slot1 {η : ℕ} (hη : 2 ≤ η) (v u : V9) : voteOfV (effV η v 1) η 1 u = some gen := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ ?_
  · show tabF η u (1 - 1) = {gen}
    rw [show (1 - 1) = 0 from rfl]
    unfold tabF; rw [if_neg (Nat.not_succ_le_zero η), if_pos rfl]
  · -- gen is seen in any known set
    show okBlk (effV η v 1).1 gen
    unfold effV; rw [if_neg (by decide), if_pos rfl]
    trivial

/-- `votesFor u t b` is exactly `b = fcV (effV η u t) η t`. -/
theorem E9_votesFor_iff {η : ℕ} {u : V9} {t : ℕ} {b : Blk} :
    (E9 η).votesFor u t b ↔ b = fcV (effV η u t) η t := by
  show (b = fcV (effV η u ((3 * 1 * t + 1) / 3)) η ((3 * 1 * t + 1) / 3)) ↔ _
  rw [three_one_mul_add t, div3_mul_add t]

/-- The tip `u` computes at slot `t`, by regime. -/
theorem chAtV_eq {η : ℕ} (hη : 2 ≤ η) (u : V9) {t : ℕ} :
    fcV (effV η u t) η t =
      if t = 0 then gen
      else if t = 1 then (if 7 ≤ u.val then bB else bA)
      else if t ≤ η then bC else bB := by
  by_cases h0 : t = 0
  · rw [if_pos h0]; subst h0; exact fcV_slot0 η u
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; subst h1
      by_cases h7 : 7 ≤ u.val
      · rw [if_pos h7]; exact fcV_slot1_v3 hη h7
      · rw [if_neg h7]; exact fcV_slot1_v2 hη (Nat.lt_succ_iff.mp (not_le.mp h7))
    · rw [if_neg h1, effV_ge2 (by omega)]
      by_cases hηt : t ≤ η
      · rw [if_pos hηt]
        rcases Nat.lt_or_ge t 3 with h3 | h3
        · rw [show t = 2 from by omega]; exact fcV_pivotF hη
        · exact fcV_mid h3 hηt
      · rw [if_neg hηt]
        rcases Nat.lt_or_ge t (η + 2) with h | h
        · rw [show t = η + 1 from by omega]; exact fcV_reorgF hη
        · exact fcV_tail hη h

/-! ### Membership facts -/

theorem mem_H10 : ∀ u : V9, (u ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset V9)) ↔ 1 ≤ u.val := by
  decide
theorem mem_H6 : ∀ u : V9,
    (u ∈ ({1, 2, 3, 4, 5, 6} : Finset V9)) ↔ (1 ≤ u.val ∧ u.val ≤ 6) := by decide
theorem mem_H38 : ∀ u : V9,
    (u ∈ ({3, 4, 5, 6, 7, 8, 9, 10} : Finset V9)) ↔ (3 ≤ u.val ∧ u.val ≤ 10) := by decide
theorem mem_A012 : ∀ u : V9, u.val ≤ 2 → u ∈ ({0, 1, 2} : Finset V9) := by decide

/-! ### `honest_vote_counted` -/

theorem fcV_viewF_mid {η t : ℕ} (hη : 2 ≤ η) (h2 : 2 ≤ t) (hηt : t ≤ η) :
    fcV (viewF η) η t = bC := by
  rcases Nat.lt_or_ge t 3 with h | h
  · rw [show t = 2 from by omega]; exact fcV_pivotF hη
  · exact fcV_mid h hηt

theorem fcV_viewF_tail {η t : ℕ} (hη : 2 ≤ η) (h : η + 1 ≤ t) :
    fcV (viewF η) η t = bB := by
  rcases Nat.lt_or_ge t (η + 2) with h' | h'
  · rw [show t = η + 1 from by omega]; exact fcV_reorgF hη
  · exact fcV_tail hη h'

theorem vF_mid {η t : ℕ} (u : V9) (hη : 2 ≤ η) (h2 : 2 ≤ t) (hηt : t ≤ η) :
    (E9 η).votesFor u t bC :=
  E9_votesFor_iff.mpr (by rw [effV_ge2 (by omega : 2 ≤ t)]; exact (fcV_viewF_mid hη h2 hηt).symm)

theorem vF_tail {η t : ℕ} (u : V9) (hη : 2 ≤ η) (h : η + 1 ≤ t) : (E9 η).votesFor u t bB :=
  E9_votesFor_iff.mpr (by rw [effV_ge2 (by omega : 2 ≤ t)]; exact (fcV_viewF_tail hη h).symm)

/-- **`honest_vote_counted` for `E9`.** -/
theorem E9_hvc {η : ℕ} (hη : 2 ≤ η) {v : V9} {t : ℕ} (u : V9) (hu : u ∈ (SM9 η).H t) :
    (∃ b, voteOfV (effV η v (t + 1)) η (t + 1) u = some b ∧ (E9 η).votesFor u t b) ∨
      (voteOfV (effV η v (t + 1)) η (t + 1) u = none ∧ u ∈ (SM9 η).A (t + 1)) := by
  by_cases h0 : t = 0
  · subst h0
    exact Or.inl ⟨gen, voteOf_slot1 hη v u, E9_votesFor_iff.mpr (fcV_slot0 η u).symm⟩
  rw [effV_ge2 (show 2 ≤ t + 1 by omega)]
  simp only [SM9] at hu
  by_cases h1 : t = 1
  · subst h1
    rw [if_pos (le_refl 1), mem_H10] at hu
    by_cases h7 : 7 ≤ u.val
    · exact Or.inl ⟨bB, voteOf_pivotF_v3 hη h7, E9_votesFor_iff.mpr (fcV_slot1_v3 hη h7).symm⟩
    · exact Or.inl ⟨bA, voteOf_pivotF_v2 hη hu (Nat.lt_succ_iff.mp (not_le.mp h7)),
        E9_votesFor_iff.mpr (fcV_slot1_v2 hη (Nat.lt_succ_iff.mp (not_le.mp h7))).symm⟩
  rw [if_neg (by omega : ¬ t ≤ 1)] at hu
  by_cases hηt : t ≤ η
  · rw [if_pos hηt, mem_H6] at hu
    by_cases hteq : t = η
    · rw [hteq]
      by_cases h12 : u.val ≤ 2
      · refine Or.inr ⟨voteOf_reorgF_equiv hη hu.1 h12, ?_⟩
        simp only [SM9]; rw [if_neg (by omega : ¬ η + 1 ≤ η)]; exact mem_A012 u h12
      · exact Or.inl ⟨bC, voteOf_reorgF_v2 hη (by omega) hu.2,
          vF_mid u hη (by omega) (le_refl η)⟩
    · exact Or.inl ⟨bC, voteOf_mid_v2 (by omega) (by omega) hu.1 hu.2,
        vF_mid u hη (by omega) hηt⟩
  · rw [if_neg hηt, mem_H38] at hu
    have hgt : η < t := Nat.lt_of_not_le hηt
    exact Or.inl ⟨bB, voteOf_tail hη (by omega) u, vF_tail u hη (by omega)⟩

/-! ### `counted_from_window` -/

theorem zero_mem_A {η : ℕ} (s : ℕ) : (0 : V9) ∈ (SM9 η).A s := by
  simp only [SM9]; by_cases h : s ≤ η
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- `H_t ∪ A_{t+1} ∪ Hwindow η (t+1)` covers every validator, so any counted
vote's sender is accounted for. -/
theorem E9_cfw_cover {η : ℕ} (hη : 2 ≤ η) (t : ℕ) (u : V9) :
    u ∈ (SM9 η).H t ∨ u ∈ (SM9 η).A (t + 1) ∨ u ∈ (SM9 η).Hwindow η (t + 1) := by
  by_cases h0 : u.val = 0
  · refine Or.inr (Or.inl ?_)
    rw [show u = 0 from Fin.ext h0]; exact zero_mem_A _
  by_cases hle1 : t ≤ 1
  · left; simp only [SM9]; rw [if_pos hle1, mem_H10]; omega
  by_cases hηt : t ≤ η
  · -- t ∈ [2, η]
    by_cases h6 : u.val ≤ 6
    · left; simp only [SM9]; rw [if_neg hle1, if_pos hηt, mem_H6]; omega
    · -- V3: in Hwindow via slot 1
      refine Or.inr (Or.inr ?_)
      rw [SleepyModel.mem_Hwindow]
      have ha : t + 1 ≤ 1 + η := by omega
      have hb : 1 + 2 ≤ t + 1 := by omega
      refine ⟨1, ha, hb, ?_⟩
      simp only [SM9]; rw [if_pos (by omega : (1 : ℕ) ≤ 1), mem_H10]; omega
  · -- t ≥ η + 1
    by_cases h2 : u.val ≤ 2
    · refine Or.inr (Or.inl ?_)
      simp only [SM9]; rw [if_neg (by omega : ¬ t + 1 ≤ η)]
      have : u ∈ ({0, 1, 2} : Finset V9) := mem_A012 u h2
      exact this
    · left; simp only [SM9]; rw [if_neg hle1, if_neg hηt, mem_H38]
      exact ⟨by omega, by omega⟩

/-! ### `EtaSleepy τ` for `τ < η` -/

/-- Every honest set is contained in `{1,…,10}` (no adversary `0`). -/
theorem H_sub_all {η : ℕ} (u' : ℕ) :
    (SM9 η).H u' ⊆ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset V9) := by
  simp only [SM9]
  split_ifs <;> decide

/-- `Hwindow` never contains the adversary. -/
theorem Hwindow_sub_all {η τ : ℕ} (s : ℕ) :
    (SM9 η).Hwindow τ s ⊆ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset V9) := by
  intro v hv
  rw [SleepyModel.mem_Hwindow] at hv
  obtain ⟨u', _, _, hvu⟩ := hv
  exact H_sub_all u' hvu

/-- At the reorg slot, `Hwindow τ (η+1) ⊆ {1,…,6}`: because `τ < η`, the window
`[η+1−τ, η−1] ⊆ [2, η−1]` never reaches slot 1 where `V3` last voted. -/
private theorem reorg_window_bound {u' η τ : ℕ} (h1 : η + 1 ≤ u' + τ)
    (h2 : u' + 2 ≤ η + 1) (hτ : τ < η) : ¬ u' ≤ 1 ∧ u' ≤ η :=
  ⟨by omega, by omega⟩

theorem Hwindow_reorg_sub {η τ : ℕ} (hη : 2 ≤ η) (hτ : τ < η) :
    (SM9 η).Hwindow τ (η + 1) ⊆ ({1, 2, 3, 4, 5, 6} : Finset V9) := by
  intro v hv
  rw [SleepyModel.mem_Hwindow] at hv
  obtain ⟨u', hu1, hu2, hvu⟩ := hv
  obtain ⟨hb1, hb2⟩ := reorg_window_bound hu1 hu2 hτ
  simp only [SM9] at hvu
  rw [if_neg hb1, if_pos hb2] at hvu
  exact hvu

theorem SM9_EtaSleepy {η τ : ℕ} (hη : 2 ≤ η) (hτ1 : 1 ≤ τ) (hτ : τ < η) :
    (SM9 η).EtaSleepy τ := by
  intro t
  by_cases hteq : t = η
  · -- reorg slot: A = {0,1,2}, Hwindow ⊆ {1-6} = H_η, so Hwindow \ H_η = ∅
    rw [hteq]
    have hn1 : ¬ η ≤ 1 := by omega
    have hnA : ¬ η + 1 ≤ η := by omega
    have hHt : (SM9 η).H η = ({1, 2, 3, 4, 5, 6} : Finset V9) := by
      simp only [SM9]; rw [if_neg hn1, if_pos le_rfl]
    have hA : (SM9 η).A (η + 1) = ({0, 1, 2} : Finset V9) := by
      simp only [SM9]; rw [if_neg hnA]
    have hsub : (SM9 η).A (η + 1) ∪ ((SM9 η).Hwindow τ (η + 1) \ (SM9 η).H η) ⊆
        ({0, 1, 2} : Finset V9) := by
      rw [hA, hHt]
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hx
      · rw [Finset.mem_sdiff] at hx
        exact absurd (Hwindow_reorg_sub hη hτ hx.1) hx.2
    calc ((SM9 η).A (η + 1) ∪ ((SM9 η).Hwindow τ (η + 1) \ (SM9 η).H η)).card
        ≤ ({0, 1, 2} : Finset V9).card := Finset.card_le_card hsub
      _ < ({1, 2, 3, 4, 5, 6} : Finset V9).card := by decide
      _ = ((SM9 η).H η).card := by rw [hHt]
  · -- other slots: Hwindow ⊆ {1-10}, bound by A ∪ ({1-10} \ H_t)
    have hsub : (SM9 η).A (t + 1) ∪ ((SM9 η).Hwindow τ (t + 1) \ (SM9 η).H t) ⊆
        (SM9 η).A (t + 1) ∪ (({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset V9) \ (SM9 η).H t) := by
      apply Finset.union_subset_union_right
      exact Finset.sdiff_subset_sdiff (Hwindow_sub_all _) (Finset.Subset.refl _)
    refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
    by_cases hle1 : t ≤ 1
    · have ha1 : t + 1 ≤ η := le_trans (Nat.succ_le_succ hle1) hη
      rw [show (SM9 η).A (t + 1) = ({0} : Finset V9) by
          simp only [SM9]; rw [if_pos ha1],
        show (SM9 η).H t = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset V9) by
          simp only [SM9]; rw [if_pos hle1]]
      decide
    · by_cases hηt : t ≤ η
      · have ha1 : t + 1 ≤ η := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hηt hteq)
        rw [show (SM9 η).A (t + 1) = ({0} : Finset V9) by
            simp only [SM9]; rw [if_pos ha1],
          show (SM9 η).H t = ({1, 2, 3, 4, 5, 6} : Finset V9) by
            simp only [SM9]; rw [if_neg hle1, if_pos hηt]]
        decide
      · have hnA : ¬ t + 1 ≤ η := Nat.not_le.mpr (Nat.lt_succ_of_lt (Nat.lt_of_not_le hηt))
        rw [show (SM9 η).A (t + 1) = ({0, 1, 2} : Finset V9) by
            simp only [SM9]; rw [if_neg hnA],
          show (SM9 η).H t = ({3, 4, 5, 6, 7, 8, 9, 10} : Finset V9) by
            simp only [SM9]; rw [if_neg hle1, if_neg hηt]]
        decide

end Tightness

end RLMDGhost
