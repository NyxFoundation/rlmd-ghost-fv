import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import RLMDGhost.Ghost

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

/-!
# Tightness witnesses — a concrete RLMD-GHOST view/filter/fork-choice model

The Track B/D negative results are existence statements: a compliant execution
of the protocol violating a security property. Exhibiting one requires a
*concrete* model discharging the abstract interfaces (`Spec`,
`RLMDGhostBase`, …) — this file provides the reusable operational layer, over
an arbitrary finite validator type:

* `Blk` — the four-block tree `⊥ = gen ⋖ {bA, bB}`, `bA ⋖ bC` of the attack
  constructions (`bA`/`bB` the two conflicting adversarial proposals, `bC` the
  honest proposal extending `bA`), with its `BlockTree` instance;
* `Vw V := Finset Blk × (V → Slot → Finset Blk)` — a view is a set of known
  blocks together with a table of the votes seen, per validator and slot; view
  merge is the componentwise union;
* `voteOf1`/`votesV` — an operational `FIL_rlmd`: per validator, the latest
  in-expiry-window slot with votes seen is selected on the *raw* table; the
  validator is discounted if it equivocated there (two votes for one slot),
  and its vote is counted iff its target is *seen* (`okBlk`: the target or a
  descendant is known, so its whole history is available; genesis for free).
  Selecting and discounting on the raw table keeps the counted votes
  *monotone* under view growth, which is what makes the §2 consistency
  property of the fork choice provable;
* `fcV` — GHOST on the four-block tree over the counted votes, descending on
  the seen blocks with ties broken toward the `bA` branch, satisfying
  `GhostSelects` (`fcV_ghost`) and the §2 consistency property
  (`fcV_consistency`);
* the two counting bookkeeping facts (`count_le_weight_votesV`,
  `card_votesV_le_weight_add`) required by `RLMDGhostBase`.
-/

namespace RLMDGhost

namespace Tightness

/-! ## The four-block tree -/

/-- The block tree of the attack constructions: genesis, two conflicting
blocks `bA`, `bB`, and `bC` extending `bA`. -/
inductive Blk : Type
  | gen | bA | bB | bC
deriving DecidableEq

namespace Blk

instance : Fintype Blk :=
  ⟨⟨[gen, bA, bB, bC], by decide⟩, by intro x; cases x <;> decide⟩

/-- The prefix order, as a Boolean function. -/
def ble : Blk → Blk → Bool
  | gen, _ => true
  | bA, bA => true
  | bA, bC => true
  | bB, bB => true
  | bC, bC => true
  | _, _ => false

instance : PartialOrder Blk where
  le a b := ble a b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Blk := fun a b =>
  inferInstanceAs (Decidable (ble a b = true))

instance : DecidableLT Blk := fun a b =>
  inferInstanceAs (Decidable (a ≤ b ∧ ¬b ≤ a))

theorem le_iff_ble {a b : Blk} : a ≤ b ↔ ble a b = true := Iff.rfl

instance : OrderBot Blk where
  bot := gen
  bot_le := by decide

instance : BlockTree Blk where
  ancestors_isChain := by
    have h : ∀ b x y : Blk, x ≤ b → y ≤ b → x ≠ y → x ≤ y ∨ y ≤ x := by decide
    intro b x hx y hy hxy
    exact h b x y hx hy hxy

instance : FiniteAncestors Blk := ⟨fun _ => Set.toFinite _⟩

instance : ∀ P B' : Blk, Decidable (P ⋖ B') := fun P B' =>
  inferInstanceAs (Decidable (P < B' ∧ ∀ c, P < c → ¬c < B'))

private theorem covBy_cases' : ∀ P B' : Blk, P ⋖ B' →
    (P = gen ∧ B' = bA) ∨ (P = gen ∧ B' = bB) ∨ (P = bA ∧ B' = bC) := by
  decide

/-- The only covering pairs of the four-block tree. -/
theorem covBy_cases {P B' : Blk} (h : P ⋖ B') :
    (P = gen ∧ B' = bA) ∨ (P = gen ∧ B' = bB) ∨ (P = bA ∧ B' = bC) :=
  covBy_cases' P B' h

private theorem le_iffs : ∀ x : Blk,
    (bB ≤ x ↔ x = bB) ∧ (bC ≤ x ↔ x = bC) ∧ (bA ≤ x ↔ x = bA ∨ x = bC) := by
  decide

theorem le_bB_iff {x : Blk} : bB ≤ x ↔ x = bB := (le_iffs x).1
theorem le_bC_iff {x : Blk} : bC ≤ x ↔ x = bC := (le_iffs x).2.1
theorem le_bA_iff {x : Blk} : bA ≤ x ↔ x = bA ∨ x = bC := (le_iffs x).2.2

/-- The ancestor closure of a block. -/
def down : Blk → Finset Blk
  | gen => {gen}
  | bA => {gen, bA}
  | bB => {gen, bB}
  | bC => {gen, bA, bC}

private theorem mem_down' : ∀ a b : Blk, a ∈ b.down ↔ a ≤ b := by decide

theorem mem_down {a b : Blk} : a ∈ b.down ↔ a ≤ b := mem_down' a b

end Blk

open Blk

/-! ## Views: known blocks × vote tables -/

/-- A vote table: the votes seen, per validator and slot. -/
abbrev VTab (V : Type*) := V → Slot → Finset Blk

/-- A view: known blocks together with a vote table. Merge (`⊔`) is the
componentwise union. -/
abbrev Vw (V : Type*) := Finset Blk × VTab V

variable {V : Type*}

/-- The view carrying just a proposal for `b`: `b` and its history become
known, no votes. -/
def blockViewV (V : Type*) (b : Blk) : Vw V := (b.down, fun _ _ => ∅)

theorem sup_blockViewV (W : Vw V) (b : Blk) :
    W ⊔ blockViewV V b = (W.1 ∪ b.down, W.2) := by
  refine Prod.ext rfl ?_
  funext u u'
  exact Finset.union_empty _

/-- A block is *seen* in a known set if it, or a descendant, is known — in the
real protocol blocks carry their history, so a seen block's ancestor chain is
available. Genesis is seen for free. Votes are counted only for seen
targets. -/
def okBlk (K : Finset Blk) : Blk → Prop
  | gen => True
  | bA => bA ∈ K ∨ bC ∈ K
  | bB => bB ∈ K
  | bC => bC ∈ K

instance (K : Finset Blk) : (b : Blk) → Decidable (okBlk K b)
  | gen => .isTrue trivial
  | bA => inferInstanceAs (Decidable (_ ∨ _))
  | bB => inferInstanceAs (Decidable (_ ∈ _))
  | bC => inferInstanceAs (Decidable (_ ∈ _))

theorem okBlk_mono {K K' : Finset Blk} (h : K ⊆ K') :
    ∀ {b : Blk}, okBlk K b → okBlk K' b
  | gen, _ => trivial
  | bA, hb => hb.imp (@h bA) (@h bC)
  | bB, hb => h hb
  | bC, hb => h hb

/-- Seen-ness is closed under ancestors. -/
theorem okBlk_of_le {K : Finset Blk} :
    ∀ {a b : Blk}, a ≤ b → okBlk K b → okBlk K a := by
  intro a b
  cases a <;> cases b <;> intro hab hb <;>
    first
    | trivial
    | exact absurd hab (by decide)
    | exact hb
    | exact Or.inl hb
    | exact Or.inr hb

/-- How seen-ness changes when a proposal's history is merged in. -/
theorem okBlk_union_down (K : Finset Blk) (b : Blk) :
    ∀ x : Blk, okBlk (K ∪ b.down) x ↔ okBlk K x ∨ x ≤ b := by
  intro x
  cases x <;> cases b <;>
    simp [okBlk, Blk.down, le_iff_ble, Blk.ble]

/-! ## The operational `FIL_rlmd` -/

/-- The in-window slots at which votes from `T` have been seen: the candidates
for the latest message. Raw (`K`-independent). -/
def cand (T : Slot → Finset Blk) (η s : ℕ) : Finset ℕ :=
  (Finset.range s).filter fun u' => s ≤ u' + η ∧ T u' ≠ ∅

theorem mem_cand {T : Slot → Finset Blk} {η s u' : ℕ} :
    u' ∈ cand T η s ↔ u' < s ∧ s ≤ u' + η ∧ T u' ≠ ∅ := by
  simp only [cand, Finset.mem_filter, Finset.mem_range, and_assoc]

/-- The counted vote extracted from one validator's table: at the latest
in-window slot with votes seen, count the vote iff it is unique (equivocation
discounting, `FIL_eq`) and its target is seen. Selection and discounting are
raw, so growing `K` only *adds* counted votes. -/
noncomputable def voteOf1 (K : Finset Blk) (T : Slot → Finset Blk)
    (η s : ℕ) : Option Blk :=
  if h : (cand T η s).Nonempty then
    if h2 : ∃ b : Blk, T ((cand T η s).max' h) = {b} ∧ okBlk K b then
      some h2.choose
    else none
  else none

theorem voteOf1_some {K : Finset Blk} {T : Slot → Finset Blk} {η s : ℕ}
    {b : Blk} (h : voteOf1 K T η s = some b) :
    ∃ hne : (cand T η s).Nonempty,
      T ((cand T η s).max' hne) = {b} ∧ okBlk K b := by
  unfold voteOf1 at h
  split_ifs at h with h1 h2
  obtain ⟨hT, hok⟩ := h2.choose_spec
  have hb : h2.choose = b := Option.some.inj h
  exact ⟨h1, hb ▸ hT, hb ▸ hok⟩

/-- Evaluation: if `L` is the maximal candidate slot and carries the single
seen vote `b`, the counted vote is `b`. -/
theorem voteOf1_eq_some {K : Finset Blk} {T : Slot → Finset Blk} {η s L : ℕ}
    {b : Blk} (hL : L ∈ cand T η s) (hmax : ∀ u' ∈ cand T η s, u' ≤ L)
    (hTb : T L = {b}) (hok : okBlk K b) :
    voteOf1 K T η s = some b := by
  have hne : (cand T η s).Nonempty := ⟨L, hL⟩
  have hLmax : (cand T η s).max' hne = L :=
    le_antisymm (hmax _ ((cand T η s).max'_mem hne)) (Finset.le_max' _ L hL)
  have hex : ∃ b : Blk, T ((cand T η s).max' hne) = {b} ∧ okBlk K b :=
    ⟨b, by rw [hLmax]; exact hTb, hok⟩
  unfold voteOf1
  rw [dif_pos hne, dif_pos hex]
  have h' : T L = {hex.choose} := by
    rw [← hLmax]
    exact hex.choose_spec.1
  exact congrArg some (Finset.singleton_injective (h'.symm.trans hTb))

/-- Evaluation: if the maximal candidate slot carries no single seen vote, the
validator is discounted. -/
theorem voteOf1_eq_none {K : Finset Blk} {T : Slot → Finset Blk} {η s L : ℕ}
    (hL : L ∈ cand T η s) (hmax : ∀ u' ∈ cand T η s, u' ≤ L)
    (h : ∀ b : Blk, ¬(T L = {b} ∧ okBlk K b)) :
    voteOf1 K T η s = none := by
  have hne : (cand T η s).Nonempty := ⟨L, hL⟩
  have hLmax : (cand T η s).max' hne = L :=
    le_antisymm (hmax _ ((cand T η s).max'_mem hne)) (Finset.le_max' _ L hL)
  have hno : ¬∃ b : Blk, T ((cand T η s).max' hne) = {b} ∧ okBlk K b := by
    rintro ⟨b, hTb, hok⟩
    rw [hLmax] at hTb
    exact h b ⟨hTb, hok⟩
  unfold voteOf1
  rw [dif_pos hne, dif_neg hno]

/-- Evaluation: no candidate slots, no counted vote. -/
theorem voteOf1_eq_none_of_empty {K : Finset Blk} {T : Slot → Finset Blk}
    {η s : ℕ} (h : cand T η s = ∅) : voteOf1 K T η s = none := by
  unfold voteOf1
  rw [dif_neg (by simp [h])]

/-- Growing the known set only turns `none` into `some` (for a newly seen
target), never changes or removes a counted vote. -/
theorem voteOf1_grow {K K' : Finset Blk} (hK : K ⊆ K')
    (T : Slot → Finset Blk) (η s : ℕ) :
    voteOf1 K' T η s = voteOf1 K T η s ∨
    (voteOf1 K T η s = none ∧
      ∃ b, voteOf1 K' T η s = some b ∧ ¬okBlk K b) := by
  by_cases h1 : (cand T η s).Nonempty
  · have hLmem : (cand T η s).max' h1 ∈ cand T η s := (cand T η s).max'_mem h1
    have hLmax : ∀ u' ∈ cand T η s, u' ≤ (cand T η s).max' h1 :=
      fun u' hu' => Finset.le_max' _ u' hu'
    by_cases h2 : ∃ b : Blk, T ((cand T η s).max' h1) = {b} ∧ okBlk K b
    · obtain ⟨b, hTb, hok⟩ := h2
      left
      rw [voteOf1_eq_some hLmem hLmax hTb (okBlk_mono hK hok),
        voteOf1_eq_some hLmem hLmax hTb hok]
    · have hnone : voteOf1 K T η s = none :=
        voteOf1_eq_none hLmem hLmax fun b hb => h2 ⟨b, hb⟩
      by_cases h3 : ∃ b : Blk, T ((cand T η s).max' h1) = {b} ∧ okBlk K' b
      · obtain ⟨b, hTb, hok'⟩ := h3
        right
        exact ⟨hnone, b, voteOf1_eq_some hLmem hLmax hTb hok',
          fun hok => h2 ⟨b, hTb, hok⟩⟩
      · left
        rw [hnone, voteOf1_eq_none hLmem hLmax fun b hb => h3 ⟨b, hb⟩]
  · left
    rw [voteOf1_eq_none_of_empty (Finset.not_nonempty_iff_eq_empty.mp h1),
      voteOf1_eq_none_of_empty (Finset.not_nonempty_iff_eq_empty.mp h1)]

/-- The counted vote of validator `u` in view `W` at slot `s`. -/
noncomputable def voteOfV {V : Type*} (W : Vw V) (η s : ℕ) (u : V) : Option Blk :=
  voteOf1 W.1 (W.2 u) η s

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The counted-vote multiset of a view at a slot: one vote per validator. -/
noncomputable def votesV (W : Vw V) (η s : ℕ) : Multiset Blk :=
  ∑ u : V, ((voteOfV W η s u).elim 0 fun b => {b})

open Classical in
theorem weight_votesV_eq (W : Vw V) (η s : ℕ) (X : Blk) :
    weight X (votesV W η s) =
      (Finset.univ.filter fun u : V =>
        ∃ b, voteOfV W η s u = some b ∧ X ≤ b).card := by
  classical
  unfold votesV
  induction (Finset.univ : Finset V) using Finset.cons_induction with
  | empty => simp
  | cons u t hu ih =>
    rw [Finset.sum_cons, weight_add, ih, Finset.filter_cons]
    by_cases hvote : ∃ b, voteOfV W η s u = some b ∧ X ≤ b
    · obtain ⟨b, hb, hXb⟩ := hvote
      rw [if_pos ⟨b, hb, hXb⟩, hb, Finset.card_cons]
      simp [weight_singleton_of_le hXb, Nat.add_comm]
    · rw [if_neg hvote]
      rcases hb : voteOfV W η s u with - | b
      · simp
      · have hnXb : ¬X ≤ b := fun hXb => hvote ⟨b, hb, hXb⟩
        simp [weight_singleton_of_not_le hnXb]

open Classical in
theorem card_votesV_eq (W : Vw V) (η s : ℕ) :
    (votesV W η s).card =
      (Finset.univ.filter fun u : V => (voteOfV W η s u).isSome).card := by
  classical
  unfold votesV
  induction (Finset.univ : Finset V) using Finset.cons_induction with
  | empty => simp
  | cons u t hu ih =>
    rw [Finset.sum_cons, Multiset.card_add, ih, Finset.filter_cons]
    rcases hb : voteOfV W η s u with - | b
    · rw [if_neg (by simp)]
      simp
    · rw [if_pos (by simp), Finset.card_cons]
      simp [Nat.add_comm]

/-- Bookkeeping for `RLMDGhostBase.count_le_weight`. -/
theorem count_le_weight_votesV (W : Vw V) (η s : ℕ) (X : Blk)
    (A : Finset V) (h : ∀ u ∈ A, ∃ b, X ≤ b ∧ voteOfV W η s u = some b) :
    A.card ≤ weight X (votesV W η s) := by
  classical
  rw [weight_votesV_eq]
  apply Finset.card_le_card
  intro u hu
  obtain ⟨b, hXb, hb⟩ := h u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, b, hb, hXb⟩

/-- Bookkeeping for `RLMDGhostBase.card_le_weight_add`. -/
theorem card_votesV_le_weight_add (W : Vw V) (η s : ℕ) (X : Blk)
    (A : Finset V)
    (h : ∀ u b, voteOfV W η s u = some b → ¬X ≤ b → u ∈ A) :
    (votesV W η s).card ≤ weight X (votesV W η s) + A.card := by
  classical
  rw [card_votesV_eq, weight_votesV_eq]
  have hsub : (Finset.univ.filter fun u : V => (voteOfV W η s u).isSome) ⊆
      (Finset.univ.filter fun u : V =>
        ∃ b, voteOfV W η s u = some b ∧ X ≤ b) ∪ A := by
    intro u hu
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hu).2
    by_cases hXb : X ≤ b
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ u, b, hb, hXb⟩)
    · exact Finset.mem_union_right _ (h u b hb hXb)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Bookkeeping for `RLMDGhostBase.weight_le_contrib`: if every counted vote
for a descendant of `X` comes from `A`, then `w(X, ·) ≤ |A|`. -/
theorem weight_votesV_le_contrib (W : Vw V) (η s : ℕ) (X : Blk)
    (A : Finset V)
    (h : ∀ u b, voteOfV W η s u = some b → X ≤ b → u ∈ A) :
    weight X (votesV W η s) ≤ A.card := by
  classical
  rw [weight_votesV_eq]
  apply Finset.card_le_card
  intro u hu
  obtain ⟨-, b, hb, hXb⟩ := Finset.mem_filter.mp hu
  exact h u b hb hXb

/-- Counted votes target seen blocks: positive weight forces seen-ness. -/
theorem ok_of_weight_pos {W : Vw V} {η s : ℕ} {X : Blk}
    (h : 0 < weight X (votesV W η s)) : okBlk W.1 X := by
  classical
  rw [weight_votesV_eq] at h
  obtain ⟨u, hu⟩ := Finset.card_pos.mp h
  obtain ⟨-, b, hb, hXb⟩ := Finset.mem_filter.mp hu
  obtain ⟨-, -, hok⟩ := voteOf1_some hb
  exact okBlk_of_le hXb hok

/-- Unseen blocks carry no weight. -/
theorem weight_eq_zero_of_not_ok {W : Vw V} {η s : ℕ} {X : Blk}
    (h : ¬okBlk W.1 X) : weight X (votesV W η s) = 0 := by
  by_contra hne
  exact h (ok_of_weight_pos (Nat.pos_of_ne_zero hne))

/-- Counted votes are monotone under view growth (same table, larger known
set): the weight of every block can only grow. -/
theorem weight_mono_known {K K' : Finset Blk} (hK : K ⊆ K') (T : VTab V)
    (η s : ℕ) (X : Blk) :
    weight X (votesV (K, T) η s) ≤ weight X (votesV (K', T) η s) := by
  classical
  rw [weight_votesV_eq, weight_votesV_eq]
  apply Finset.card_le_card
  intro u hu
  obtain ⟨-, b, hb, hXb⟩ := Finset.mem_filter.mp hu
  have hb' : voteOf1 K (T u) η s = some b := hb
  rcases voteOf1_grow hK (T u) η s with heq | ⟨hnone, -⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ u, b, (heq.trans hb' : voteOfV (K', T) η s u = some b), hXb⟩
  · exact absurd (hnone.symm.trans hb') (by simp)

/-- If no newly seen target lies in the subtree of `X`, the weight of `X` is
unchanged by growing the known set. -/
theorem weight_stable_known {K K' : Finset Blk} (hK : K ⊆ K') (T : VTab V)
    (η s : ℕ) (X : Blk)
    (h : ∀ b, okBlk K' b → ¬okBlk K b → ¬X ≤ b) :
    weight X (votesV (K', T) η s) = weight X (votesV (K, T) η s) := by
  classical
  rw [weight_votesV_eq, weight_votesV_eq]
  congr 1
  apply Finset.Subset.antisymm
  · intro u hu
    obtain ⟨-, b, hb, hXb⟩ := Finset.mem_filter.mp hu
    have hb' : voteOf1 K' (T u) η s = some b := hb
    rcases voteOf1_grow hK (T u) η s with heq | ⟨-, b', hb'', hnok⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ u, b, (heq.symm.trans hb' : voteOfV (K, T) η s u = some b), hXb⟩
    · have hbb : b' = b := Option.some.inj (hb''.symm.trans hb')
      obtain ⟨-, -, hok'⟩ := voteOf1_some hb'
      exact absurd hXb (h b hok' (hbb ▸ hnok))
  · intro u hu
    obtain ⟨-, b, hb, hXb⟩ := Finset.mem_filter.mp hu
    have hb' : voteOf1 K (T u) η s = some b := hb
    rcases voteOf1_grow hK (T u) η s with heq | ⟨hnone, -⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ u, b, (heq.trans hb' : voteOfV (K', T) η s u = some b), hXb⟩
    · exact absurd (hnone.symm.trans hb') (by simp)

/-! ## The concrete GHOST fork choice -/

open Classical in
/-- GHOST on the four-block tree over the counted votes of a view: descend to
the seen heavier branch at the genesis fork (ties toward `bA`), then to `bC`
if seen. -/
noncomputable def fcV (W : Vw V) (η s : ℕ) : Blk :=
  if okBlk W.1 bA ∧
      ¬(weight bA (votesV W η s) < weight bB (votesV W η s) ∧ okBlk W.1 bB) then
    (if okBlk W.1 bC then bC else bA)
  else if okBlk W.1 bB then bB else gen

/-- The concrete fork choice satisfies the GHOST-descent characterization. -/
theorem fcV_ghost (W : Vw V) (η s : ℕ) :
    GhostSelects (votesV W η s) (fcV W η s) := by
  classical
  constructor
  · intro P B' B'' hc' hc'' hle
    rcases covBy_cases hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases covBy_cases hc'' with ⟨hP2, rfl⟩ | ⟨hP2, rfl⟩ | ⟨hP2, rfl⟩
    · exact le_refl _
    · -- fork at gen, descent went to bB against bA
      have hout : fcV W η s = bB := le_bB_iff.mp hle
      by_cases hA : okBlk W.1 bA ∧
          ¬(weight bA (votesV W η s) < weight bB (votesV W η s) ∧
            okBlk W.1 bB)
      · unfold fcV at hout
        rw [if_pos hA] at hout
        split_ifs at hout <;> exact absurd hout (by decide)
      · rw [not_and_or, not_not] at hA
        rcases hA with hA | hA
        · rw [weight_eq_zero_of_not_ok hA]
          exact Nat.zero_le _
        · exact le_of_lt hA.1
    · exact absurd hP2 (by decide)
    · -- fork at gen, descent went to the bA side against bB
      have hout : fcV W η s = bA ∨ fcV W η s = bC := le_bA_iff.mp hle
      have h1 : okBlk W.1 bA ∧
          ¬(weight bA (votesV W η s) < weight bB (votesV W η s) ∧
            okBlk W.1 bB) := by
        by_contra h1
        unfold fcV at hout
        rcases hout with hout | hout <;> rw [if_neg h1] at hout <;>
          split_ifs at hout <;> simp_all
      by_cases hB : okBlk W.1 bB
      · exact Nat.le_of_not_lt fun hlt => h1.2 ⟨hlt, hB⟩
      · rw [weight_eq_zero_of_not_ok hB]
        exact Nat.zero_le _
    · exact le_refl _
    · exact absurd hP2 (by decide)
    · exact absurd hP2 (by decide)
    · exact absurd hP2 (by decide)
    · exact le_refl _
  · intro Y hc
    rcases covBy_cases hc with ⟨hP, rfl⟩ | ⟨hP, rfl⟩ | ⟨hP, rfl⟩
    · -- output gen, cover bA: the bA branch is unseen
      unfold fcV at hP
      by_cases hA : okBlk W.1 bA ∧
          ¬(weight bA (votesV W η s) < weight bB (votesV W η s) ∧
            okBlk W.1 bB)
      · rw [if_pos hA] at hP
        split_ifs at hP <;> exact absurd hP (by decide)
      · rw [if_neg hA] at hP
        by_cases hB : okBlk W.1 bB
        · rw [if_pos hB] at hP
          exact absurd hP (by decide)
        · rw [not_and_or, not_not] at hA
          rcases hA with hA | hA
          · exact weight_eq_zero_of_not_ok hA
          · exact absurd hA.2 hB
    · -- output gen, cover bB: bB is unseen
      unfold fcV at hP
      by_cases hA : okBlk W.1 bA ∧
          ¬(weight bA (votesV W η s) < weight bB (votesV W η s) ∧
            okBlk W.1 bB)
      · rw [if_pos hA] at hP
        split_ifs at hP <;> exact absurd hP (by decide)
      · rw [if_neg hA] at hP
        by_cases hB : okBlk W.1 bB
        · rw [if_pos hB] at hP
          exact absurd hP (by decide)
        · exact weight_eq_zero_of_not_ok hB
    · -- output bA, cover bC: bC is unseen
      unfold fcV at hP
      by_cases hA : okBlk W.1 bA ∧
          ¬(weight bA (votesV W η s) < weight bB (votesV W η s) ∧
            okBlk W.1 bB)
      · rw [if_pos hA] at hP
        by_cases hC : okBlk W.1 bC
        · rw [if_pos hC] at hP
          exact absurd hP (by decide)
        · exact weight_eq_zero_of_not_ok hC
      · rw [if_neg hA] at hP
        split_ifs at hP <;> exact absurd hP (by decide)

/-! ### The §2 consistency property -/

theorem le_bA_cases : ∀ {x : Blk}, x ≤ bA → x = gen ∨ x = bA := by decide
theorem le_bB_cases : ∀ {x : Blk}, x ≤ bB → x = gen ∨ x = bB := by decide

/-- Core of the consistency cases landing on `bC`: if the `bA` side won the
genesis fork before the merge, it still wins after `bC`'s history is merged in
(`bB` gains nothing, the `bA` side only grows), and the descent reaches the
now-seen `bC`. -/
private theorem consistency_to_bC {K : Finset Blk} {T : VTab V} {η s : ℕ}
    (h1 : okBlk K bA ∧
      ¬(weight bA (votesV (K, T) η s) < weight bB (votesV (K, T) η s) ∧
        okBlk K bB)) :
    fcV ((K ∪ bC.down, T) : Vw V) η s = bC := by
  classical
  have hok' := okBlk_union_down K bC
  have hB' : weight bB (votesV (K ∪ bC.down, T) η s) =
      weight bB (votesV (K, T) η s) := by
    apply weight_stable_known Finset.subset_union_left
    intro x hx hnx hBx
    rcases (hok' x).mp hx with h | h
    · exact hnx h
    · exact absurd (hBx.trans h) (by decide)
  have hAmono : weight bA (votesV (K, T) η s) ≤
      weight bA (votesV (K ∪ bC.down, T) η s) :=
    weight_mono_known Finset.subset_union_left T η s bA
  have hBiff : okBlk (K ∪ bC.down) bB ↔ okBlk K bB := by
    rw [hok' bB]; exact or_iff_left (by decide)
  have hcond : okBlk (K ∪ bC.down) bA ∧
      ¬(weight bA (votesV (K ∪ bC.down, T) η s) <
          weight bB (votesV (K ∪ bC.down, T) η s) ∧
        okBlk (K ∪ bC.down) bB) := by
    refine ⟨(hok' bA).mpr (Or.inl h1.1), ?_⟩
    rintro ⟨hlt, hB⟩
    rw [hB'] at hlt
    exact h1.2 ⟨lt_of_le_of_lt hAmono hlt, hBiff.mp hB⟩
  unfold fcV
  rw [if_pos hcond, if_pos ((hok' bC).mpr (Or.inr le_rfl))]

/-- The §2 consistency property for the concrete fork choice: merging in a
proposal that extends the current output makes it the new output. -/
theorem fcV_consistency (W : Vw V) (η s : ℕ) (b : Blk)
    (hle : fcV W η s ≤ b) : fcV (W ⊔ blockViewV V b) η s = b := by
  classical
  rw [sup_blockViewV]
  obtain ⟨K, T⟩ := W
  simp only at hle ⊢
  by_cases h1 : okBlk K bA ∧
      ¬(weight bA (votesV (K, T) η s) < weight bB (votesV (K, T) η s) ∧
        okBlk K bB)
  case pos =>
    by_cases h2 : okBlk K bC
    case pos =>
      -- previous output bC: only b = bC extends it
      unfold fcV at hle
      rw [if_pos h1, if_pos h2] at hle
      rw [le_bC_iff.mp hle]
      exact consistency_to_bC h1
    case neg =>
      -- previous output bA: b = bA or b = bC
      unfold fcV at hle
      rw [if_pos h1, if_neg h2] at hle
      rcases le_bA_iff.mp hle with hb | hb
      · subst hb
        have hok' := okBlk_union_down K bA
        have hnone : ∀ x : Blk, okBlk (K ∪ bA.down) x → okBlk K x := by
          intro x hx
          rcases (hok' x).mp hx with h | h
          · exact h
          · rcases le_bA_cases h with rfl | rfl
            · trivial
            · exact h1.1
        have hA' : weight bA (votesV (K ∪ bA.down, T) η s) =
            weight bA (votesV (K, T) η s) :=
          weight_stable_known Finset.subset_union_left T η s bA
            fun x hx hnx => absurd (hnone x hx) hnx
        have hB' : weight bB (votesV (K ∪ bA.down, T) η s) =
            weight bB (votesV (K, T) η s) :=
          weight_stable_known Finset.subset_union_left T η s bB
            fun x hx hnx => absurd (hnone x hx) hnx
        have hBiff : okBlk (K ∪ bA.down) bB ↔ okBlk K bB := by
          rw [hok' bB]; exact or_iff_left (by decide)
        have hCiff : okBlk (K ∪ bA.down) bC ↔ okBlk K bC := by
          rw [hok' bC]; exact or_iff_left (by decide)
        have hcond : okBlk (K ∪ bA.down) bA ∧
            ¬(weight bA (votesV (K ∪ bA.down, T) η s) <
                weight bB (votesV (K ∪ bA.down, T) η s) ∧
              okBlk (K ∪ bA.down) bB) := by
          refine ⟨(hok' bA).mpr (Or.inl h1.1), ?_⟩
          rintro ⟨hlt, hB⟩
          rw [hA', hB'] at hlt
          exact h1.2 ⟨hlt, hBiff.mp hB⟩
        unfold fcV
        rw [if_pos hcond, if_neg (fun hC => h2 (hCiff.mp hC))]
      · subst hb
        exact consistency_to_bC h1
  case neg =>
   by_cases h3 : okBlk K bB
   case pos =>
    -- previous output bB: only b = bB extends it
    unfold fcV at hle
    rw [if_neg h1, if_pos h3] at hle
    rw [le_bB_iff.mp hle]
    have hok' := okBlk_union_down K bB
    have hnone : ∀ x : Blk, okBlk (K ∪ bB.down) x → okBlk K x := by
      intro x hx
      rcases (hok' x).mp hx with h | h
      · exact h
      · rcases le_bB_cases h with rfl | rfl
        · trivial
        · exact h3
    have hA' : weight bA (votesV (K ∪ bB.down, T) η s) =
        weight bA (votesV (K, T) η s) :=
      weight_stable_known Finset.subset_union_left T η s bA
        fun x hx hnx => absurd (hnone x hx) hnx
    have hB' : weight bB (votesV (K ∪ bB.down, T) η s) =
        weight bB (votesV (K, T) η s) :=
      weight_stable_known Finset.subset_union_left T η s bB
        fun x hx hnx => absurd (hnone x hx) hnx
    have hAiff : okBlk (K ∪ bB.down) bA ↔ okBlk K bA := by
      rw [hok' bA]; exact or_iff_left (by decide)
    have hB'ok : okBlk (K ∪ bB.down) bB := (hok' bB).mpr (Or.inr le_rfl)
    rw [not_and_or, not_not] at h1
    have hcondneg : ¬(okBlk (K ∪ bB.down) bA ∧
        ¬(weight bA (votesV (K ∪ bB.down, T) η s) <
            weight bB (votesV (K ∪ bB.down, T) η s) ∧
          okBlk (K ∪ bB.down) bB)) := by
      rintro ⟨hA, hno⟩
      rcases h1 with h1 | h1
      · exact h1 (hAiff.mp hA)
      · exact hno ⟨by rw [hA', hB']; exact h1.1, hB'ok⟩
    unfold fcV
    rw [if_neg hcondneg, if_pos hB'ok]
   case neg =>
    -- previous output gen: b is arbitrary
    rw [not_and_or, not_not] at h1
    have hnB : ¬okBlk K bB := h3
    have hnA : ¬okBlk K bA := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1.2 hnB
    have hnC : ¬okBlk K bC := fun hC => hnA (Or.inr hC)
    have hok' := okBlk_union_down K b
    cases b
    · -- b = gen
      have hAiff : okBlk (K ∪ gen.down) bA ↔ okBlk K bA := by
        rw [hok' bA]; exact or_iff_left (by decide)
      have hBiff : okBlk (K ∪ gen.down) bB ↔ okBlk K bB := by
        rw [hok' bB]; exact or_iff_left (by decide)
      unfold fcV
      rw [if_neg (fun h => hnA (hAiff.mp h.1)),
        if_neg (fun h => hnB (hBiff.mp h))]
    · -- b = bA
      have hBiff : okBlk (K ∪ bA.down) bB ↔ okBlk K bB := by
        rw [hok' bB]; exact or_iff_left (by decide)
      have hCiff : okBlk (K ∪ bA.down) bC ↔ okBlk K bC := by
        rw [hok' bC]; exact or_iff_left (by decide)
      have hcond : okBlk (K ∪ bA.down) bA ∧
          ¬(weight bA (votesV (K ∪ bA.down, T) η s) <
              weight bB (votesV (K ∪ bA.down, T) η s) ∧
            okBlk (K ∪ bA.down) bB) := by
        refine ⟨(hok' bA).mpr (Or.inr le_rfl), ?_⟩
        rintro ⟨-, hB⟩
        exact hnB (hBiff.mp hB)
      unfold fcV
      rw [if_pos hcond, if_neg (fun hC => hnC (hCiff.mp hC))]
    · -- b = bB
      have hAiff : okBlk (K ∪ bB.down) bA ↔ okBlk K bA := by
        rw [hok' bA]; exact or_iff_left (by decide)
      unfold fcV
      rw [if_neg (fun h => hnA (hAiff.mp h.1)),
        if_pos ((hok' bB).mpr (Or.inr le_rfl))]
    · -- b = bC
      have hBiff : okBlk (K ∪ bC.down) bB ↔ okBlk K bB := by
        rw [hok' bB]; exact or_iff_left (by decide)
      have hcond : okBlk (K ∪ bC.down) bA ∧
          ¬(weight bA (votesV (K ∪ bC.down, T) η s) <
              weight bB (votesV (K ∪ bC.down, T) η s) ∧
            okBlk (K ∪ bC.down) bB) := by
        refine ⟨(hok' bA).mpr (Or.inr (by decide)), ?_⟩
        rintro ⟨-, hB⟩
        exact hnB (hBiff.mp hB)
      unfold fcV
      rw [if_pos hcond, if_pos ((hok' bC).mpr (Or.inr le_rfl))]

end Tightness

end RLMDGhost
