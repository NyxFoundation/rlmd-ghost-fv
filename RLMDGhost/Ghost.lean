import Mathlib.Data.Multiset.Filter
import Mathlib.Order.Cover
import Mathlib.Order.Preorder.Finite
import RLMDGhost.Basic

/-!
# RLMD-GHOST — the GHOST weight layer

The §4 GHOST instantiations reason about the vote-weight function `w(B, M)` (the
number of votes in `M` for descendants of `B`, glossary §2) and the greedy
heaviest-observed-subtree descent. This file provides:

* `weight B M` — the weight function over a `Multiset` of votes (each vote names
  its target block; the LMD/expiry/equivocation *filters* that decide which
  votes are counted live upstream, in whoever supplies `M`);
* `GhostSelects M C` — the defining property of a GHOST output: at every fork
  on its path the chosen branch is weight-maximal, and the descent stops only
  when no child carries weight;
* `FiniteAncestors` — each block has a finite history, giving the two fork-tree
  constructions the paper uses implicitly: the immediate successor toward a
  descendant (`exists_covBy_le`) and the deepest common ancestor of two
  conflicting blocks with its diverging covers (`exists_fork`).

Lemma 3 is proved from these in `RLMDGhost.GhostInstantiations.Lemma3`.
-/

namespace RLMDGhost

open BlockTree

variable {Block : Type*} [BlockTree Block]

/-! ## The weight function `w(B, M)` -/

open Classical in
/-- `w(B, M)` (§2): the number of votes in `M` cast for `B` or a descendant of
`B` — the total weight of the subtree rooted at `B`. -/
noncomputable def weight (B : Block) (M : Multiset Block) : ℕ :=
  (M.filter fun b => B ≤ b).card

open Classical in
theorem weight_def (B : Block) (M : Multiset Block) :
    weight B M = (M.filter fun b => B ≤ b).card := rfl

theorem weight_le_card (B : Block) (M : Multiset Block) : weight B M ≤ M.card := by
  classical
  rw [weight_def]
  exact Multiset.card_le_card (Multiset.filter_le _ M)

/-- Weight is antitone along the prefix order: votes for the subtree of a
descendant also count for every ancestor. -/
theorem weight_le_weight_of_le {B₁ B₂ : Block} (h : B₁ ≤ B₂) (M : Multiset Block) :
    weight B₂ M ≤ weight B₁ M := by
  classical
  rw [weight_def, weight_def]
  exact Multiset.card_le_card
    (Multiset.monotone_filter_right M fun b (hb : B₂ ≤ b) => h.trans hb)

/-- The subtrees of two conflicting blocks are vote-disjoint: no vote counts
for both, so their weights sum to at most the total number of votes. -/
theorem weight_add_weight_le {B' B'' : Block} (h : Conflicts B' B'')
    (M : Multiset Block) : weight B' M + weight B'' M ≤ M.card := by
  classical
  rw [weight_def, weight_def]
  rw [← Multiset.card_add]
  refine Multiset.card_le_card ?_
  rw [Multiset.le_iff_count]
  intro b
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
  by_cases h1 : B' ≤ b
  · by_cases h2 : B'' ≤ b
    · exact absurd (consistent_of_le_of_le h1 h2) h
    · simp [h1, h2]
  · by_cases h2 : B'' ≤ b <;> simp [h1, h2]

/-! ## The GHOST descent -/

/-- The defining property of a GHOST fork-choice output `C` on the counted
votes `M` (`GHOST(V, t)` after filtering, §2/§4):

* `choice_max` — greedy descent: at every block on the output's path, the child
  the descent continues through is weight-maximal among all children (ties are
  broken arbitrarily, so only `≤` is required);
* `progress` — the descent stops only when no child of the output carries any
  weight.

Any operational GHOST implementation satisfies both; the §4 statements only
need this characterization. -/
structure GhostSelects (M : Multiset Block) (C : Block) : Prop where
  choice_max :
    ∀ ⦃P B' B'' : Block⦄, P ⋖ B' → P ⋖ B'' → B'' ≤ C → weight B' M ≤ weight B'' M
  progress : ∀ ⦃Y : Block⦄, C ⋖ Y → weight Y M = 0

/-! ## Fork-tree constructions -/

/-- Every block has a finite history: the set of its ancestors is finite. This
is the (implicit) finiteness of blockchains that the paper's height-descent
argument for Lemma 3 uses. -/
class FiniteAncestors (Block : Type*) [BlockTree Block] : Prop where
  finite_ancestors : ∀ b : Block, {a : Block | a ≤ b}.Finite

variable [FiniteAncestors Block]

/-- Toward any strict descendant there is an immediate child: if `P < B` then
some cover `B₁` of `P` satisfies `B₁ ≤ B`. -/
theorem exists_covBy_le {P B : Block} (h : P < B) : ∃ B₁ : Block, P ⋖ B₁ ∧ B₁ ≤ B := by
  have hfin : {a : Block | P < a ∧ a ≤ B}.Finite :=
    (FiniteAncestors.finite_ancestors B).subset fun a ha => ha.2
  obtain ⟨B₁, hB₁, hmin⟩ := hfin.exists_minimal ⟨B, h, le_rfl⟩
  refine ⟨B₁, ⟨hB₁.1, fun X hPX hXB₁ => ?_⟩, hB₁.2⟩
  exact hXB₁.not_ge (hmin ⟨hPX, hXB₁.le.trans hB₁.2⟩ hXB₁.le)

/-- Two conflicting blocks fork at their deepest common ancestor: there are `P`
and covers `B'`, `B''` of `P` with `B' ≤ B`, `B'' ≤ C`, and `B'`, `B''`
themselves conflicting (vote-disjoint subtrees). -/
theorem exists_fork {B C : Block} (hconf : Conflicts B C) :
    ∃ P B' B'' : Block,
      P ⋖ B' ∧ P ⋖ B'' ∧ B' ≤ B ∧ B'' ≤ C ∧ Conflicts B' B'' := by
  have hfin : {a : Block | a ≤ B ∧ a ≤ C}.Finite :=
    (FiniteAncestors.finite_ancestors B).subset fun a ha => ha.1
  obtain ⟨P, hP, hmax⟩ := hfin.exists_maximal ⟨⊥, bot_le, bot_le⟩
  have hPB : P < B := lt_of_le_of_ne hP.1 fun e => hconf (Or.inl (e ▸ hP.2))
  have hPC : P < C := lt_of_le_of_ne hP.2 fun e => hconf (Or.inr (e ▸ hP.1))
  obtain ⟨B', hcov', hB'B⟩ := exists_covBy_le hPB
  obtain ⟨B'', hcov'', hB''C⟩ := exists_covBy_le hPC
  refine ⟨P, B', B'', hcov', hcov'', hB'B, hB''C, fun hcons => ?_⟩
  rcases hcons with hle | hge
  · exact hcov'.lt.not_ge (hmax ⟨hB'B, hle.trans hB''C⟩ hcov'.lt.le)
  · exact hcov''.lt.not_ge (hmax ⟨hge.trans hB'B, hB''C⟩ hcov''.lt.le)

end RLMDGhost
