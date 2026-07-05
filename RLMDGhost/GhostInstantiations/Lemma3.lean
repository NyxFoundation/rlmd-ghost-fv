import RLMDGhost.Ghost

/-!
# Lemma 3 — vote majority for a descendant of `B` ⇒ GHOST outputs a descendant of `B`

> **Lemma 3** (arXiv:2302.11326). Let `V` be a view in which over a majority of
> the votes are for a descendant of a block `B`. Then, `GHOST(V, t)` is a
> descendant of `B`, i.e., `B` is in the canonical chain output by the GHOST
> fork-choice.

The paper argues per height: at every fork at height `≤ height(B)`, the branch
`B'` containing `B` carries the whole subtree of `B`, so
`w(B', M) > |M|/2 > w(B'', M)` for any competing sibling `B''` (their subtrees
are vote-disjoint), and GHOST selects `B'`. We render the height descent by
contradiction through the two fork-tree constructions of `RLMDGhost.Ghost`:

* if the output `C` were a strict *ancestor* of `B`, the child of `C` toward
  `B` carries at least `w(B, M) > |M|/2 > 0` weight, contradicting that the
  GHOST descent stops only at weightless children (`progress`);
* if `C` *conflicted* with `B`, then at the deepest common ancestor
  (`exists_fork`) the branch `B'` toward `B` has
  `w(B', M) ≥ w(B, M) > |M|/2`, while greedy descent through the conflicting
  sibling `B''` forces `w(B', M) ≤ w(B'', M)`; vote-disjointness
  (`weight_add_weight_le`) makes the two together exceed `|M|`.
-/

namespace RLMDGhost

open BlockTree

variable {Block : Type*} [BlockTree Block] [FiniteAncestors Block]

/-- **Lemma 3.** If strictly more than half of the counted votes `M` are for
descendants of `B` (`|M| < 2·w(B, M)`), then any GHOST output on `M` is a
descendant of `B`. -/
theorem lemma3 {M : Multiset Block} {B C : Block}
    (hmaj : M.card < 2 * weight B M) (hghost : GhostSelects M C) : B ≤ C := by
  by_contra hBC
  by_cases hcons : Consistent B C
  · rcases hcons with hle | hge
    · exact hBC hle
    · have hCB : C < B := lt_of_le_of_ne hge fun e => hBC (e ▸ le_rfl)
      obtain ⟨Y, hcov, hYB⟩ := exists_covBy_le hCB
      have h0 : weight Y M = 0 := hghost.progress hcov
      have hBY : weight B M ≤ weight Y M := weight_le_weight_of_le hYB M
      have hcard : weight B M ≤ M.card := weight_le_card B M
      omega
  · obtain ⟨P, B', B'', hcov', hcov'', hB'B, hB''C, hconf⟩ := exists_fork hcons
    have h1 : weight B M ≤ weight B' M := weight_le_weight_of_le hB'B M
    have h2 : weight B' M ≤ weight B'' M := hghost.choice_max hcov' hcov'' hB''C
    have h3 : weight B' M + weight B'' M ≤ M.card := weight_add_weight_le hconf M
    omega

/-- **Lemma 3, per-sibling form** (used by Lemma 5, §B). If `B` has positive
weight and strictly outweighs every *conflicting* block, then any GHOST output
on `M` is a descendant of `B`. Unlike `lemma3` this needs only a per-sibling
comparison, not an overall strict majority — the fast-confirmation quorum gives
`w(B) > n/3` while each conflicting block collects `≤ n/3`. -/
theorem canonical_of_conflict_lt {M : Multiset Block} {B C : Block}
    (hpos : 0 < weight B M)
    (hconf : ∀ B' : Block, Conflicts B B' → weight B' M < weight B M)
    (hghost : GhostSelects M C) : B ≤ C := by
  by_contra hBC
  by_cases hcons : Consistent B C
  · rcases hcons with hle | hge
    · exact hBC hle
    · have hCB : C < B := lt_of_le_of_ne hge fun e => hBC (e ▸ le_rfl)
      obtain ⟨Y, hcov, hYB⟩ := exists_covBy_le hCB
      have h0 : weight Y M = 0 := hghost.progress hcov
      have hBY : weight B M ≤ weight Y M := weight_le_weight_of_le hYB M
      omega
  · obtain ⟨P, B', B'', hcov', hcov'', hB'B, hB''C, hconf'⟩ := exists_fork hcons
    -- `B''` conflicts with `B`: else `B'` and `B''` would be consistent
    have hconfB : Conflicts B B'' := by
      rintro (hle | hle)
      · exact hconf' (Or.inl (hB'B.trans hle))
      · exact hconf' (consistent_of_le_of_le hB'B hle)
    have h1 : weight B M ≤ weight B' M := weight_le_weight_of_le hB'B M
    have h2 : weight B' M ≤ weight B'' M := hghost.choice_max hcov' hcov'' hB''C
    have h3 : weight B'' M < weight B M := hconf B'' hconfB
    omega

end RLMDGhost
