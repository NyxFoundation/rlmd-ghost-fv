import Mathlib.Order.Preorder.Chain
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Real.Basic

/-!
# RLMD-GHOST — basic types and the data layer

Core types shared by every numbered statement of *Recent Latest Message Driven
GHOST* (arXiv:2302.11326, CSF 2024): the block-tree prefix order `⪯`, slots and
rounds of the `3∆`-slot structure, and the `Negligible` abstraction behind the
paper's "with overwhelming probability" claims.

Protocol mechanics (propose-vote-merge, the fork choice `FC`, view-merge) are an
abstract interface in `RLMDGhost.Protocol` (Barrier 4 of
`docs/formalization-strategy.md`); the probabilistic pivot-slot good event of
Lemma 2 is declared in `RLMDGhost.Axioms` (Barrier 1).
-/

namespace RLMDGhost

/-- Protocol rounds. One RLMD-GHOST slot spans `3∆` rounds: propose at `3∆t`,
vote at `3∆t + ∆`, merge at `3∆t + 2∆`. -/
abbrev Round := ℕ

/-- Protocol slots. -/
abbrev Slot := ℕ

/-! ## Block tree -/

/-- The carrier of blocks, ordered by the ancestor / prefix relation `⪯`.

`a ≤ b` (read `a ⪯ b`) means the chain ending at `a` is a prefix of the chain
ending at `b` — equivalently `a` is an ancestor of, or equal to, `b`. Genesis is
the global minimum `⊥`, and the set of ancestors of any block is a chain (the
tree property: a block has a single linear history). -/
class BlockTree (Block : Type*) extends PartialOrder Block, OrderBot Block where
  /-- The set of ancestors of any block is totally ordered (the tree property). -/
  ancestors_isChain : ∀ b : Block, IsChain (· ≤ ·) {a : Block | a ≤ b}

namespace BlockTree

variable {Block : Type*} [BlockTree Block]

/-- Genesis block `B_genesis`: the global minimum of the prefix order. -/
abbrev genesis : Block := ⊥

@[simp] theorem genesis_le (b : Block) : (genesis : Block) ≤ b := bot_le

/-- Two blocks are *consistent* if one is a prefix of the other (they lie on a
common chain). -/
def Consistent (a b : Block) : Prop := a ≤ b ∨ b ≤ a

/-- Two blocks *conflict* if neither is a prefix of the other. -/
def Conflicts (a b : Block) : Prop := ¬ Consistent a b

@[refl] theorem Consistent.rfl (a : Block) : Consistent a a := Or.inl le_rfl

theorem Consistent.symm {a b : Block} (h : Consistent a b) : Consistent b a := Or.symm h

theorem consistent_comm {a b : Block} : Consistent a b ↔ Consistent b a :=
  ⟨Consistent.symm, Consistent.symm⟩

/-- Genesis is consistent with every block. -/
theorem consistent_genesis (b : Block) : Consistent (genesis : Block) b :=
  Or.inl (genesis_le b)

/-- Any two ancestors of a common block are consistent (the tree property,
unpacked from `ancestors_isChain`). This is the workhorse for the safety half of
Theorem 2: blocks on the path to a common descendant never conflict. -/
theorem consistent_of_le_of_le {a b c : Block} (ha : a ≤ c) (hb : b ≤ c) :
    Consistent a b := by
  rcases eq_or_ne a b with rfl | hne
  · exact Consistent.rfl a
  · exact ancestors_isChain c ha hb hne

/-- `B ≤ B'` always implies the two are consistent. -/
theorem consistent_of_le {a b : Block} (h : a ≤ b) : Consistent a b := Or.inl h

end BlockTree

/-! ## Negligibility / overwhelming probability -/

/-- A real-valued sequence is *negligible* (`negl`) if it eventually decays
faster than every inverse polynomial in the security parameter.

The w.o.p. error term of Lemma 2 is negligible in `κ`; the composition API
belongs to the probabilistic layer that replaces the Lemma 2 axiom in Phase 2
(issue #21). -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, |f n| < 1 / (n : ℝ) ^ c

end RLMDGhost
