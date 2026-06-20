import Mathlib.Order.Preorder.Chain
import Mathlib.Order.BoundedOrder.Basic

/-!
# RLMD-GHOST — basic types and the data layer

Core vocabulary shared by every numbered statement of *RLMD-GHOST*
(arXiv:2302.11326, CSF 2024): protocol slots/rounds (one slot spans `3∆`
rounds) and the block-tree prefix order `⪯` with its tree property, together
with the consistency/conflict relations used throughout the GHOST reasoning.

The generalized sleepy model lives in `RLMDGhost.Model`; the abstract
propose-vote-merge / GHOST / filter interface in `RLMDGhost.Protocol`; the
idealized-cryptography and pivot-slot good-event axioms in `RLMDGhost.Axioms`.
The subtree weight `w(B, M)` driving the GHOST fork-choice is introduced with
Lemma 3 (its only consumer).
-/

namespace RLMDGhost

/-- Protocol rounds. One RLMD-GHOST slot spans `3∆` rounds: a proposal round
`3∆t`, a vote round `3∆t+∆`, and a merge round `3∆t+2∆`. -/
abbrev Round := ℕ

/-- Protocol slots. -/
abbrev Slot := ℕ

/-! ## Block tree

Blocks are ordered by the ancestor / prefix relation `⪯` (`a ≤ b` means the
chain ending at `a` is a prefix of the chain ending at `b`). Genesis is the
global minimum `⊥`, and the ancestors of any block form a chain — a block has a
single linear history. -/
class BlockTree (Block : Type*) extends PartialOrder Block, OrderBot Block where
  /-- The set of ancestors of any block is totally ordered (the tree property). -/
  ancestors_isChain : ∀ b : Block, IsChain (· ≤ ·) {a : Block | a ≤ b}

namespace BlockTree

variable {Block : Type*} [BlockTree Block]

/-- Genesis block `B₀`: the global minimum of the prefix order. -/
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

/-- Any two ancestors of a common block are consistent (the tree property). The
workhorse for GHOST reasoning: blocks on the path to a common descendant never
conflict. -/
theorem consistent_of_le_of_le {a b c : Block} (ha : a ≤ c) (hb : b ≤ c) :
    Consistent a b := by
  rcases eq_or_ne a b with rfl | hne
  · exact Consistent.rfl a
  · exact ancestors_isChain c ha hb hne

/-- `a ≤ b` always implies the two are consistent. -/
theorem consistent_of_le {a b : Block} (h : a ≤ b) : Consistent a b := Or.inl h

end BlockTree

end RLMDGhost
