import Mathlib.Order.Lattice
import RLMDGhost.Basic

/-!
# RLMD-GHOST — abstract propose-vote-merge interface

Per Barrier 4 of `docs/formalization-strategy.md`, we do **not** implement
Algorithms 1–5 operationally. Instead the propose-vote-merge round structure,
view-merge, and the fork-choice function `FC` are captured by an abstract
interface: an `Execution` of observable data plus a `Spec` bundling the
protocol's defining behaviour as hypotheses. The §3.6 framework statements
(Lemma 1, Proposition 1, Theorems 1–2) are then *derived* from `Spec`.

Views are an abstract semilattice: `V ⊔ V'` is the merge (union) of two message
sets and `blockView B` the singleton view carrying the proposal message of `B`.
A concrete GHOST instantiation (`GHOST ∘ FIL_rlmd` with its filter family,
Barrier 4's second half) can later discharge every `Spec` field without changing
any theorem statement.

Every `Spec` field is a protocol *mechanic* (a consequence of Algorithms 1–5,
synchrony within a slot, and the joining protocol), never a consequence of a
numbered statement — so deriving the numbered statements from `Spec` is
non-circular.
-/

namespace RLMDGhost

/-- The observable data of a propose-vote-merge execution over a block tree
`Block`, a validator type `Validator`, and a view semilattice `View`.

`active` means *honest and active* in the generalized sleepy model: the
validator has completed the joining protocol, so it participates and its
canonical chain is meaningful. Adversarial validators are outside `active`;
their influence enters only through which `Spec` hypotheses hold. -/
structure Execution (Block Validator View : Type*) [BlockTree Block]
    [SemilatticeSup View] where
  /-- Network delay bound `∆`; one slot spans `3∆` rounds. -/
  Δ : ℕ
  /-- `∆` is positive. -/
  Δ_pos : 0 < Δ
  /-- `view v r`: the local view (set of received messages) of validator `v` at
  round `r`, before any merge event of that round. -/
  view : Validator → Round → View
  /-- `active v r`: validator `v` is honest and active (post-joining) at round
  `r`. -/
  active : Validator → Round → Prop
  /-- `pivot t`: slot `t` has an honest proposer active at its proposing round
  `3∆t` (the pivot-slot notion of Lemma 1/2). -/
  pivot : Slot → Prop
  /-- `proposerView t`: the view `V_p` of slot `t`'s proposer at round `3∆t`
  (meaningful when `pivot t`). -/
  proposerView : Slot → View
  /-- `proposal t`: the block `B` proposed at slot `t` (meaningful when
  `pivot t`). -/
  proposal : Slot → Block
  /-- `blockView B`: the singleton view carrying the proposal message of `B`,
  so that `V ⊔ blockView B` is the paper's `V ∪ {B}`. -/
  blockView : Block → View
  /-- The fork-choice function `FC(V, t)` (§2): the canonical-chain tip that
  view `V` determines at slot `t`. -/
  FC : View → Slot → Block
  /-- `votesFor v t B`: honest validator `v` casts its slot-`t` vote for `B`. -/
  votesFor : Validator → Slot → Block → Prop
  /-- `chAt v r`: the tip of the canonical chain `ch^r_v` of validator `v` at
  round `r`; "`B` is in the canonical chain" is rendered as `B ≤ chAt v r`. -/
  chAt : Validator → Round → Block

namespace Execution

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  (E : Execution Block Validator View)

/-- Proposing round of slot `t`: `3∆t`. -/
def slotStart (t : Slot) : Round := 3 * E.Δ * t

/-- Voting round of slot `t`: `3∆t + ∆`. -/
def voteRound (t : Slot) : Round := 3 * E.Δ * t + E.Δ

/-- Merge round of slot `t`: `3∆t + 2∆`. -/
def mergeRound (t : Slot) : Round := 3 * E.Δ * t + 2 * E.Δ

/-- `v ∈ H_t`: an honest voter of slot `t` is an honest validator active at the
voting round `3∆t + ∆`. -/
def voter (v : Validator) (t : Slot) : Prop := E.active v (E.voteRound t)

/-- The proposed view `V_p ∪ {B}` broadcast by slot `t`'s proposer. -/
def proposedView (t : Slot) : View := E.proposerView t ⊔ E.blockView (E.proposal t)

/-- `v` casts its slot-`t` vote for some descendant of `B`. -/
def votesForDescendant (v : Validator) (t : Slot) (B : Block) : Prop :=
  ∃ B', B ≤ B' ∧ E.votesFor v t B'

theorem votesForDescendant.of_votesFor {E : Execution Block Validator View}
    {v : Validator} {t : Slot} {B : Block} (h : E.votesFor v t B) :
    E.votesForDescendant v t B :=
  ⟨B, le_rfl, h⟩

end Execution

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]

/-- The abstract protocol specification: the defining behaviour of a
propose-vote-merge protocol (Algorithm 1), view-merge, the §2 consistency
property of `FC`, and synchronous delivery, stated as hypotheses. The §3.6
statements are derived from `Spec` together with `Persistence` (Proposition 1,
established per protocol) and the pivot-slot good event of Lemma 2. -/
structure Spec (E : Execution Block Validator View) : Prop where
  /-- **Consistency of the fork choice** (§2): adding to a view a block that
  extends its fork-choice output makes that block the new output. -/
  fc_consistency :
    ∀ (V : View) (t : Slot) (B : Block),
      E.FC V t ≤ B → E.FC (V ⊔ E.blockView B) t = B
  /-- **Honest proposal** (Algorithm 1, `PROPOSE`): in a pivot slot the honest
  proposer proposes a block extending the fork-choice output of its view `V_p`
  at round `3∆t`. -/
  proposal_extends :
    ∀ {t : Slot}, E.pivot t → E.FC (E.proposerView t) t ≤ E.proposal t
  /-- **Synchrony + joining protocol** (Lemma 1's delivery argument): an honest
  voter of slot `t` has been active since round `3∆(t−1) − 2∆`, so every message
  in its pre-merge view at round `3∆t + ∆` was delivered to the proposer by
  round `3∆t`: `V_i ⊆ V_p`. -/
  voter_view_le :
    ∀ {v : Validator} {t : Slot}, E.pivot t → E.voter v t →
      E.view v (E.voteRound t) ≤ E.proposerView t
  /-- **View-merge** (Algorithm 1, `VOTE`): in a pivot slot an honest voter
  merges the proposed view `V_p ∪ {B}` into its view and its canonical chain at
  the voting round is the fork-choice output of the merged view. -/
  chAt_pivot_merge :
    ∀ {v : Validator} {t : Slot}, E.pivot t → E.voter v t →
      E.chAt v (E.voteRound t) = E.FC (E.view v (E.voteRound t) ⊔ E.proposedView t) t
  /-- **Voting rule** (Algorithm 1, `VOTE`): an honest voter of slot `t` votes
  for the tip of its canonical chain at the voting round `3∆t + ∆` (the output
  of its fork choice there). -/
  vote_chAt :
    ∀ {v : Validator} {t : Slot}, E.voter v t →
      E.votesFor v t (E.chAt v (E.voteRound t))

/-- **Reorg resilience** (§3.1): every honest proposal — the proposal of a pivot
slot `t` — is in the canonical chain of every honest active validator at every
fork-choice round from `3∆t + ∆` on. Validators only update their canonical
chain at the rounds `{3∆s, 3∆s + ∆}`, so canonicity at those rounds for all
`s ≥ t` is reorg resilience. -/
def ReorgResilient (E : Execution Block Validator View) : Prop :=
  ∀ t : Slot, E.pivot t →
    (∀ s : Slot, t ≤ s → ∀ v : Validator, E.active v (E.voteRound s) →
      E.proposal t ≤ E.chAt v (E.voteRound s)) ∧
    (∀ s : Slot, t < s → ∀ v : Validator, E.active v (E.slotStart s) →
      E.proposal t ≤ E.chAt v (E.slotStart s))

end RLMDGhost
