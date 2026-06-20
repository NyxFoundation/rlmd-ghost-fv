import RLMDGhost.Basic

/-!
# RLMD-GHOST — abstract propose-vote-merge / GHOST interface

Following Barrier 4 of the formalization strategy we do **not** implement
Algorithms 1–5 operationally. The propose-vote-merge round structure, the GHOST
fork-choice and the RLMD filter family are captured abstractly: an `Execution`
of observable per-round data, plus a `Spec` bundling the protocol's defining
behaviour (view-merge, the voting rule) as hypotheses. The reorg-resilience,
dynamic-availability and asynchrony-resilience theorems are then *derived* from
`Spec` together with the per-protocol `Proposition1Holds` property and the
pivot-slot good event (declared in `RLMDGhost.Axioms`).

A concrete `η = 1` (Goldfish) or `η = ∞` (LMD-GHOST) instantiation can later
discharge `Spec`'s fields without changing any theorem statement.
-/

namespace RLMDGhost

/-- The observable data of an RLMD-GHOST execution over a block tree `Block` and
a validator type `Validator`. Predicates are indexed by rounds/slots; the
fork-choice `forkChoice id r` is the output of `GHOST ∘ FIL_rlmd` on `id`'s
filtered view at round `r`. -/
structure Execution (Block Validator : Type*) [BlockTree Block] where
  /-- Network-delay bound `∆`; one slot spans `3∆` rounds. -/
  Δ : ℕ
  /-- `∆` is positive. -/
  Δ_pos : 0 < Δ
  /-- `active id r`: validator `id` is an active participant at round `r` (awake
  and past the joining protocol). -/
  active : Validator → Round → Prop
  /-- `honestAt id r`: `id` is honest at round `r` (corruption is monotone;
  used as a premise, not enforced here). -/
  honestAt : Validator → Round → Prop
  /-- `eligibleVote id t`: `id` won the vote lottery for slot `t`. -/
  eligibleVote : Validator → Slot → Prop
  /-- `eligiblePropose id t`: `id` won the proposer lottery for slot `t`. -/
  eligiblePropose : Validator → Slot → Prop
  /-- `votesFor id t B`: honest `id` casts its slot-`t` vote for block `B`. -/
  votesFor : Validator → Slot → Block → Prop
  /-- The block `id` proposes for slot `t` when it is the slot leader. -/
  proposalBlock : Validator → Slot → Block
  /-- RLMD-GHOST fork-choice output (`GHOST ∘ FIL_rlmd`): the canonical-chain tip
  in `id`'s filtered view at round `r`. -/
  forkChoice : Validator → Round → Block

namespace Execution

variable {Block Validator : Type*} [BlockTree Block] (E : Execution Block Validator)

/-! ## Round schedule (3∆ regime) -/

/-- Proposal round of slot `t`: `3∆t`. -/
def slotStart (t : Slot) : Round := 3 * E.Δ * t

/-- Vote round of slot `t`: `3∆t + ∆`. -/
def voteRound (t : Slot) : Round := 3 * E.Δ * t + E.Δ

/-- Merge round of slot `t`: `3∆t + 2∆`. -/
def mergeRound (t : Slot) : Round := 3 * E.Δ * t + 2 * E.Δ

/-! ## Derived participation / voting notions -/

/-- `id` is active and honest at round `r`. -/
def activeHonest (id : Validator) (r : Round) : Prop :=
  E.active id r ∧ E.honestAt id r

/-- **Honest voter of slot `t`** (`H_t`): active and honest at the vote round
`3∆t+∆` and eligible to vote at slot `t`. -/
def honestVoter (id : Validator) (t : Slot) : Prop :=
  E.activeHonest id (E.voteRound t) ∧ E.eligibleVote id t

/-- `id` casts its slot-`t` vote for some descendant of `B`. -/
def votesForDescendant (id : Validator) (t : Slot) (B : Block) : Prop :=
  ∃ B', B ≤ B' ∧ E.votesFor id t B'

theorem votesForDescendant_of_votesFor {id : Validator} {t : Slot} {B : Block}
    (h : E.votesFor id t B) : E.votesForDescendant id t B :=
  ⟨B, le_rfl, h⟩

/-- Block `B` is *canonical at round `r`*: it is a prefix of the fork-choice
output of every active validator at round `r`. -/
def Canonical (B : Block) (r : Round) : Prop :=
  ∀ a : Validator, E.active a r → B ≤ E.forkChoice a r

/-- **Pivot slot** (`Lemma 1`): a slot with an active honest eligible proposer.
Its proposal `proposalBlock vp t` is the honest proposal all honest voters
adopt via view-merge. Lemma 2 asserts a pivot slot exists in every `κ`-window. -/
def IsPivot (t : Slot) : Prop :=
  ∃ vp : Validator, E.eligiblePropose vp t ∧ E.honestAt vp (E.slotStart t)

end Execution

/-- The abstract protocol specification: the defining behaviour of the
propose-vote-merge round, view-merge and the RLMD-GHOST voting rule, stated as
hypotheses. Each field is a protocol *mechanic* (a consequence of the algorithms
and synchrony), never a consequence of a numbered lemma — so deriving the
numbered lemmas from `Spec` is non-circular. -/
structure Spec {Block Validator : Type*} [BlockTree Block]
    (E : Execution Block Validator) : Prop where
  /-- **Voting rule.** An active honest validator eligible to vote at slot `t`
  votes for the block its RLMD-GHOST fork-choice returns at the vote round
  `3∆t+∆`. -/
  vote_forkChoice :
    ∀ {id : Validator} {t : Slot},
      E.activeHonest id (E.voteRound t) → E.eligibleVote id t →
        E.votesFor id t (E.forkChoice id (E.voteRound t))
  /-- **View-merge at a pivot slot** (Lemma 1's mechanic). When slot `t` has an
  active honest eligible proposer `vp`, every honest voter merges `vp`'s proposed
  view before voting, so by the consistency of the fork-choice its vote-round
  fork choice is exactly `vp`'s proposed block. -/
  pivot_forkChoice :
    ∀ {vp id : Validator} {t : Slot},
      E.eligiblePropose vp t → E.honestAt vp (E.slotStart t) →
        E.activeHonest id (E.voteRound t) → E.eligibleVote id t →
          E.forkChoice id (E.voteRound t) = E.proposalBlock vp t

namespace Execution

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- An honest voter whose fork choice has `B` as a prefix votes for a descendant
of `B`: it votes for its fork-choice output (the voting rule), which is `≥ B`. -/
theorem votesForDescendant_of_canonical (S : Spec E) {B : Block} {t : Slot}
    (hcanon : E.Canonical B (E.voteRound t)) {id : Validator}
    (hid : E.honestVoter id t) : E.votesForDescendant id t B := by
  obtain ⟨⟨hactive, hhon⟩, helig⟩ := hid
  exact ⟨E.forkChoice id (E.voteRound t), hcanon id hactive,
    S.vote_forkChoice ⟨hactive, hhon⟩ helig⟩

end Execution

/-! ## Reorg resilience and Proposition 1 (the persistence property) -/

variable {Block Validator : Type*} [BlockTree Block]

/-- **Reorg resilience for an honest proposal `B` of slot `t`.** Every honest
voter of slot `t` votes for (a descendant of) `B`, and at every later slot `B`
stays canonical in the view of every active validator — i.e. the honest proposal
is never reorged out of the canonical chain. -/
def ReorgResilient (E : Execution Block Validator) (B : Block) (t : Slot) : Prop :=
  (∀ id : Validator, E.honestVoter id t → E.votesForDescendant id t B) ∧
    (∀ s : Slot, t < s → E.Canonical B (E.voteRound s))

/-- **Proposition 1 (persistence) holds for `E`.** Whenever all honest voters of
slot `t-1` vote for a descendant of `B`, block `B` is canonical in the view of
every active validator at the proposal and vote rounds of slot `t`. This property
is established *per protocol* (for RLMD-GHOST by Lemma 4 under `η`-compliance);
Theorem 1 derives reorg resilience from it. -/
def Proposition1Holds (E : Execution Block Validator) : Prop :=
  ∀ (B : Block) (t : Slot),
    (∀ id : Validator, E.honestVoter id (t - 1) → E.votesForDescendant id (t - 1) B) →
      E.Canonical B (E.slotStart t) ∧ E.Canonical B (E.voteRound t)

end RLMDGhost
