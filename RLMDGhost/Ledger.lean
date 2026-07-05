import RLMDGhost.Protocol

/-!
# RLMD-GHOST — the confirmed-ledger layer

The security statement (Definition 4, consumed by Theorem 2) talks about the
confirmed chain `Ch^r_v`: the `κ`-deep prefix of a validator's canonical chain
`ch^r_v`. This layer adds an abstract `Ledger` assignment — the confirmed-chain
function plus the consequences of the `κ`-deep confirmation rule that the
security proof uses — on top of the `Execution`/`Spec` interface, and the
Definition 4 `Safe`/`Live` predicates.

As with `Spec`, the confirmation rule is an abstract interface (Barrier 4): an
operational `κ`-truncation model can discharge these fields later without
changing the theorem statements. Depth is measured in slots, matching the
paper's usage ("since it is from a slot `≥ t − κ`, `Ch^r_i ⪯ B`"). The
statements are placed at the voting rounds `3∆s + ∆`, the fork-choice
checkpoints where canonical chains are updated.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]

/-- A confirmed-ledger assignment for an execution at confirmation depth `κ`.

`chain v r` is the confirmed chain `Ch^r_v` output by validator `v` at round
`r`. The fields record the consequences of the `κ`-deep confirmation rule; none
of them carries any security content (they constrain only how `chain` truncates
the validator's *own* canonical chain). -/
structure Ledger (E : Execution Block Validator View) (κ : ℕ) where
  /-- `Ch^r_v`: the confirmed chain output by validator `v` at round `r`. -/
  chain : Validator → Round → Block
  /-- The confirmed chain is a prefix of the validator's own canonical chain. -/
  chain_le_chAt :
    ∀ {v : Validator} {r : Round}, E.active v r → chain v r ≤ E.chAt v r
  /-- **`κ`-deep blocks are confirmed.** A canonical block proposed at slot `t'`
  with `t' + κ ≤ s` is `κ`-deep at slot `s`, hence in the confirmed chain. -/
  le_chain_of_deep :
    ∀ {v : Validator} {s t' : Slot}, E.active v (E.voteRound s) → t' + κ ≤ s →
      E.proposal t' ≤ E.chAt v (E.voteRound s) →
      E.proposal t' ≤ chain v (E.voteRound s)
  /-- **The confirmed chain is at most `κ` slots deep.** A canonical block
  proposed at slot `t'` with `s ≤ t' + κ` lies at or beyond the truncation
  point, so the confirmed chain is a prefix of it. -/
  chain_le_of_recent :
    ∀ {v : Validator} {s t' : Slot}, E.active v (E.voteRound s) → s ≤ t' + κ →
      E.proposal t' ≤ E.chAt v (E.voteRound s) →
      chain v (E.voteRound s) ≤ E.proposal t'
  /-- **Nothing is `κ`-deep before slot `κ`**: in the first `κ` slots the
  confirmed chain is still genesis. -/
  chain_genesis_early :
    ∀ {v : Validator} {s : Slot}, s < κ → E.active v (E.voteRound s) →
      chain v (E.voteRound s) = BlockTree.genesis

/-- **Safety** (Definition 4). Any two confirmed chains output by honest active
validators at fork-choice checkpoints are consistent (one is a prefix of the
other). -/
def Ledger.Safe {E : Execution Block Validator View} {κ : ℕ} (L : Ledger E κ) : Prop :=
  ∀ {s s' : Slot} {v v' : Validator},
    E.active v (E.voteRound s) → E.active v' (E.voteRound s') →
      BlockTree.Consistent (L.chain v (E.voteRound s)) (L.chain v' (E.voteRound s'))

/-- Transaction layer for the liveness statement: a transaction type, monotone
chain-membership, receipt, and the honest-proposer inclusion rule. Abstract
(Barrier 4). -/
structure TxModel (E : Execution Block Validator View) where
  /-- Transactions. -/
  Tx : Type*
  /-- `mem tx B`: `tx` is included in the chain ending at block `B`. -/
  mem : Tx → Block → Prop
  /-- Membership is monotone along the prefix order: a transaction in a chain
  stays in every extension. -/
  mem_mono : ∀ {tx : Tx} {B B' : Block}, mem tx B → B ≤ B' → mem tx B'
  /-- `received tx t`: `tx` was delivered to every honest validator by the start
  of slot `t`. -/
  received : Tx → Slot → Prop
  /-- **Honest proposers include pending transactions**: the honest proposer of
  a pivot slot `s ≥ t` includes every transaction received by slot `t` in its
  proposal. -/
  pivot_includes :
    ∀ {tx : Tx} {t s : Slot}, received tx t → E.pivot s → t ≤ s →
      mem tx (E.proposal s)

/-- **Liveness** (Definition 4) with confirmation time `Tconf` (in slots). A
transaction received by slot `t` is in the confirmed chain of every honest
active validator at the checkpoints of every slot `s ≥ t + Tconf`. -/
def TxModel.Live {E : Execution Block Validator View} {κ : ℕ}
    (TX : TxModel E) (L : Ledger E κ) (Tconf : ℕ) : Prop :=
  ∀ {tx : TX.Tx} {t : Slot}, TX.received tx t →
    ∀ {s : Slot} {v : Validator}, t + Tconf ≤ s → E.active v (E.voteRound s) →
      TX.mem tx (L.chain v (E.voteRound s))

end RLMDGhost
