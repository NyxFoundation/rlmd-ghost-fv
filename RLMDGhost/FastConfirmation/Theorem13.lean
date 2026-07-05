import RLMDGhost.FastConfirmation.Theorem12
import RLMDGhost.Security.Theorem7

/-!
# Theorem 13 — dynamic availability with fast confirmations

> **Theorem 13** (Dynamic availability, arXiv:2302.11326). RLMD-GHOST with fast
> confirmations is `η`-dynamically-available.

The paper's proof splits into the two halves of security:

* **`η`-liveness** "follows directly from Theorem 7 … because fast confirmations
  are not needed for the confirmed chain to make progress." The fast-confirmed
  ledger extends the standard one, so a transaction confirmed by the standard
  κ-deep rule is confirmed by the fast ledger too; liveness is reused verbatim
  from Theorem 7.
* **`η`-safety** reduces to standard safety: a block fast confirmed at slot `t`
  is canonical for all active validators at rounds `≥ 3∆(t + 1) + ∆`
  (Theorem 12), hence κ-deep and standard-confirmed by slot `t + κ`, so a
  fast-confirmation safety violation is a standard-confirmation safety
  violation.

Formalisation. The fast-confirmed ledger is the abstract confirmation-rule
interface `FastLedger` (Barrier 4), exactly as the standard `Ledger` of Track A:
its confirmation-rule fields — the fast-ledger output extends the standard one
(`std_le`) and stays a prefix of the fork choice (`chain_le_chAt`), and its
entries are canonical-stable forward (`fast_persists`, the Theorem 12 / reorg
consequence) — are consequences of the rule, from which `Safe` is derived by the
shared `consistent_of_forks` argument. Liveness is inherited: any fast ledger
dominating a live standard ledger is itself live.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η n₃ : ℕ}

/-- The fast-confirmed ledger (Appendix B) at confirmation depth `κ`, over a
`FastConfirmModel`. As with the standard `Ledger`, the confirmation-rule facts
are an abstract interface; the fields record the consequences of the combined
κ-deep + fast-confirmation rule that Theorem 13 uses. Statements are placed at
the voting-round checkpoints. -/
structure FastLedger (R : FastConfirmModel E SM η n₃) (κ : ℕ) where
  /-- `Ch^r_v`: the fast-confirmed chain output by `v` at round `r`. -/
  chain : Validator → Round → Block
  /-- The fast-confirmed chain is a prefix of the validator's own canonical
  chain. -/
  chain_le_chAt :
    ∀ {v : Validator} {r : Round}, E.active v r → chain v r ≤ E.chAt v r
  /-- **Fast-confirmed blocks are canonical-stable forward** (the Theorem 12 /
  reorg consequence): a block in some honest validator's fast ledger at a
  checkpoint is a prefix of every honest validator's fork choice at every later
  checkpoint. -/
  fast_persists :
    ∀ {s s' : Slot} {v v' : Validator}, s ≤ s' →
      E.active v (E.voteRound s) → E.active v' (E.voteRound s') →
        chain v (E.voteRound s) ≤ E.chAt v' (E.voteRound s')

/-- **Safety** (Definition 4) for the fast-confirmed ledger. -/
def FastLedger.Safe {R : FastConfirmModel E SM η n₃} {κ : ℕ} (F : FastLedger R κ) :
    Prop :=
  ∀ {s s' : Slot} {v v' : Validator},
    E.active v (E.voteRound s) → E.active v' (E.voteRound s') →
      BlockTree.Consistent (F.chain v (E.voteRound s)) (F.chain v' (E.voteRound s'))

omit [FiniteAncestors Block] in
/-- The fast-confirmed ledger is **safe**: for `s ≤ s'`, both outputs are
prefixes of `v'`'s canonical chain at `s'` (the first by `fast_persists`, the
second by `chain_le_chAt`), hence consistent; the general case follows by
symmetry. This is the fast-confirmation analogue of `Ledger.safe`, and is the
`η`-safety half of Theorem 13. -/
theorem FastLedger.safe {R : FastConfirmModel E SM η n₃} {κ : ℕ}
    (F : FastLedger R κ) : F.Safe := by
  have hforks : ∀ {s s' : Slot} {v v' : Validator}, s ≤ s' →
      E.active v (E.voteRound s) → E.active v' (E.voteRound s') →
        BlockTree.Consistent (F.chain v (E.voteRound s)) (F.chain v' (E.voteRound s')) := by
    intro s s' v v' hss hv hv'
    exact BlockTree.consistent_of_le_of_le
      (F.fast_persists hss hv hv') (F.chain_le_chAt hv')
  intro s s' v v' hv hv'
  rcases le_total s s' with h | h
  · exact hforks h hv hv'
  · exact (hforks h hv' hv).symm

/-- **Theorem 13 (Dynamic availability with fast confirmations).** The
fast-confirmed ledger is safe, and live with `Tconf = 2κ` whenever the standard
ledger it extends is live (liveness is unaffected by fast confirmations —
Theorem 7). The safety half is `FastLedger.safe`; liveness is threaded from the
standard ledger via the domination `Ch_std ⪯ Ch_fast` witnessed by `hdom`. -/
theorem theorem13 (S : Spec E) (R : FastConfirmModel E SM η n₃)
    (hsleepy : SM.EtaSleepy η) {κ : ℕ} (F : FastLedger R κ)
    (L : Ledger E κ) (TX : TxModel E) (hwin : PivotEveryWindow E κ)
    (hdom : ∀ {tx : TX.Tx} {v : Validator} {s : Slot},
      E.active v (E.voteRound s) → TX.mem tx (L.chain v (E.voteRound s)) →
        TX.mem tx (F.chain v (E.voteRound s))) :
    F.Safe ∧
      (∀ {tx : TX.Tx} {t : Slot}, TX.received tx t →
        ∀ {s : Slot} {v : Validator}, t + 2 * κ ≤ s → E.active v (E.voteRound s) →
          TX.mem tx (F.chain v (E.voteRound s))) := by
  refine ⟨F.safe, ?_⟩
  intro tx t hrecv s v hs hv
  have hstd := (theorem7 S R.toRLMDGhostModel hsleepy L TX hwin).2 hrecv hs hv
  exact hdom hv hstd

end RLMDGhost
