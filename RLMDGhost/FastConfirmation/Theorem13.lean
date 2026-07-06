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
  κ-deep rule is confirmed by the combined ledger too; liveness is reused
  verbatim from Theorem 7.
* **`η`-safety** reduces to standard safety: a block fast confirmed at slot `t`
  is canonical for all active validators at rounds `≥ 3∆(t + 1) + ∆`
  (Theorem 12), so a fast entry is consistent with every later canonical chain,
  and a standard entry is consistent with everything a pivot-window argument
  reaches — a fast-confirmation safety violation would be a standard-confirmation
  safety violation.

Formalisation. `FastLedger` is the combined κ-deep + fast confirmation rule as
an abstract interface (Barrier 4) over the standard `Ledger`. Its fields are
*rule mechanics only* — none carries any security content:

* `chain_le_chAt` — the output is a prefix of the validator's own canonical
  chain (as for the standard `Ledger`);
* `chain_cases` — the combined rule outputs either the standard κ-deep entry or
  a block the validator itself fast confirmed at an *earlier* slot. (The fast
  entry is reflected in the output ledger from the next checkpoint on, matching
  the range of Theorem 12's guarantee `≥ 3∆(t + 1) + ∆`; at the confirmation
  slot's own checkpoint the output is the standard one.)
* `std_le_chain` — the combined rule dominates the standard rule (it takes the
  longer of the two candidates).

Unlike the standard `Ledger`, whose safety is `theorem2`, the safety of
`FastLedger` is **proved** here (`FastLedger.safe`) from Theorem 12 (fast
entries stay canonical), Theorem 6 (reorg resilience, via `theorem2`'s
pivot-window argument for standard entries) and standard safety — the paper's
reduction, made explicit by a four-way case analysis on the two entries'
provenance. Liveness is inherited from Theorem 7 through `std_le_chain`.
-/

namespace RLMDGhost

open BlockTree

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View] [DecidableEq Validator]
  {E : Execution Block Validator View} {SM : SleepyModel E} {η n₃ : ℕ}

/-- The combined κ-deep + fast confirmation rule (Appendix B) over the standard
`Ledger` `L`, as an abstract interface. Every field is a mechanic of the rule —
which of the two candidate chains is output — never a security consequence; see
the module docstring. -/
structure FastLedger (R : FastConfirmModel E SM η n₃) {κ : ℕ} (L : Ledger E κ) where
  /-- `Ch^r_v`: the combined confirmed chain output by `v` at round `r`. -/
  chain : Validator → Round → Block
  /-- The output is a prefix of the validator's own canonical chain. -/
  chain_le_chAt :
    ∀ {v : Validator} {r : Round}, E.active v r → chain v r ≤ E.chAt v r
  /-- **Provenance**: the combined output at a checkpoint is the standard κ-deep
  entry, or a block the validator fast confirmed at an earlier slot. -/
  chain_cases :
    ∀ {v : Validator} {s : Slot}, E.active v (E.voteRound s) →
      chain v (E.voteRound s) = L.chain v (E.voteRound s) ∨
      ∃ t B, t < s ∧ R.fastConfirms v t B ∧ chain v (E.voteRound s) = B
  /-- **Domination**: the combined rule extends the standard κ-deep rule. -/
  std_le_chain :
    ∀ {v : Validator} {s : Slot}, E.active v (E.voteRound s) →
      L.chain v (E.voteRound s) ≤ chain v (E.voteRound s)

/-- **Safety** (Definition 4) for the combined ledger. -/
def FastLedger.Safe {R : FastConfirmModel E SM η n₃} {κ : ℕ} {L : Ledger E κ}
    (F : FastLedger R L) : Prop :=
  ∀ {s s' : Slot} {v v' : Validator},
    E.active v (E.voteRound s) → E.active v' (E.voteRound s') →
      BlockTree.Consistent (F.chain v (E.voteRound s)) (F.chain v' (E.voteRound s'))

/-- The safety-window slot arithmetic, over plain `ℕ` so `omega` sees through
the `Slot` abbrev. -/
private theorem fast_window_arith {s t' κ : ℕ} (hsκ : κ ≤ s)
    (hlo : s + 1 - κ ≤ t') (hhi : t' < s + 1 - κ + κ) : t' ≤ s ∧ s ≤ t' + κ := by
  omega

/-- The combined ledger is **safe** — the `η`-safety half of Theorem 13, proved
by the paper's reduction. For checkpoints `s ≤ s'` the two outputs are compared
by provenance (`chain_cases`):

* *(fast, _)*: a fast entry of `v` from slot `t < s ≤ s'` is canonical in `v'`'s
  chain at `s'` by Theorem 12, and the other output is a prefix of that same
  chain (`chain_le_chAt` / Theorem 12 again), so the two are consistent.
* *(std, std)*: standard safety (`theorem2`, threaded as `hstd`).
* *(std, fast)*: `theorem2`'s pivot-window argument — a pivot `t*` in
  `[s + 1 − κ, s + 1)` has `Ch_v ⪯ proposal t*` (`chain_le_of_recent`), and by
  reorg resilience `proposal t*` is canonical at `(v', s')` alongside the fast
  entry `B'` (Theorem 12), so `Ch_v ⪯ proposal t*` and `B'` lie on `v'`'s one
  chain and are consistent. -/
theorem FastLedger.safe {R : FastConfirmModel E SM η n₃} {κ : ℕ} {L : Ledger E κ}
    (F : FastLedger R L) (S : Spec E) (hsleepy : SM.EtaSleepy η)
    (hstd : L.Safe) (hwin : PivotEveryWindow E κ) : F.Safe := by
  have hRR : ReorgResilient E := theorem6 S R.toRLMDGhostModel hsleepy
  -- a fast entry from slot t is canonical for every active validator at
  -- checkpoints of slots > t (Theorem 12)
  have hfast : ∀ {t : Slot} {B : Block} {vc : Validator}, R.fastConfirms vc t B →
      ∀ {w : Validator} {s' : Slot}, t < s' → E.active w (E.voteRound s') →
        B ≤ E.chAt w (E.voteRound s') := by
    intro t B vc hfc w s' hts' hw
    exact (theorem12 S R hsleepy hfc).1 s' hts' w hw
  have hforks : ∀ {s s' : Slot} {v v' : Validator}, s ≤ s' →
      E.active v (E.voteRound s) → E.active v' (E.voteRound s') →
        Consistent (F.chain v (E.voteRound s)) (F.chain v' (E.voteRound s')) := by
    intro s s' v v' hss hv hv'
    rcases F.chain_cases hv with hstdv | ⟨t, B, hts, hfc, hB⟩
    · rcases F.chain_cases hv' with hstdv' | ⟨t', B', ht's', hfc', hB'⟩
      · -- (std, std): standard safety
        rw [hstdv, hstdv']
        exact hstd hv hv'
      · -- (std, fast): the pivot-window reduction
        rw [hstdv, hB']
        rcases Nat.lt_or_ge s κ with hsκ | hsκ
        · rw [L.chain_genesis_early hsκ hv]
          exact consistent_genesis _
        · obtain ⟨tp, hlo, hhi, hpiv⟩ := hwin (s + 1 - κ)
          obtain ⟨htps, hrecent⟩ := fast_window_arith hsκ hlo hhi
          have hpropv : E.proposal tp ≤ E.chAt v (E.voteRound s) :=
            (hRR tp hpiv).1 s htps v hv
          have hCh : L.chain v (E.voteRound s) ≤ E.proposal tp :=
            L.chain_le_of_recent hv hrecent hpropv
          have hpropv' : E.proposal tp ≤ E.chAt v' (E.voteRound s') :=
            (hRR tp hpiv).1 s' (htps.trans hss) v' hv'
          have hB'v' : B' ≤ E.chAt v' (E.voteRound s') := hfast hfc' ht's' hv'
          rcases consistent_of_le_of_le hpropv' hB'v' with hle | hge
          · exact Or.inl (hCh.trans hle)
          · exact consistent_of_le_of_le hCh hge
    · -- (fast, _): Theorem 12 puts the fast entry into v''s chain at s'
      have hBv' : B ≤ E.chAt v' (E.voteRound s') :=
        hfast hfc (lt_of_lt_of_le hts hss) hv'
      rw [hB]
      rcases F.chain_cases hv' with hstdv' | ⟨t', B', ht's', hfc', hB'⟩
      · rw [hstdv']
        exact consistent_of_le_of_le hBv' (L.chain_le_chAt hv')
      · rw [hB']
        exact consistent_of_le_of_le hBv' (hfast hfc' ht's' hv')
  intro s s' v v' hv hv'
  rcases le_total s s' with h | h
  · exact hforks h hv hv'
  · exact (hforks h hv' hv).symm

/-- **Theorem 13 (Dynamic availability with fast confirmations).** In an
`η`-compliant execution, given the pivot-slot good event, the combined
κ-deep + fast confirmation ledger is safe and live with `Tconf = 2κ`: safety by
the reduction of `FastLedger.safe` (Theorem 12 + Theorem 6 + standard safety),
liveness inherited from Theorem 7 through the domination `Ch_std ⪯ Ch_fast`. -/
theorem theorem13 (S : Spec E) (R : FastConfirmModel E SM η n₃)
    (hsleepy : SM.EtaSleepy η) {κ : ℕ} {L : Ledger E κ} (F : FastLedger R L)
    (TX : TxModel E) (hwin : PivotEveryWindow E κ) :
    F.Safe ∧
      (∀ {tx : TX.Tx} {t : Slot}, TX.received tx t →
        ∀ {s : Slot} {v : Validator}, t + 2 * κ ≤ s → E.active v (E.voteRound s) →
          TX.mem tx (F.chain v (E.voteRound s))) := by
  obtain ⟨hsafe, hlive⟩ := theorem7 S R.toRLMDGhostModel hsleepy L TX hwin
  refine ⟨F.safe S hsleepy hsafe hwin, ?_⟩
  intro tx t hrecv s v hs hv
  exact TX.mem_mono (hlive hrecv hs hv) (F.std_le_chain hv)

end RLMDGhost
