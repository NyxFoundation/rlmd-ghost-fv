import RLMDGhost.Axioms
import RLMDGhost.Ledger

/-!
# Theorem 2 — dynamic availability: reorg resilience ⇒ security with `Tconf = 2κ`

> **Theorem 2** (Dynamic-availability, arXiv:2302.11326). An execution of a
> propose-vote-merge protocol satisfying reorg resilience also satisfies
> security with overwhelming probability with `Tconf = 2κ` slots. In
> particular, `τ`-reorg-resilience implies `τ`-dynamic-availability.

The single probabilistic ingredient — "w.o.p. there exists a pivot slot in
every `κ`-window" (Lemma 2) — is threaded as the hypothesis
`PivotEveryWindow E κ`; given it, both halves are deterministic, following the
paper's proof:

* **Liveness** (`Tconf = 2κ`): a transaction received by slot `t` is included by
  the honest proposer of a pivot slot `t'' ∈ [t, t + κ)`; by reorg resilience
  its proposal `B` is canonical at every slot `s ≥ t + 2κ`, where it is
  `κ`-deep (`t'' + κ < t + 2κ ≤ s`), hence confirmed.
* **Safety**: for checkpoints `s ≤ s'`, pick a pivot slot
  `t' ∈ [s + 1 − κ, s + 1)`. By reorg resilience its proposal `B` is canonical
  for both validators. Being from a slot `≥ s + 1 − κ`, `B` is at or beyond the
  truncation point, so `Ch_v ⪯ B`; and `B` and `Ch_{v'}` are both prefixes of
  `v'`'s canonical chain, so either `B ⪯ Ch_{v'}` (then
  `Ch_v ⪯ B ⪯ Ch_{v'}`) or `Ch_{v'} ⪯ B` (then both are prefixes of `B`) —
  either way the two confirmed chains are consistent. In the first `κ` slots
  the confirmed chain is still genesis and consistency is trivial.

Together with Theorem 1 this gives the "in particular": if Proposition 1 holds
in the `τ`-sleepy model then the protocol is `τ`-dynamically-available.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  {E : Execution Block Validator View} {κ : ℕ}

/-- The slot arithmetic of the safety window: a pivot slot in the length-`κ`
window starting at `s + 1 - κ` lies at or before `s` and within `κ` slots of
`s`. Stated over plain `ℕ` so that `omega` sees through the `Slot` abbrev. -/
private theorem safety_window_arith {s t' κ : ℕ} (hsκ : κ ≤ s)
    (hlo : s + 1 - κ ≤ t') (hhi : t' < s + 1 - κ + κ) : t' ≤ s ∧ s ≤ t' + κ := by
  omega

/-- The slot arithmetic of the liveness window: a pivot slot in the length-`κ`
window starting at `t` is `κ`-deep by every slot `s ≥ t + 2κ`. -/
private theorem liveness_window_arith {t t'' s κ : ℕ} (hhi : t'' < t + κ)
    (hs : t + 2 * κ ≤ s) : t'' ≤ s ∧ t'' + κ ≤ s := by
  omega

/-- The safety half for an ordered pair of checkpoints `s ≤ s'`. -/
private theorem safe_of_le (L : Ledger E κ)
    (hwin : PivotEveryWindow E κ) (hRR : ReorgResilient E)
    {s s' : Slot} {v v' : Validator} (hss : s ≤ s')
    (hv : E.active v (E.voteRound s)) (hv' : E.active v' (E.voteRound s')) :
    BlockTree.Consistent (L.chain v (E.voteRound s)) (L.chain v' (E.voteRound s')) := by
  rcases Nat.lt_or_ge s κ with hsκ | hsκ
  · rw [L.chain_genesis_early hsκ hv]
    exact BlockTree.consistent_genesis _
  · obtain ⟨t', ht'lo, ht'hi, hpiv⟩ := hwin (s + 1 - κ)
    obtain ⟨ht's, hrecent⟩ := safety_window_arith hsκ ht'lo ht'hi
    have hB : E.proposal t' ≤ E.chAt v (E.voteRound s) :=
      (hRR t' hpiv).1 s ht's v hv
    have hB' : E.proposal t' ≤ E.chAt v' (E.voteRound s') :=
      (hRR t' hpiv).1 s' (ht's.trans hss) v' hv'
    have hCh : L.chain v (E.voteRound s) ≤ E.proposal t' :=
      L.chain_le_of_recent hv hrecent hB
    rcases BlockTree.consistent_of_le_of_le hB' (L.chain_le_chAt hv') with hle | hge
    · exact Or.inl (hCh.trans hle)
    · exact BlockTree.consistent_of_le_of_le hCh hge

/-- **Theorem 2 (Dynamic-availability).** For every confirmed-ledger assignment
at depth `κ` with a transaction model, an execution satisfying reorg resilience
is secure with confirmation time `Tconf = 2κ` slots, given the pivot-slot good
event of Lemma 2. -/
theorem theorem2 (L : Ledger E κ) (TX : TxModel E)
    (hwin : PivotEveryWindow E κ) (hRR : ReorgResilient E) :
    L.Safe ∧ TX.Live L (2 * κ) := by
  constructor
  · intro s s' v v' hv hv'
    rcases le_total s s' with hss | hss
    · exact safe_of_le L hwin hRR hss hv hv'
    · exact (safe_of_le L hwin hRR hss hv' hv).symm
  · intro tx t hrecv s v hs hv
    obtain ⟨t'', ht''lo, ht''hi, hpiv⟩ := hwin t
    obtain ⟨ht''s, hdeep⟩ := liveness_window_arith ht''hi hs
    have hmem := TX.pivot_includes hrecv hpiv ht''lo
    have hcanon : E.proposal t'' ≤ E.chAt v (E.voteRound s) :=
      (hRR t'' hpiv).1 s ht''s v hv
    exact TX.mem_mono hmem (L.le_chain_of_deep hv hdeep hcanon)

end RLMDGhost
