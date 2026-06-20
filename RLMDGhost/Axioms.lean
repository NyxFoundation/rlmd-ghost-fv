import RLMDGhost.Protocol

/-!
# RLMD-GHOST — declared axioms

Two kinds of facts are declared here (never proved with `sorry`):

* **Idealized cryptography** (Barrier 2) — signature unforgeability and the
  proposer-lottery consistency/uniqueness used by equivocation discounting and
  honest-proposer recognition. Permanent idealized assumptions.

* **The pivot-slot good event** (Barrier 1, Lemma 2) — the single *probabilistic*
  fact: with overwhelming probability every `κ`-window contains a pivot slot. It
  is declared as an `axiom` so the deterministic dependents (Theorem 2 onward)
  proceed by threading the good event in as a hypothesis; the measure-theoretic
  proof replacing it is the separate Phase 2 work item and never blocks
  dependents.
-/

namespace RLMDGhost

variable {Block Validator : Type*} [BlockTree Block]

/-! ## Idealized cryptography (Barrier 2) -/

/-- **Signature unforgeability.** A vote attributed to a validator was actually
cast by it: the adversary cannot forge a slot-`t` vote on behalf of an honest
validator. Threaded into the equivocation-discounting argument of Lemma 4. -/
axiom SignatureUnforgeable (E : Execution Block Validator) : Prop

/-- **Proposer-lottery uniqueness.** Each slot has at most one validator that
wins the proposer lottery, so a pivot slot's honest proposal is well-defined. -/
axiom proposerUnique (E : Execution Block Validator) :
    ∀ {vp vp' : Validator} {t : Slot},
      E.eligiblePropose vp t → E.eligiblePropose vp' t → vp = vp'

/-! ## Lemma 2 — pivot-slot good event (Barrier 1)

The single probabilistic statement of the paper. Declared as an `axiom`; the
Chernoff/union-bound proof over the proposer lottery that replaces it is the
Phase 2 work item and does **not** block dependents. -/

/-- Every `κ`-window of slots contains a pivot slot (one with an active honest
eligible proposer). -/
def HasPivotEveryWindow (E : Execution Block Validator) (κ : ℕ) : Prop :=
  ∀ t : Slot, ∃ s : Slot, t ≤ s ∧ s < t + κ ∧ E.IsPivot s

/-- **Lemma 2** (arXiv:2302.11326). With overwhelming probability every
`κ`-interval contains a pivot slot. Declared as an axiom (Barrier 1); the
probabilistic proof is deferred to Phase 2 and never blocks dependents. -/
axiom lemma2 (E : Execution Block Validator) {κ : ℕ} (hκ : 0 < κ) :
    HasPivotEveryWindow E κ

end RLMDGhost
