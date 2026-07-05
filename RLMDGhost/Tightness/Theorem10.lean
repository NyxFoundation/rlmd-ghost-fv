import RLMDGhost.Tightness.Theorem9Close

/-!
# Theorem 10 — RLMD-GHOST is not `τ`-dynamically-available for any `1 ≤ τ < η`

Where Theorem 9 shows RLMD-GHOST is not `τ`-reorg-resilient for `τ < η`, this is
the *dynamic-availability* consequence: the honest chain is reorged, so no
confirmation rule keeps the execution both safe and live.

The witnessing execution is the Theorem 9 one (`E9`): a genuine RLMD-GHOST run
(`Spec` + `RLMDGhostModel`) that is `τ`-compliant for `τ < η`, in which the
honest proposal `bC` of the pivot slot 2 is canonical throughout `[2, η]` yet
reorged to the conflicting `bB` at slot `η + 1`. Any `κ`-deep confirmation with
`κ ≤ η − 2` confirms `bC` before it is reorged, and the conflicting `bB` is
confirmed afterwards — a safety violation; conversely if nothing is confirmed the
execution is not live. The paper's `k`-fold repetition of this reorg extends the
argument to every confirmation time `Tconf < ⌊(n−5)/4⌋·η`; the single reorg
already refutes dynamic availability for the small-`Tconf` regime, and is the
mechanism the `k`-fold iterates.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-- **Theorem 10.** For every `η ≥ 2` and `1 ≤ τ < η`, there is a `τ`-compliant
genuine RLMD-GHOST execution whose honest pivot proposal `bC` is canonical at the
pivot slot 2 but is *reorged* — a conflicting `bB` is canonical — by slot `η + 1`.
Hence RLMD-GHOST is not `τ`-dynamically-available: the reorged honest chain
cannot be both safely confirmed and live. -/
theorem theorem10 {η : ℕ} (hη : 2 ≤ η) {τ : ℕ} (hτ1 : 1 ≤ τ) (hτ : τ < η) :
    ∃ (E : Execution Blk V9 (Vw V9)) (SM : SleepyModel E),
      Spec E ∧ Nonempty (RLMDGhostModel E SM η) ∧ SM.EtaSleepy τ ∧
        E.pivot 2 ∧
        (∀ v : V9, E.active v (E.voteRound 2) →
          E.chAt v (E.voteRound 2) = E.proposal 2) ∧
        (∃ v : V9, E.active v (E.voteRound (η + 1)) ∧
          ¬ E.proposal 2 ≤ E.chAt v (E.voteRound (η + 1))) := by
  refine ⟨E9 η, SM9 η, E9_spec hη, ⟨E9_model hη⟩, SM9_EtaSleepy hη hτ1 hτ, rfl, ?_, ?_⟩
  · -- `bC` canonical at the pivot slot 2
    intro v _
    rw [E9_chAt_slot η v (Or.inr rfl), effV_ge2 (le_refl 2), fcV_pivotF hη]
    show bC = (if (2 : Slot) = 2 then bC else gen)
    rw [if_pos rfl]
  · -- reorged to `bB` at slot `η + 1`
    refine ⟨0, trivial, ?_⟩
    have hprop : (E9 η).proposal 2 = bC := by
      show (if (2 : Slot) = 2 then bC else gen) = bC; rfl
    rw [hprop, E9_chAt_slot η 0 (Or.inr rfl)]
    have hview : effV η 0 (η + 1) = viewF η := by
      unfold effV
      rw [if_neg (Nat.succ_ne_zero η), if_neg (by omega : ¬ η + 1 = 1)]
    rw [hview, fcV_reorgF hη]
    decide

end Tightness

end RLMDGhost
