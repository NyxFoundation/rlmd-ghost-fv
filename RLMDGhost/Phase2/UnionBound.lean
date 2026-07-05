import RLMDGhost.Phase2.Lemma2
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.Basic

/-!
# Phase 2 — the measure-theoretic union bound for Lemma 2 (issue #21)

`RLMDGhost.Phase2.Lemma2` reduces Lemma 2's "with overwhelming probability" to the
union bound `|failProb κ| ≤ horizon κ * (1 − p)^κ`, which it threads as a
hypothesis. This file **discharges that hypothesis** by constructing the
underlying probability space and proving the union bound from independence — the
part deferred by the strategy doc as "measure-theoretic".

## The probability space

The proposer lottery of a horizon of `T` slots is the product-Bernoulli measure
`lot T p hp := Measure.pi (fun _ : Fin T => (PMF.bernoulli p hp).toMeasure)`
on `Fin T → Bool`, where coordinate `t` records whether slot `t`'s proposer is
honest-and-active (probability `≥ p`). The coordinates are independent
(`iIndepFun_pi`).

## What is proved (`sorry`-free, Lean core axioms only)

* `lot_miss` — a single slot misses (`ω t = false`) with probability `1 − p`.
* `lot_window` — a window `w` misses on *every* slot with probability
  `(1 − p) ^ w.card`, via coordinate independence.
* `lot_union_bound` — over a family `W` of length-`κ` windows, the failure event
  `⋃ w ∈ W, (w all-miss)` has measure `≤ (#W) · (1 − p)^κ` (union bound).
* `pivotEveryWindow_fail_negligible` — the capstone: with `p ∈ (0, 1]` and a
  polynomially-bounded number of windows, the real-valued failure probability is
  **negligible** in `κ`. This is Lemma 2's "w.o.p." fully realized: the union
  bound is no longer a hypothesis but a theorem about the product-Bernoulli space,
  fed into the negligibility core of `RLMDGhost.Phase2.Lemma2`.
-/

namespace RLMDGhost

open MeasureTheory ProbabilityTheory PMF Function
open scoped ENNReal NNReal

/-- **The proposer lottery.** The product-Bernoulli measure over a horizon of `T`
slots: each coordinate is an independent `Bernoulli p` draw recording whether the
slot's proposer is honest-and-active. -/
noncomputable def lot (T : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Fin T → Bool) :=
  Measure.pi (fun _ => (PMF.bernoulli p hp).toMeasure)

instance lot_isProb (T : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : IsProbabilityMeasure (lot T p hp) := by
  unfold lot; infer_instance

/-- A single slot's proposer is *not* honest-and-active with probability `1 − p`. -/
theorem lot_miss (T : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (t : Fin T) :
    lot T p hp (eval t ⁻¹' {false}) = ((1 : ℝ≥0∞) - p) := by
  unfold lot
  rw [(measurePreserving_eval (fun _ => (PMF.bernoulli p hp).toMeasure) t).measure_preimage
    ((measurableSet_singleton _).nullMeasurableSet)]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.bernoulli_apply]

/-- The per-slot lottery draws are independent. -/
theorem lot_indep (T : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun (fun (i : Fin T) (ω : Fin T → Bool) => ω i) (lot T p hp) := by
  unfold lot
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- **A whole window misses with probability `(1 − p)^κ`.** By independence of the
per-slot draws, the event that *every* slot of `w` misses has probability
`∏_{i ∈ w} (1 − p) = (1 − p) ^ w.card`. -/
theorem lot_window (T : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (w : Finset (Fin T)) :
    lot T p hp (⋂ i ∈ w, eval i ⁻¹' {false}) = ((1 : ℝ≥0∞) - p) ^ w.card := by
  set s : Fin T → Set (Fin T → Bool) :=
    fun i => if i ∈ w then eval i ⁻¹' {false} else Set.univ with hs_def
  have hinter : (⋂ i, s i) = ⋂ i ∈ w, eval i ⁻¹' {false} := by
    ext ω; simp only [hs_def, Set.mem_iInter]; constructor
    · intro h i hi; have := h i; rw [if_pos hi] at this; exact this
    · intro h i; by_cases hi : i ∈ w
      · rw [if_pos hi]; exact h i hi
      · rw [if_neg hi]; trivial
  rw [← hinter]
  have hmeas : ∀ i, MeasurableSet[(inferInstance : MeasurableSpace Bool).comap (eval i)] (s i) := by
    intro i; simp only [hs_def]; by_cases hi : i ∈ w
    · rw [if_pos hi]; exact ⟨{false}, measurableSet_singleton _, rfl⟩
    · rw [if_neg hi]; exact ⟨Set.univ, MeasurableSet.univ, by simp⟩
  rw [(lot_indep T p hp).meas_iInter hmeas]
  have hval : ∀ i, lot T p hp (s i) = if i ∈ w then ((1 : ℝ≥0∞) - p) else 1 := by
    intro i; simp only [hs_def]; by_cases hi : i ∈ w
    · rw [if_pos hi, if_pos hi]; exact lot_miss T p hp i
    · rw [if_neg hi, if_neg hi]; exact measure_univ
  simp_rw [hval]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **The union bound.** Over a family `W` of length-`κ` windows, the probability
that *some* window misses entirely is at most `(#W) · (1 − p)^κ`. -/
theorem lot_union_bound (T : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (W : Finset (Finset (Fin T)))
    (κ : ℕ) (hκ : ∀ w ∈ W, w.card = κ) :
    lot T p hp (⋃ w ∈ W, ⋂ i ∈ w, eval i ⁻¹' {false}) ≤ (W.card : ℝ≥0∞) * ((1 - p) ^ κ) := by
  refine le_trans (measure_biUnion_finset_le W _) ?_
  have hcongr : ∀ w ∈ W, lot T p hp (⋂ i ∈ w, eval i ⁻¹' {false}) = ((1 : ℝ≥0∞) - p) ^ κ := by
    intro w hw; rw [lot_window T p hp w, hκ w hw]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]

/-- **Lemma 2, fully realized (w.o.p.).** Let the honest-proposer probability be
`p ∈ (0, 1]` and let the number of length-`κ` windows in the time horizon be
polynomially bounded (`#(W κ) ≤ C · κ^d`). Then the real-valued failure
probability of the pivot-slot good event — the measure, under the product-Bernoulli
proposer lottery, of "some length-`κ` window misses entirely" — is **negligible**
in `κ`.

This closes the loop of `RLMDGhost.Axioms.lemma2`: the union bound is now proved
from the probability space (`lot_union_bound`) rather than assumed, and combined
with the negligibility core (`pivotEveryWindow_failure_negligible`) it yields that
`PivotEveryWindow` holds with overwhelming probability. -/
theorem pivotEveryWindow_fail_negligible {T : ℕ → ℕ} {p : ℝ≥0} {C : ℝ} {d : ℕ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C)
    (W : ∀ κ, Finset (Finset (Fin (T κ))))
    (hcard : ∀ κ, ∀ w ∈ W κ, w.card = κ)
    (hhor : ∀ κ, ((W κ).card : ℝ) ≤ C * (κ : ℝ) ^ d) :
    Negligible (fun κ =>
      (lot (T κ) p hp1 (⋃ w ∈ W κ, ⋂ i ∈ w, eval i ⁻¹' {false})).toReal) := by
  have hp1' : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  refine pivotEveryWindow_failure_negligible (p := (p : ℝ)) (d := d) (by exact_mod_cast hp0) hp1' hC
    (horizon := fun κ => ((W κ).card : ℝ)) (fun κ => ?_) (fun κ => ?_)
  · rw [abs_of_nonneg (by positivity)]; exact hhor κ
  · rw [abs_of_nonneg ENNReal.toReal_nonneg]
    have hb := lot_union_bound (T κ) p hp1 (W κ) κ (hcard κ)
    have hfin : (((W κ).card : ℝ≥0∞) * ((1 : ℝ≥0∞) - p) ^ κ) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.pow_ne_top (by exact (tsub_le_self).trans_lt ENNReal.one_lt_top |>.ne))
    refine le_trans (ENNReal.toReal_mono hfin hb) (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    have hsub : ((1 : ℝ≥0∞) - (p : ℝ≥0∞)).toReal = 1 - (p : ℝ) := by
      rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp1) ENNReal.one_ne_top,
        ENNReal.toReal_one, ENNReal.coe_toReal]
    rw [hsub]

end RLMDGhost
