import RLMDGhost.Axioms
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Phase 2 — the probabilistic core of Lemma 2 (issue #21)

`RLMDGhost.Axioms.lemma2` declares the pivot-slot good event `PivotEveryWindow`
as a Barrier-1 axiom: it holds *with overwhelming probability* (w.o.p.). This
file discharges the analytic heart of that "w.o.p." — the fact that the
union-bound failure probability of the proposer lottery is **negligible** in the
security parameter `κ`.

## What the paper's proof produces

For a fixed window length `κ`, honesty ratio `h₀/n` and time horizon `Thor`:

* the proposer of each slot is honest-and-active independently with probability
  `≥ p := h₀/n > 0`, so a fixed length-`κ` window contains no pivot with
  probability `≤ (1 − p)^κ`;
* a union bound over the `Thor = poly(κ)` windows bounds the failure probability
  of `PivotEveryWindow` by `Thor · (1 − p)^κ`.

The remaining step — that `Thor · (1 − p)^κ` with `Thor` polynomial and
`0 ≤ 1 − p < 1` is negligible — is the *content* of "with overwhelming
probability" under `RLMDGhost.Negligible`, and is what this file proves in full
(no `sorry`, Lean core axioms only). The measure-theoretic construction of the
probability space that yields the union bound (product Bernoulli measure,
independence of the per-slot lottery) is threaded here as the standard bound
`failProb κ ≤ horizon κ * (1 - p) ^ κ`, matching the project's
hypothesis-threading discipline for probabilistic facts.

## Main results

* `tendsto_poly_mul_geometric` — `κ ^ d * q ^ κ → 0` for `0 ≤ q < 1`.
* `negligible_geometric` — `fun κ => q ^ κ` is negligible for `0 ≤ q < 1`.
* `Negligible.of_abs_le` — comparison: a sequence dominated by a negligible one
  is negligible.
* `negligible_poly_mul_geometric` — `fun κ => κ ^ d * q ^ κ` is negligible: the
  union-bound shape with a polynomial horizon.
* `lemma2_failure_negligible` — the `PivotEveryWindow` failure probability, under
  the standard union bound, is negligible in `κ`; equivalently the good event
  holds w.o.p.
-/

namespace RLMDGhost

open Filter Asymptotics
open scoped Topology

/-- **Polynomial times geometric tends to zero.** For `0 ≤ q < 1` and any degree
`d`, `κ ↦ κ ^ d * q ^ κ → 0`: geometric decay dominates polynomial growth. -/
theorem tendsto_poly_mul_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ d * q ^ n) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hq0 with hq0' | hq0'
  · -- `q = 0`: eventually the constant `0`.
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← hq0', zero_pow hn.ne', mul_zero]
  · -- `0 < q < 1`: rewrite as `κ^d / (1/q)^κ` and use `κ^d =o (1/q)^κ`.
    have hr : (1 : ℝ) < 1 / q := by rw [lt_div_iff₀ hq0']; simpa using hq1
    have hlittle : (fun n : ℕ => (n : ℝ) ^ d) =o[atTop] (fun n : ℕ => (1 / q) ^ n) :=
      isLittleO_pow_const_const_pow_of_one_lt d hr
    refine (tendsto_congr fun n => ?_).mp hlittle.tendsto_div_nhds_zero
    rw [one_div, inv_pow, div_eq_mul_inv, inv_inv]

/-- **Geometric decay is negligible.** For `0 ≤ q < 1`, the sequence `κ ↦ q ^ κ`
decays faster than every inverse polynomial: `Negligible (fun κ => q ^ κ)`.

This is the analytic kernel of "with overwhelming probability": the per-window
failure factor `(1 − p) ^ κ` of the proposer lottery beats any polynomial time
horizon. -/
theorem negligible_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Negligible (fun κ => q ^ κ) := by
  intro c
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * q ^ n < 1 :=
    (tendsto_poly_mul_geometric hq0 hq1 c).eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨max N 1, fun n hn => ?_⟩
  obtain ⟨hlt, hn1⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hnpos : (0 : ℝ) < (n : ℝ) ^ c := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    positivity
  rw [abs_of_nonneg (pow_nonneg hq0 n), lt_div_iff₀ hnpos, mul_comm]
  exact hlt

/-- **Comparison.** If `|f n| ≤ |g n|` eventually and `g` is negligible, then `f`
is negligible. Passes from the exact union-bound expression to a clean dominating
shape. -/
theorem Negligible.of_abs_le {f g : ℕ → ℝ} (hg : Negligible g)
    (hle : ∀ᶠ n in atTop, |f n| ≤ |g n|) : Negligible f := by
  intro c
  obtain ⟨Ng, hNg⟩ := hg c
  obtain ⟨Nle, hNle⟩ := hle.exists_forall_of_atTop
  refine ⟨max Ng Nle, fun n hn => ?_⟩
  exact lt_of_le_of_lt (hNle n (le_trans (le_max_right _ _) hn))
    (hNg n (le_trans (le_max_left _ _) hn))

/-- **Polynomial × geometric is negligible.** The union-bound failure shape
`κ ↦ κ ^ d * q ^ κ` (a `poly(κ)` horizon times the per-window factor) is
negligible for `0 ≤ q < 1`. -/
theorem negligible_poly_mul_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (d : ℕ) : Negligible (fun κ => (κ : ℝ) ^ d * q ^ κ) := by
  -- Pick `q < s < 1`; then eventually `κ^d q^κ ≤ s^κ`, and `s^κ` is negligible.
  obtain ⟨s, hqs, hs1⟩ := exists_between hq1
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt hq0 hqs
  refine (negligible_geometric hs0.le hs1).of_abs_le ?_
  -- `κ^d (q/s)^κ → 0`, so eventually `≤ 1`, giving `κ^d q^κ ≤ s^κ`.
  have hqs1 : q / s < 1 := (div_lt_one hs0).mpr hqs
  have hqs0 : (0 : ℝ) ≤ q / s := div_nonneg hq0 hs0.le
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d * (q / s) ^ n ≤ 1 :=
    ((tendsto_poly_mul_geometric hqs0 hqs1 d).eventually_le_const (by norm_num))
  filter_upwards [hev] with n hn
  have hspos : (0 : ℝ) < s ^ n := pow_pos hs0 n
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg hs0.le n)]
  -- from `n^d (q/s)^n ≤ 1`, multiply by `s^n > 0`.
  rw [div_pow] at hn
  have : (n : ℝ) ^ d * q ^ n ≤ s ^ n := by
    have h2 := mul_le_mul_of_nonneg_right hn hspos.le
    rwa [one_mul, mul_assoc, div_mul_cancel₀ _ hspos.ne'] at h2
  exact this

/-- **Constant multiple.** A constant times a negligible sequence is negligible:
for large `n` the constant `|C|` is dominated by one factor of `n`, absorbed into
the extra polynomial slack of `g`. -/
theorem Negligible.const_mul {g : ℕ → ℝ} (hg : Negligible g) (C : ℝ) :
    Negligible (fun n => C * g n) := by
  intro c
  obtain ⟨Ng, hNg⟩ := hg (c + 1)
  refine ⟨max Ng (Nat.ceil |C| + 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) (le_trans (le_max_right _ _) hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hCn : |C| ≤ (n : ℝ) := by
    have : (Nat.ceil |C| : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hn)
    exact le_trans (Nat.le_ceil _) this
  have hgn := hNg n (le_trans (le_max_left _ _) hn)
  -- `|C * g n| = |C| * |g n| ≤ n * |g n| < n / n^(c+1) = 1/n^c`.
  rw [abs_mul]
  have hstep1 : |C| * |g n| ≤ (n : ℝ) * |g n| :=
    mul_le_mul_of_nonneg_right hCn (abs_nonneg _)
  have hstep2 : (n : ℝ) * |g n| < (n : ℝ) * (1 / (n : ℝ) ^ (c + 1)) :=
    mul_lt_mul_of_pos_left hgn hnpos
  refine lt_of_le_of_lt hstep1 (lt_of_lt_of_le hstep2 (le_of_eq ?_))
  rw [mul_one_div, pow_succ, mul_comm ((n : ℝ) ^ c) n, div_mul_eq_div_div, div_self hnpos.ne']

/-! ## The Lemma 2 failure probability is negligible

We package the paper's union bound as the hypothesis
`hbound : ∀ κ, |failProb κ| ≤ horizon κ * q ^ κ` where `horizon` is dominated by
a polynomial and `q = 1 - p ∈ [0, 1)`. Under it, `failProb` is negligible — i.e.
`PivotEveryWindow` holds with overwhelming probability. -/

/-- **Lemma 2, probabilistic core.** Let `q = 1 − p ∈ [0, 1)` be the per-window
miss factor of the proposer lottery and `horizon` the number of windows, bounded
by a degree-`d` polynomial `κ ↦ C * κ ^ d`. If the failure probability of
`PivotEveryWindow` obeys the union bound `|failProb κ| ≤ horizon κ * q ^ κ`, then
`failProb` is negligible in `κ`: the good event holds with overwhelming
probability. -/
theorem lemma2_failure_negligible {failProb horizon : ℕ → ℝ} {q C : ℝ} {d : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hhor : ∀ κ, |horizon κ| ≤ C * (κ : ℝ) ^ d)
    (hbound : ∀ κ, |failProb κ| ≤ horizon κ * q ^ κ) :
    Negligible failProb := by
  -- Dominating shape: `C · (κ^d q^κ)`, negligible.
  have hdom : Negligible (fun κ => C * ((κ : ℝ) ^ d * q ^ κ)) :=
    (negligible_poly_mul_geometric hq0 hq1 d).const_mul C
  refine hdom.of_abs_le (Filter.Eventually.of_forall fun κ => ?_)
  have hqκ : (0 : ℝ) ≤ q ^ κ := pow_nonneg hq0 κ
  -- `|failProb κ| ≤ horizon κ q^κ ≤ |horizon κ| q^κ ≤ C κ^d q^κ = |dom κ|`.
  have h1 : horizon κ * q ^ κ ≤ |horizon κ| * q ^ κ :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hqκ
  have h2 : |horizon κ| * q ^ κ ≤ (C * (κ : ℝ) ^ d) * q ^ κ :=
    mul_le_mul_of_nonneg_right (hhor κ) hqκ
  have hdomnn : (0 : ℝ) ≤ C * ((κ : ℝ) ^ d * q ^ κ) := by positivity
  rw [abs_of_nonneg hdomnn, ← mul_assoc]
  exact le_trans (hbound κ) (le_trans h1 h2)

/-- **Lemma 2, w.o.p. conclusion in protocol terms.** Let `p = h₀/n ∈ (0, 1]` be
the (lower bound on the) probability that a slot's proposer is honest and active,
so a fixed length-`κ` window misses a pivot with probability `≤ (1 − p)^κ`, and
let the number of windows in the time horizon be bounded by the degree-`d`
polynomial `κ ↦ C · κ^d`. Then the union-bound failure probability of
`PivotEveryWindow` is negligible in `κ`:

`PivotEveryWindow` holds *with overwhelming probability* — which is exactly the
content of the `RLMDGhost.Axioms.lemma2` axiom this Phase-2 development justifies.
The measure-theoretic construction of the underlying probability space is threaded
as the union bound `hbound`. -/
theorem pivotEveryWindow_failure_negligible {failProb horizon : ℕ → ℝ}
    {p C : ℝ} {d : ℕ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C)
    (hhor : ∀ κ, |horizon κ| ≤ C * (κ : ℝ) ^ d)
    (hbound : ∀ κ, |failProb κ| ≤ horizon κ * (1 - p) ^ κ) :
    Negligible failProb :=
  lemma2_failure_negligible (by linarith) (by linarith) hC hhor hbound

end RLMDGhost
