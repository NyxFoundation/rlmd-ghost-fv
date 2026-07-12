import RLMDGhost.Tightness.WitnessBase

/-!
# Theorem 4 — LMD-GHOST is not `τ`-dynamically-available for any finite `τ`

LMD-GHOST is RLMD-GHOST with `η = ∞`: votes never expire, so a validator's
*latest* vote counts forever. This lets the adversary keep an old minority vote
alive and, with a single corruption, flip the fork-choice majority and reorg the
honest chain — violating reorg resilience and hence dynamic availability.

**`η = ∞`, exactly.** The fork choice of the witness is `fcV W s s` — the
witness GHOST with the expiry window as wide as the slot index — so at every
slot `s` the counted window is the whole history `[0, s − 1]`. No vote ever
expires at any evaluated round: this is LMD-GHOST itself, not a truncation.

**Per-`τ` witness family** (paper: "we fix a finite `τ ≥ Tconf` … the adversary
… does nothing for `N ≫ τ` slots"). The paper's claim quantifies over every
finite `τ`, and its execution *depends on* `τ`: the adversary waits until the
sleeping voters have left the `τ`-sleepiness window before corrupting. The
witness `E4 τ` reproduces this with `n = 7 = 2·3 + 1` (`m = 3`), the paper's
partition `V1 = {v0}` (adversarial), `V2 = {v1, v2, v3, v4}` (`m + 1` honest),
`V3 = {v5, v6}` (`m − 1` honest):

* at the pivot slot 2 the honest proposal `bA` reaches `V2`, which votes `bA`
  from slot 2 on; the adversary shows `V3` only the conflicting `bB`, `V3`
  votes `bB` at slot 2 and is put to sleep;
* nothing happens for `τ` slots — by slot `τ + 3` the window `[3, τ + 1]` of
  `τ`-sleepiness no longer reaches slot 2, so `V3` stops counting against the
  honest majority, while its `bB` votes still count in the fork choice
  (`η = ∞`);
* at slot `τ + 3` the adversary corrupts `v1` and votes `bB` with both `v0` and
  `v1`: at slot `τ + 4` the counted latest votes are `bB` for `{v0, v1, v5, v6}`
  (weight 4) against `bA` for `{v2, v3, v4}` (weight 3), so `bB` is canonical
  and the honest proposal is reorged.

`τ`-sleepiness holds at *every* slot (`SM4_EtaSleepy`): before the corruption
the four honest `V2` voters outnumber `{v0} ∪ V3`, and from the corruption slot
on the window `[t + 1 − τ, t − 1]` no longer contains slot 2, so only
`{v0, v1}` count against the three remaining honest voters. A reorged honest
proposal cannot be both safely confirmed and live under any confirmation rule,
so — as with Theorem 10 — the property refuted formally is reorg resilience,
the reorg-level rendering of the dynamic-availability failure. -/

namespace RLMDGhost

namespace Tightness

open Blk

/-- The seven validators (`n = 2m + 1`, `m = 3`). `0 = v0` (adversary),
`1 = v1` (corrupted at slot `τ + 3`), `2, 3, 4` (honest `V2` core),
`5, 6` (honest `V3`, asleep after slot 2). -/
abbrev V7 : Type := Fin 7

/-- The LMD vote table of the `τ`-indexed witness: `V3 = {v5, v6}` votes `bB`
at slot 2 and sleeps; the `V2` core `{v2, v3, v4}` votes `bA` from slot 2
through slot `τ + 3`; `v0` and the freshly corrupted `v1` vote `bB` at slot
`τ + 3`. (`v1`'s earlier honest `bA` votes are elided: under the latest-message
rule only its final `bB` vote is ever counted.) -/
def tab4 (τ : ℕ) (u : V7) (u' : ℕ) : Finset Blk :=
  if u' ≤ 1 then {gen}
  else if u.val ≤ 1 then (if u' = τ + 3 then {bB} else ∅)
  else if u.val ≤ 4 then (if u' ≤ τ + 3 then {bA} else ∅)
  else (if u' = 2 then {bB} else ∅)

/-- The common view. -/
def view4 (τ : ℕ) : Vw V7 := (({gen, bA, bB} : Finset Blk), tab4 τ)

theorem view4_fst (τ : ℕ) : (view4 τ).1 = ({gen, bA, bB} : Finset Blk) := rfl
theorem okBlk_bA_view4 (τ : ℕ) : okBlk (view4 τ).1 bA := by rw [view4_fst]; decide
theorem okBlk_bB_view4 (τ : ℕ) : okBlk (view4 τ).1 bB := by rw [view4_fst]; decide

/-! ### Counted votes at the reorg slot `τ + 4` (window `τ + 4` ⊇ the whole
history — no expiry, `η = ∞`) -/

/-- `v0` and `v1` vote `bB` at slot `τ + 3`; their latest vote is `bB`. -/
theorem voteOf4_adv {τ : ℕ} {u : V7} (h : u.val ≤ 1) :
    voteOfV (view4 τ) (τ + 4) (τ + 4) u = some bB := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bB_view4 τ)
  show tab4 τ u (τ + 4 - 1) = {bB}
  rw [show τ + 4 - 1 = τ + 3 from rfl]
  unfold tab4
  rw [if_neg (by omega : ¬ τ + 3 ≤ 1), if_pos h, if_pos rfl]

/-- `v2, v3, v4` vote `bA` through slot `τ + 3`; their latest vote is `bA`. -/
theorem voteOf4_hon {τ : ℕ} {u : V7} (h1 : ¬ u.val ≤ 1) (h4 : u.val ≤ 4) :
    voteOfV (view4 τ) (τ + 4) (τ + 4) u = some bA := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ (okBlk_bA_view4 τ)
  show tab4 τ u (τ + 4 - 1) = {bA}
  rw [show τ + 4 - 1 = τ + 3 from rfl]
  unfold tab4
  rw [if_neg (by omega : ¬ τ + 3 ≤ 1), if_neg h1, if_pos h4,
    if_pos (le_refl (τ + 3))]

/-- `v5, v6`, asleep since slot 2, have their slot-2 `bB` vote still counted:
with the full-history window (`η = ∞`) it never expires, and slot 2 is their
latest voting slot. -/
theorem voteOf4_sleep {τ : ℕ} {u : V7} (h4 : ¬ u.val ≤ 4) :
    voteOfV (view4 τ) (τ + 4) (τ + 4) u = some bB := by
  unfold voteOfV
  have h1 : ¬ u.val ≤ 1 := by omega
  have hT2 : tab4 τ u 2 = {bB} := by
    unfold tab4
    rw [if_neg (by omega : ¬ (2 : ℕ) ≤ 1), if_neg h1, if_neg h4, if_pos rfl]
  have hmax : ∀ u' ∈ cand (tab4 τ u) (τ + 4) (τ + 4), u' ≤ 2 := by
    intro u' hu'
    rw [mem_cand] at hu'
    obtain ⟨hlt, hwin, hne⟩ := hu'
    by_contra hgt
    apply hne
    unfold tab4
    rw [if_neg (by omega : ¬ u' ≤ 1), if_neg h1, if_neg h4,
      if_neg (by omega : ¬ u' = 2)]
  refine voteOf1_eq_some ?_ hmax hT2 (okBlk_bB_view4 τ)
  rw [mem_cand]
  refine ⟨by omega, by omega, ?_⟩
  show tab4 τ u 2 ≠ ∅
  rw [hT2]
  exact Finset.singleton_ne_empty bB

def expected4 (u : V7) : Option Blk :=
  if u.val ≤ 1 then some bB else if u.val ≤ 4 then some bA else some bB

theorem voteOfV_eq_expected4 {τ : ℕ} (u : V7) :
    voteOfV (view4 τ) (τ + 4) (τ + 4) u = expected4 u := by
  unfold expected4
  by_cases h1 : u.val ≤ 1
  · rw [if_pos h1, voteOf4_adv h1]
  · rw [if_neg h1]
    by_cases h4 : u.val ≤ 4
    · rw [if_pos h4, voteOf4_hon h1 h4]
    · rw [if_neg h4, voteOf4_sleep h4]

theorem weight_bA_reorg4 (τ : ℕ) : weight bA (votesV (view4 τ) (τ + 4) (τ + 4)) = 3 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V7 =>
      ∃ b, voteOfV (view4 τ) (τ + 4) (τ + 4) u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V7 => ∃ b, expected4 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected4 u]
  rw [this]; decide

theorem weight_bB_reorg4 (τ : ℕ) : weight bB (votesV (view4 τ) (τ + 4) (τ + 4)) = 4 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V7 =>
      ∃ b, voteOfV (view4 τ) (τ + 4) (τ + 4) u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V7 => ∃ b, expected4 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected4 u]
  rw [this]; decide

/-- **The LMD reorg.** At slot `τ + 4` the fork choice outputs `bB`: the
never-expiring `V3` votes plus the two adversarial votes give `bB` a strict
majority (weight 4) over `bA` (weight 3), reorging the honest chain. -/
theorem fcV_reorg4 (τ : ℕ) : fcV (view4 τ) (τ + 4) (τ + 4) = bB := by
  unfold fcV
  rw [if_neg, if_pos (okBlk_bB_view4 τ)]
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨?_, okBlk_bB_view4 τ⟩
  rw [weight_bA_reorg4 τ, weight_bB_reorg4 τ]
  omega

/-! ## The execution, `τ`-compliance and the theorem -/

private theorem l_d3ma (s : ℕ) : (3 * s + 1) / 3 = s := by omega
private theorem l_d3m (s : ℕ) : (3 * s) / 3 = s := by omega
private theorem l_t3 (s : ℕ) : 3 * 1 * s = 3 * s := by omega
private theorem l_t31 (t : ℕ) : 3 * 1 * t + 1 = 3 * t + 1 := by omega

/-- The LMD witnessing execution: `Δ = 1` and the *full-history* fork choice
`fcV W s s` — the expiry window is the whole past at every slot, i.e.
LMD-GHOST (`η = ∞`) exactly, at every evaluated round. -/
noncomputable def E4 (τ : ℕ) : Execution Blk V7 (Vw V7) where
  Δ := 1
  Δ_pos := one_pos
  view _ _ := view4 τ
  active _ _ := True
  pivot t := t = 2
  proposerView _ := view4 τ
  proposal t := if t = 2 then bA else gen
  blockView b := blockViewV V7 b
  FC W s := fcV W s s
  votesFor u t b := tab4 τ u t = {b}
  chAt _ r := fcV (view4 τ) (r / 3) (r / 3)

theorem E4_voteRound (τ t : ℕ) : (E4 τ).voteRound t = 3 * t + 1 := l_t31 t

/-- Bundle the RLMD-GHOST fork-choice interface for `E4` (full-history
window). -/
noncomputable def E4_base (τ : ℕ) : RLMDGhostBase (E4 τ) where
  votes W s := votesV W s s
  voteOf W s u := voteOfV W s s u
  effView _ _ := view4 τ
  fc_ghost W s := fcV_ghost W s s
  chAt_fc := by
    intro u s r _ hr
    have hrs : r / 3 = s := by
      rcases hr with h | h
      · rw [h]; show (3 * 1 * s) / 3 = s; rw [l_t3 s]; exact l_d3m s
      · rw [h]; show (3 * 1 * s + 1) / 3 = s; rw [l_t31 s]; exact l_d3ma s
    show fcV (view4 τ) (r / 3) (r / 3) = fcV (view4 τ) s s
    rw [hrs]
  count_le_weight W s B A h := count_le_weight_votesV W s s B A h
  card_le_weight_add W s B A h := card_votesV_le_weight_add W s s B A h
  weight_le_contrib W s B A h := weight_votesV_le_contrib W s s B A h

/-- The LMD sleepy model, `τ`-indexed. `v0` adversarial always; `v5, v6`
(`V3`) awake only through slot 2; `v1` corrupted at slot `τ + 3` — the paper's
"does nothing for `N ≫ τ` slots" delay that lets `V3` leave the `τ`-window
before the corruption. -/
def SM4 (τ : ℕ) : SleepyModel (E4 τ) where
  H t := if t ≤ 2 then {1, 2, 3, 4, 5, 6}
    else if t ≤ τ + 2 then {1, 2, 3, 4} else {2, 3, 4}
  A t := if t ≤ τ + 2 then {0} else {0, 1}
  H_voter := fun _ => trivial

private theorem SM4_A_subset (τ s : ℕ) : (SM4 τ).A s ⊆ ({0, 1} : Finset V7) := by
  simp only [SM4]
  split_ifs
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    decide
  · exact Finset.Subset.refl _

/- Plain-`ℕ` index arithmetic (so `omega` sees through the `Slot` abbrev). -/
private theorem arith_a_u {t u : ℕ} (h2 : t ≤ 2) (hu2 : u + 2 ≤ t + 1) : u ≤ 2 := by
  omega
private theorem arith_b_t {t τ : ℕ} (hb : t ≤ τ + 1) : t ≤ τ + 2 := by omega
private theorem arith_b_A {t τ : ℕ} (hb : t ≤ τ + 1) : t + 1 ≤ τ + 2 := by omega
private theorem arith_b_u {t u τ : ℕ} (hb : t ≤ τ + 1) (hu2 : u + 2 ≤ t + 1) :
    u ≤ τ + 2 := by omega
private theorem arith_c_A {t τ : ℕ} (hb : ¬ t ≤ τ + 1) : ¬ t + 1 ≤ τ + 2 := by omega
private theorem arith_c_u3 {t u τ : ℕ} (hb : ¬ t ≤ τ + 1) (hu1 : t + 1 ≤ u + τ) :
    ¬ u ≤ 2 := by omega
private theorem arith_c_u2 {t u τ : ℕ} (hc : t ≤ τ + 2) (hu2 : u + 2 ≤ t + 1) :
    u ≤ τ + 2 := by omega
private theorem arith_d_A {t τ : ℕ} (hc : ¬ t ≤ τ + 2) : ¬ t + 1 ≤ τ + 2 := by omega
private theorem arith_d_u {t u τ : ℕ} (hc : ¬ t ≤ τ + 2) (hu1 : t + 1 ≤ u + τ) :
    ¬ u ≤ 2 := by omega

/- Concrete `Fin 7` membership facts. -/
private theorem mem56 : ∀ x : V7, x ∈ ({1, 2, 3, 4, 5, 6} : Finset V7) →
    x ∉ ({1, 2, 3, 4} : Finset V7) → x ∈ ({0, 5, 6} : Finset V7) := by decide
private theorem mem1d : ∀ x : V7, x ∈ ({1, 2, 3, 4} : Finset V7) →
    x ∉ ({2, 3, 4} : Finset V7) → x ∈ ({0, 1} : Finset V7) := by decide
private theorem sub0_056 : ({0} : Finset V7) ⊆ ({0, 5, 6} : Finset V7) := by decide

/-- **`E4 τ` is `τ`-compliant.** `τ`-sleepiness holds at every slot: through
slot 2 six honest voters face one adversary; between the sleep of `V3` and the
corruption, the window still reaches `V3`'s slot 2 but `|{v0, v5, v6}| = 3 <
4 = |H_t|`; at the corruption slot `τ + 3` the window `[3, τ + 1]` no longer
contains slot 2, so only `{v0, v1}` count against the three honest voters —
exactly the paper's sleepiness bookkeeping for the `N ≫ τ` delay. -/
theorem SM4_EtaSleepy (τ : ℕ) : (SM4 τ).EtaSleepy τ := by
  intro t
  by_cases h2 : t ≤ 2
  · -- warm-up slots: the window lies inside `H_t`
    have hHt : (SM4 τ).H t = ({1, 2, 3, 4, 5, 6} : Finset V7) := by
      simp only [SM4]; rw [if_pos h2]
    rw [hHt]
    refine lt_of_le_of_lt (Finset.card_le_card ?_)
      (by decide : ({0, 1} : Finset V7).card < ({1, 2, 3, 4, 5, 6} : Finset V7).card)
    apply Finset.union_subset (SM4_A_subset τ (t + 1))
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxw, hxn⟩ := hx
    rw [SleepyModel.mem_Hwindow] at hxw
    obtain ⟨u, hu1, hu2, hxu⟩ := hxw
    have hHu : (SM4 τ).H u = ({1, 2, 3, 4, 5, 6} : Finset V7) := by
      simp only [SM4]; rw [if_pos (arith_a_u h2 hu2)]
    rw [hHu] at hxu
    exact absurd hxu hxn
  · by_cases hb : t ≤ τ + 1
    · -- sleepers gone, corruption not yet: `{v0} ∪ (V3 in window)` vs 4 honest
      have hHt : (SM4 τ).H t = ({1, 2, 3, 4} : Finset V7) := by
        simp only [SM4]; rw [if_neg h2, if_pos (arith_b_t hb)]
      have hA : (SM4 τ).A (t + 1) = ({0} : Finset V7) := by
        simp only [SM4]; rw [if_pos (arith_b_A hb)]
      rw [hHt, hA]
      refine lt_of_le_of_lt (Finset.card_le_card ?_)
        (by decide : ({0, 5, 6} : Finset V7).card < ({1, 2, 3, 4} : Finset V7).card)
      apply Finset.union_subset sub0_056
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxw, hxn⟩ := hx
      rw [SleepyModel.mem_Hwindow] at hxw
      obtain ⟨u, hu1, hu2, hxu⟩ := hxw
      by_cases hu : u ≤ 2
      · have hHu : (SM4 τ).H u = ({1, 2, 3, 4, 5, 6} : Finset V7) := by
          simp only [SM4]; rw [if_pos hu]
        rw [hHu] at hxu
        exact mem56 x hxu hxn
      · have hHu : (SM4 τ).H u = ({1, 2, 3, 4} : Finset V7) := by
          simp only [SM4]; rw [if_neg hu, if_pos (arith_b_u hb hu2)]
        rw [hHu] at hxu
        exact absurd hxu hxn
    · by_cases hc : t ≤ τ + 2
      · -- the corruption slot `t = τ + 2`: the window `[3, τ + 1]` misses slot 2
        have hHt : (SM4 τ).H t = ({1, 2, 3, 4} : Finset V7) := by
          simp only [SM4]; rw [if_neg h2, if_pos hc]
        have hA : (SM4 τ).A (t + 1) = ({0, 1} : Finset V7) := by
          simp only [SM4]; rw [if_neg (arith_c_A hb)]
        rw [hHt, hA]
        refine lt_of_le_of_lt (Finset.card_le_card ?_)
          (by decide : ({0, 1} : Finset V7).card < ({1, 2, 3, 4} : Finset V7).card)
        apply Finset.union_subset (Finset.Subset.refl _)
        intro x hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxw, hxn⟩ := hx
        rw [SleepyModel.mem_Hwindow] at hxw
        obtain ⟨u, hu1, hu2, hxu⟩ := hxw
        have hHu : (SM4 τ).H u = ({1, 2, 3, 4} : Finset V7) := by
          simp only [SM4]
          rw [if_neg (arith_c_u3 hb hu1), if_pos (arith_c_u2 hc hu2)]
        rw [hHu] at hxu
        exact absurd hxu hxn
      · -- after the corruption: `{v0, v1}` vs 3 honest, window past slot 2
        have hHt : (SM4 τ).H t = ({2, 3, 4} : Finset V7) := by
          simp only [SM4]; rw [if_neg h2, if_neg hc]
        have hA : (SM4 τ).A (t + 1) = ({0, 1} : Finset V7) := by
          simp only [SM4]; rw [if_neg (arith_d_A hc)]
        rw [hHt, hA]
        refine lt_of_le_of_lt (Finset.card_le_card ?_)
          (by decide : ({0, 1} : Finset V7).card < ({2, 3, 4} : Finset V7).card)
        apply Finset.union_subset (Finset.Subset.refl _)
        intro x hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxw, hxn⟩ := hx
        rw [SleepyModel.mem_Hwindow] at hxw
        obtain ⟨u, hu1, hu2, hxu⟩ := hxw
        have hu3 : ¬ u ≤ 2 := arith_d_u hc hu1
        by_cases hu4 : u ≤ τ + 2
        · have hHu : (SM4 τ).H u = ({1, 2, 3, 4} : Finset V7) := by
            simp only [SM4]; rw [if_neg hu3, if_pos hu4]
          rw [hHu] at hxu
          exact mem1d x hxu hxn
        · have hHu : (SM4 τ).H u = ({2, 3, 4} : Finset V7) := by
            simp only [SM4]; rw [if_neg hu3, if_neg hu4]
          rw [hHu] at hxu
          exact absurd hxu hxn

private theorem l_2le (τ : ℕ) : (2 : ℕ) ≤ τ + 4 := by omega

/-- **`E4 τ` reorgs the honest proposal.** Slot 2 is a pivot proposing `bA`,
yet at slot `τ + 4` the canonical chain of every active validator is `bB`. -/
theorem E4_not_reorgResilient (τ : ℕ) : ¬ ReorgResilient (E4 τ) := by
  intro hRR
  obtain ⟨hc1, -⟩ := hRR 2 rfl
  have hle := hc1 (τ + 4) (l_2le τ) 0 trivial
  have hprop : (E4 τ).proposal 2 = bA := by
    show (if (2 : Slot) = 2 then bA else gen) = bA
    rfl
  rw [hprop] at hle
  have hch : (E4 τ).chAt (0 : V7) ((E4 τ).voteRound (τ + 4)) = bB := by
    show fcV (view4 τ) (((E4 τ).voteRound (τ + 4)) / 3)
      (((E4 τ).voteRound (τ + 4)) / 3) = bB
    rw [E4_voteRound, l_d3ma, fcV_reorg4]
  rw [hch] at hle
  exact absurd hle (by decide)

/-- **Theorem 4.** LMD-GHOST (RLMD-GHOST with `η = ∞`, rendered exactly by the
full-history fork choice `fcV W s s`) is not `τ`-dynamically-available for
*any* finite `τ`: for every `τ` there is a `τ`-compliant execution — the
paper's per-`τ` construction, with the corruption delayed past the
`τ`-sleepiness window — whose honest pivot proposal `bA` is reorged to `bB` at
slot `τ + 4`. A reorged honest proposal cannot be safely confirmed, so no
confirmation rule makes the execution both safe and live (the reorg-level
rendering, as in Theorem 10). -/
theorem theorem4 (τ : ℕ) :
    ∃ (E : Execution Blk V7 (Vw V7)) (SM : SleepyModel E),
      Nonempty (RLMDGhostBase E) ∧ SM.EtaSleepy τ ∧ ¬ ReorgResilient E :=
  ⟨E4 τ, SM4 τ, ⟨E4_base τ⟩, SM4_EtaSleepy τ, E4_not_reorgResilient τ⟩

end Tightness

end RLMDGhost
