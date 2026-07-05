import RLMDGhost.Tightness.Theorem11

/-!
# Theorem 5 — Goldfish is not `(τ, π)`-asynchrony-resilient for any `τ > π ≥ 2`

Goldfish is RLMD-GHOST with `η = 1` (GHOST-Eph: only the immediately-previous
slot's votes count). A temporary period of asynchrony of length `π ≥ 2` — longer
than the length-1 expiry window — lets *all* votes for the honest chain expire,
after which the adversary's genesis-extension `bB` (proposed inside the tpa) is
tiebreak-selected and reorgs the honest proposal. This is the `η = 1`
specialisation of the Theorem 11 mechanism; it reuses the tiebreak-toward-`bB`
fork choice `fcVB` at `η = 1`.
-/

namespace RLMDGhost

namespace Tightness

open Blk

/-- The Goldfish (`η = 1`) vote table over a length-2 tpa `(2, 4)`: `bA` proposed
at the pivot slot 2, `v2` proposing/voting the genesis-extension `bB` from slot
4 on. -/
def tab5 (u : V3) (u' : ℕ) : Finset Blk :=
  if u' ≤ 1 then {gen}
  else if u.val = 0 then (if u' = 2 then {bA} else ∅)
  else if u.val = 1 then {bA}
  else (if 4 ≤ u' then {bB} else ∅)

def view5 : Vw V3 := (({gen, bA, bB} : Finset Blk), tab5)

theorem view5_fst : (view5).1 = ({gen, bA, bB} : Finset Blk) := rfl
theorem okBlk_bA_view5 : okBlk (view5).1 bA := by rw [view5_fst]; decide
theorem okBlk_bB_view5 : okBlk (view5).1 bB := by rw [view5_fst]; decide

/-! ### Counted votes at the reorg slot 5 (Goldfish window `[4, 4]`) -/

theorem voteOf5_v1 {u : V3} (h : u.val = 1) : voteOfV view5 1 5 u = some bA := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ okBlk_bA_view5
  show tab5 u (5 - 1) = {bA}
  rw [show (5 - 1) = 4 from rfl]; unfold tab5
  rw [if_neg (by omega : ¬ (4:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0), if_pos h]

theorem voteOf5_v2 {u : V3} (h : u.val = 2) : voteOfV view5 1 5 u = some bB := by
  unfold voteOfV
  refine voteOf1_at_prev (by omega) (by omega) ?_ okBlk_bB_view5
  show tab5 u (5 - 1) = {bB}
  rw [show (5 - 1) = 4 from rfl]; unfold tab5
  rw [if_neg (by omega : ¬ (4:ℕ) ≤ 1), if_neg (by omega : ¬ u.val = 0),
    if_neg (by omega : ¬ u.val = 1), if_pos (by omega : (4:ℕ) ≤ 4)]

theorem voteOf5_v0 {u : V3} (h : u.val = 0) : voteOfV view5 1 5 u = none := by
  unfold voteOfV
  apply voteOf1_eq_none_of_empty
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u' hu'
  rw [mem_cand] at hu'
  obtain ⟨hlt, hwin, hne⟩ := hu'
  apply hne
  show tab5 u u' = ∅
  -- window `[4, 4]` (η = 1): `u' = 4`, where `v0` has no vote
  unfold tab5
  rw [if_neg (by omega : ¬ u' ≤ 1), if_pos h, if_neg (by omega : ¬ u' = 2)]

theorem voteOfV_eq_expected5 (u : V3) : voteOfV view5 1 5 u = expected11 u := by
  unfold expected11
  by_cases h0 : u.val = 0
  · rw [if_pos h0, voteOf5_v0 h0]
  · rw [if_neg h0]
    by_cases h1 : u.val = 1
    · rw [if_pos h1, voteOf5_v1 h1]
    · rw [if_neg h1, voteOf5_v2 (by omega)]

theorem weight_bA_reorg5 : weight bA (votesV view5 1 5) = 1 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V3 => ∃ b, voteOfV view5 1 5 u = some b ∧ bA ≤ b) =
      Finset.univ.filter fun u : V3 => ∃ b, expected11 u = some b ∧ bA ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected5 u]
  rw [this]; decide

theorem weight_bB_reorg5 : weight bB (votesV view5 1 5) = 1 := by
  rw [weight_votesV_eq]
  have : (Finset.univ.filter fun u : V3 => ∃ b, voteOfV view5 1 5 u = some b ∧ bB ≤ b) =
      Finset.univ.filter fun u : V3 => ∃ b, expected11 u = some b ∧ bB ≤ b := by
    apply Finset.filter_congr; intro u _; rw [voteOfV_eq_expected5 u]
  rw [this]; decide

/-- **The Goldfish asynchrony reorg.** At slot 5 the fork choice outputs `bB`:
after the length-2 tpa, all `bA` votes have expired from the Goldfish window
`[4, 4]`; only `v1`'s `bA` and `v2`'s `bB` (both from slot 4) remain, a 1-1 tie
the adversarial tiebreak `fcVB` resolves to `bB`. -/
theorem fcVB_reorg5 : fcVB view5 1 5 = bB := by
  unfold fcVB
  rw [if_pos]
  refine ⟨okBlk_bB_view5, ?_⟩
  rw [weight_bA_reorg5, weight_bB_reorg5]
  rintro ⟨hlt, -⟩; omega

/-! ## The Goldfish execution and the theorem -/

private theorem g_d3ma (s : ℕ) : (3 * s + 1) / 3 = s := by omega
private theorem g_d3m (s : ℕ) : (3 * s) / 3 = s := by omega
private theorem g_t3 (s : ℕ) : 3 * 1 * s = 3 * s := by omega
private theorem g_t31 (t : ℕ) : 3 * 1 * t + 1 = 3 * t + 1 := by omega

/-- The Goldfish witnessing execution (`η = 1`, GHOST-Eph fork choice `fcVB`). -/
noncomputable def E5 : Execution Blk V3 (Vw V3) where
  Δ := 1
  Δ_pos := one_pos
  view _ _ := view5
  active _ _ := True
  pivot t := t = 2
  proposerView _ := view5
  proposal t := if t = 2 then bA else gen
  blockView b := blockViewV V3 b
  FC W s := fcVB W 1 s
  votesFor u t b := b = fcVB view5 1 ((3 * 1 * t + 1) / 3)
  chAt u r := fcVB view5 1 (r / 3)

theorem E5_voteRound (t : ℕ) : (E5).voteRound t = 3 * t + 1 := g_t31 t

noncomputable def E5_base : RLMDGhostBase E5 where
  votes W s := votesV W 1 s
  voteOf W s u := voteOfV W 1 s u
  effView _ _ := view5
  fc_ghost W s := fcVB_ghost W 1 s
  chAt_fc := by
    intro u s r _ hr
    have hrs : r / 3 = s := by
      rcases hr with h | h
      · rw [h]; show (3 * 1 * s) / 3 = s; rw [g_t3 s]; exact g_d3m s
      · rw [h]; show (3 * 1 * s + 1) / 3 = s; rw [g_t31 s]; exact g_d3ma s
    show fcVB view5 1 (r / 3) = fcVB view5 1 s
    rw [hrs]
  count_le_weight W s B A h := count_le_weight_votesV W 1 s B A h
  card_le_weight_add W s B A h := card_votesV_le_weight_add W 1 s B A h
  weight_le_contrib W s B A h := weight_votesV_le_contrib W 1 s B A h

/-- The Goldfish sleepy model over the length-2 tpa `(2, 4)`. -/
def SM5 : SleepyModel E5 where
  H t := if t ≤ 2 then {0, 1} else if t ≤ 3 then {1}
    else if t ≤ 4 then {1, 2} else {0, 1, 2}
  A _ := ∅
  H_voter := fun _ => trivial

theorem SM5_card {t : ℕ} (h : t ≤ 2 ∨ 4 ≤ t) :
    (Finset.univ \ (SM5).H t).card < ((SM5).H t).card := by
  simp only [SM5]
  rcases h with h | h
  · rw [if_pos h]; decide
  · rw [if_neg (by omega : ¬ t ≤ 2), if_neg (by omega : ¬ t ≤ 3)]
    by_cases h4 : t ≤ 4
    · rw [if_pos h4]; decide
    · rw [if_neg h4]; decide

theorem SM5_bound (s t : ℕ) (Hw : Finset V3) :
    ((SM5).A s ∪ (Hw \ (SM5).H t)).card ≤ (Finset.univ \ (SM5).H t).card := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact absurd hx (by simp [SM5])
  · rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_univ x, hx.2⟩

private theorem eso5_bound {t : ℕ} (h : t + 1 ≤ 2 ∨ 4 + 1 ≤ t + 1) : t ≤ 2 ∨ 4 ≤ t := by omega

theorem SM5_EtaSleepyOutside : (SM5).EtaSleepyOutside 1 2 4 := by
  intro t h
  exact lt_of_le_of_lt (SM5_bound _ _ _) (SM5_card (eso5_bound h))

theorem SM5_TpaSleepy : (SM5).TpaSleepy 1 2 4 := by
  intro s _ _
  have hA : (SM5).H 2 \ (SM5).A s = (SM5).H 2 := by simp [SM5]
  rw [hA]
  exact lt_of_le_of_lt (SM5_bound _ _ _) (SM5_card (Or.inl (le_refl 2)))

/-- Goldfish reorgs the honest proposal over the length-2 tpa. -/
theorem E5_not_asynchronyResilient : ¬ AsynchronyResilient E5 SM5 2 4 := by
  intro hAR
  obtain ⟨hc1, -⟩ := hAR 2 (le_refl 2) rfl
  have haw : Aware E5 SM5 2 4 (0 : V3) 5 ((E5).voteRound 5) :=
    ⟨trivial, fun _ h => absurd h (by decide)⟩
  have hle := hc1 5 (by decide) 0 haw
  have hprop : (E5).proposal 2 = bA := by show (if (2:Slot) = 2 then bA else gen) = bA; rfl
  rw [hprop] at hle
  have hch : (E5).chAt (0 : V3) ((E5).voteRound 5) = bB := by
    show fcVB view5 1 (((E5).voteRound 5) / 3) = bB
    rw [E5_voteRound]; show fcVB view5 1 ((3 * 5 + 1) / 3) = bB
    rw [g_d3ma, fcVB_reorg5]
  rw [hch] at hle
  exact absurd hle (by decide)

/-- **Theorem 5.** Goldfish (`η = 1`) is not `(τ, π)`-asynchrony-resilient for
`π = 2`: there is an execution with the Goldfish GHOST-Eph fork choice and a
length-2 tpa `(2, 4)`, satisfying the tpa sleepiness conditions, in which the
honest proposal of the pivot slot 2 is reorged at the aware slot 5. (By
`E_{τ,π} ⊇ E_{∞,2}`, the same witness refutes `(τ, π)`-asynchrony-resilience for
all `τ > π ≥ 2`.) -/
theorem theorem5 :
    ∃ (E : Execution Blk V3 (Vw V3)) (SM : SleepyModel E) (t1 t2 : Slot),
      Nonempty (RLMDGhostBase E) ∧ t2 = t1 + 2 ∧
        SM.EtaSleepyOutside 1 t1 t2 ∧ SM.TpaSleepy 1 t1 t2 ∧
        ¬ AsynchronyResilient E SM t1 t2 :=
  ⟨E5, SM5, 2, 4, ⟨E5_base⟩, rfl, SM5_EtaSleepyOutside, SM5_TpaSleepy,
    E5_not_asynchronyResilient⟩

end Tightness

end RLMDGhost
