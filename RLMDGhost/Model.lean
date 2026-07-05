import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import RLMDGhost.Protocol

/-!
# RLMD-GHOST — the generalized sleepy model

Per Barrier 3 of `docs/formalization-strategy.md`, the sleepy environment is an
abstract structure carrying the honest/adversarial validator sets per slot,
with the compliance inequalities as hypotheses.

`SleepyModel` records, for each slot, the honest voters `H_t` (honest
validators active at the voting round `3∆t + ∆`) and the corrupted set `A_t`,
as `Finset`s so the compliance *cardinality* inequalities can be stated.
`Hwindow η s` is the paper's `H_{s−η, s−2}` — the honest validators active in
at least one slot of the window `[s−η, s−2]` — rendered subtraction-free
(`u ∈ [s−η, s−2] ⟺ s ≤ u + η ∧ u + 2 ≤ s`) so that the window is genuinely
empty for small `s` instead of collapsing onto slot `0` under truncated `ℕ`
subtraction.

`EtaSleepy` is the `η`-sleepiness inequality of §5.1,

  `|H_{s−1}| > |A_s ∪ (H_{s−η, s−2} \ H_{s−1})|`,

stated at `s = t + 1` for every `t` (again avoiding `s − 1`). An `η`-compliant
execution is one satisfying `η`-sleepiness; the synchrony half of compliance
lives in the protocol mechanics (`Spec` and the `RLMDGhostModel` interface of
`RLMDGhost.Security.Basic`).

The `(τ, π)`-compliance vocabulary and the temporary period of asynchrony
(`(η−1)`-tpa) used by Theorem 8 and Track D extend this file when those
statements are taken up.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]

/-- The generalized sleepy environment of an execution: per-slot honest-voter
and corrupted validator sets. Everything downstream consumes only the
cardinality hypotheses (`EtaSleepy`, …), never an operational
awake/asleep schedule. -/
structure SleepyModel (E : Execution Block Validator View) where
  /-- `H_t`: the honest voters of slot `t` — honest validators active at the
  voting round `3∆t + ∆`. -/
  H : Slot → Finset Validator
  /-- `A_t`: the validators corrupted (adversarial) by slot `t`. Corruption is
  monotone in the paper; only the per-slot sets enter the inequalities. -/
  A : Slot → Finset Validator
  /-- Members of `H_t` are honest voters of slot `t` in the execution. -/
  H_voter : ∀ {t : Slot} {v : Validator}, v ∈ H t → E.voter v t

namespace SleepyModel

variable {E : Execution Block Validator View} [DecidableEq Validator]

/-- `H_{s−η, s−2}` (paper notation): honest validators active in at least one
slot of the window `[s−η, s−2]`, i.e. those whose (non-expired at slot `s`)
latest vote may be from a slot strictly before `s − 1`. Subtraction-free:
`u ∈ [s−η, s−2] ⟺ s ≤ u + η ∧ u + 2 ≤ s`. -/
def Hwindow (SM : SleepyModel E) (η s : Slot) : Finset Validator :=
  ((Finset.range s).filter fun u => s ≤ u + η ∧ u + 2 ≤ s).biUnion SM.H

theorem mem_Hwindow {SM : SleepyModel E} {η s : Slot} {v : Validator} :
    v ∈ SM.Hwindow η s ↔ ∃ u : Slot, s ≤ u + η ∧ u + 2 ≤ s ∧ v ∈ SM.H u := by
  simp only [Hwindow, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨u, ⟨-, h1, h2⟩, hv⟩; exact ⟨u, h1, h2, hv⟩
  · rintro ⟨u, h1, h2, hv⟩; exact ⟨u, ⟨Nat.le_of_succ_le h2, h1, h2⟩, hv⟩

/-- **`η`-sleepiness** (§5.1): at every slot `s = t + 1`, the honest voters of
the previous slot outnumber the corrupted validators together with the honest
validators whose only in-window votes are stale
(`|H_{s−1}| > |A_s ∪ (H_{s−η, s−2} \ H_{s−1})|`). An execution satisfying this
(together with the synchrony mechanics of the protocol interface) is
`η`-compliant (Definition 1). -/
def EtaSleepy (SM : SleepyModel E) (η : ℕ) : Prop :=
  ∀ t : Slot,
    (SM.A (t + 1) ∪ (SM.Hwindow η (t + 1) \ SM.H t)).card < (SM.H t).card

/-- `H_{s−η, s−1}` (paper notation): honest validators active in at least one
slot of the *inclusive* window `[s−η, s−1]` — the full expiry window of slot
`s`, used by the `(τ, π)`-compliance inequality (Definition 3). Rendered
subtraction-free like `Hwindow`. -/
def HwindowIncl (SM : SleepyModel E) (η s : Slot) : Finset Validator :=
  ((Finset.range s).filter fun u => s ≤ u + η ∧ u + 1 ≤ s).biUnion SM.H

theorem mem_HwindowIncl {SM : SleepyModel E} {η s : Slot} {v : Validator} :
    v ∈ SM.HwindowIncl η s ↔ ∃ u : Slot, s ≤ u + η ∧ u + 1 ≤ s ∧ v ∈ SM.H u := by
  simp only [HwindowIncl, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨u, ⟨-, h1, h2⟩, hv⟩; exact ⟨u, h1, h2, hv⟩
  · rintro ⟨u, h1, h2, hv⟩; exact ⟨u, ⟨h2, h1, h2⟩, hv⟩

/-- The synchronous-slot half of `(η, π)`-compliance (Definition 3, first
bullet): `η`-sleepiness at every slot outside the tpa-affected interval
`(t1, t2]`, i.e. at slots `t + 1 ≤ t1` and `t + 1 ≥ t2 + 1`. -/
def EtaSleepyOutside (SM : SleepyModel E) (η t1 t2 : Slot) : Prop :=
  ∀ t : Slot, t + 1 ≤ t1 ∨ t2 + 1 ≤ t + 1 →
    (SM.A (t + 1) ∪ (SM.Hwindow η (t + 1) \ SM.H t)).card < (SM.H t).card

/-- The tpa half of `(η, π)`-compliance (Definition 3, second bullet): for
every slot `s ∈ (t1, t2 + 1]`, the slot-`t1` honest voters still honest at `s`
outnumber the corrupted validators together with the in-window voters outside
`H_{t1}`: `|H_{t1} \ A_s| > |A_s ∪ (H_{s−η, s−1} \ H_{t1})|`. -/
def TpaSleepy (SM : SleepyModel E) (η t1 t2 : Slot) : Prop :=
  ∀ s : Slot, t1 < s → s ≤ t2 + 1 →
    (SM.A s ∪ (SM.HwindowIncl η s \ SM.H t1)).card < (SM.H t1 \ SM.A s).card

end SleepyModel

end RLMDGhost
