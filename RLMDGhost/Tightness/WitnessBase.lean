import RLMDGhost.Tightness.Witness
import RLMDGhost.Security.Basic

/-!
# Witness → `RLMDGhostBase`

The concrete witness layer (`RLMDGhost.Tightness.Witness`) proves the counting
bookkeeping (`count_le_weight_votesV`, `card_votesV_le_weight_add`,
`weight_votesV_le_contrib`), the GHOST-descent property (`fcV_ghost`), and the
§2 consistency of the fork choice (`fcV_consistency`) over an *arbitrary* finite
validator type. This file bundles them into the abstract `RLMDGhostBase`
interface, so that any adversarial `Execution` whose fork choice is `fcV` — the
common shape of every Track B/D impossibility construction — obtains its
`RLMDGhostBase` for free.

`witnessBase` takes the two structural facts that tie a concrete `Execution` to
the witness (`hFC`: its fork choice *is* `fcV`; `hchAt`: its canonical chain at
the fork-choice rounds is that fork choice on the supplied `effView`) and fills
the five `RLMDGhostBase` fields from the witness lemmas. The impossibility
theorems then only need to build the `Execution` and discharge `hFC`/`hchAt`,
plus the `η`/`τ`-sleepiness bookkeeping and the property violation.
-/

namespace RLMDGhost

namespace Tightness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bundle the witness counting/fork-choice lemmas into `RLMDGhostBase`, for any
`Execution` over the four-block witness tree whose fork choice is `fcV η` and
whose canonical chain at the fork-choice rounds is that fork choice on
`effView`. -/
noncomputable def witnessBase (E : Execution Blk V (Vw V)) (η : ℕ)
    (hFC : ∀ (W : Vw V) (s : Slot), E.FC W s = fcV W η s)
    (effView : V → Round → Vw V)
    (hchAt : ∀ {v : V} {s : Slot} {r : Round}, E.active v r →
      r = E.slotStart s ∨ r = E.voteRound s → E.chAt v r = E.FC (effView v r) s) :
    RLMDGhostBase E where
  votes W s := votesV W η s
  voteOf W s u := voteOfV W η s u
  effView := effView
  fc_ghost W s := by rw [hFC]; exact fcV_ghost W η s
  chAt_fc := hchAt
  count_le_weight W s B A h := count_le_weight_votesV W η s B A h
  card_le_weight_add W s B A h := card_votesV_le_weight_add W η s B A h
  weight_le_contrib W s B A h := weight_votesV_le_contrib W η s B A h

@[simp] theorem witnessBase_votes (E : Execution Blk V (Vw V)) (η : ℕ)
    (hFC) (effView) (hchAt) (W : Vw V) (s : Slot) :
    (witnessBase E η hFC effView hchAt).votes W s = votesV W η s := rfl

@[simp] theorem witnessBase_voteOf (E : Execution Blk V (Vw V)) (η : ℕ)
    (hFC) (effView) (hchAt) (W : Vw V) (s : Slot) (u : V) :
    (witnessBase E η hFC effView hchAt).voteOf W s u = voteOfV W η s u := rfl

end Tightness

end RLMDGhost
