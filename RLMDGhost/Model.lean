import RLMDGhost.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

/-!
# RLMD-GHOST — the generalized sleepy model

The paper proves its results in a *generalized sleepy model* (Pass–Shi extended
with stronger corruption/sleepiness constraints). A validator is, per slot,
either honest or adversarial and either active (participating after the joining
protocol) or not. We record per-slot finite voter sets and the compliance
inequalities as a structure of hypotheses (Barrier 3 of the formalization
strategy): the substance of the RLMD argument is the **`η`-sleepiness
inequality**

> `|H_{t-1}| > |A_t ∪ (H_{t-η,t-2} \ H_{t-1})|`

which is the defining premise of Lemma 4. `H_{a,b}` denotes validators that were
honest active voters in at least one slot of the range `[a, b]`.
-/

namespace RLMDGhost

/-- The generalized sleepy model over a validator type, recording the honest and
adversarial *active voter* sets at each slot. `honest t = H_t` and `adv t = A_t`
are finite (the validator population at any slot is finite). -/
structure SleepyModel (Validator : Type*) where
  /-- `H_t`: honest validators that are active voters at slot `t`. -/
  honest : Slot → Finset Validator
  /-- `A_t`: adversarial validators relevant at slot `t`. -/
  adv : Slot → Finset Validator

namespace SleepyModel

variable {Validator : Type*} [DecidableEq Validator] (M : SleepyModel Validator)

/-- `H_{a,b}`: validators that were honest active voters in at least one slot of
the inclusive range `[a, b]`. -/
def honestRange (a b : Slot) : Finset Validator :=
  (Finset.Icc a b).biUnion M.honest

/-- The set of votes, at slot `t`, that are *not* guaranteed to be for a
descendant of the block in question: the adversary `A_t` together with honest
validators that voted somewhere in `[t-η, t-2]` but dropped out by slot `t-1`
(`H_{t-η,t-2} \ H_{t-1}`). This is the right-hand side of the `η`-sleepiness
inequality. -/
def staleAdversarial (η t : Slot) : Finset Validator :=
  M.adv t ∪ (M.honestRange (t - η) (t - 2) \ M.honest (t - 1))

/-- **`η`-sleepiness at slot `t`** (the Lemma 4 premise): the honest active
voters of slot `t-1` strictly outnumber the adversarial-or-stale set. -/
def EtaSleepy (η t : Slot) : Prop :=
  (M.staleAdversarial η t).card < (M.honest (t - 1)).card

/-- **`η`-compliance**: `η`-sleepiness holds at every slot. An `η`-compliant
execution is one in which the active honest set never shrinks fast enough,
relative to the `η`-window of expiring votes, to be outweighed. -/
def EtaCompliant (η : Slot) : Prop :=
  ∀ t : Slot, M.EtaSleepy η t

theorem EtaCompliant.etaSleepy {η : Slot} (h : M.EtaCompliant η) (t : Slot) :
    M.EtaSleepy η t := h t

end SleepyModel

end RLMDGhost
