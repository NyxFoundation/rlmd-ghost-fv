import RLMDGhost.Security.Basic

/-!
# RLMD-GHOST — the fast-confirmation interface (Appendix B)

Fast confirmation (§B) is an *optimistic single-slot* confirmation rule: an
honest validator fast confirms a block `B` at slot `t` when it observes at least
`⌈2n/3⌉` slot-`t` votes for `B`. On top of the fully synchronous RLMD-GHOST
model of Track C (fast confirmations only *add* to the protocol — the reorg /
availability results of Lemma 4 / Theorems 6–7 still hold), this layer adds the
abstract fast-confirmation interface (Barrier 4) that Lemma 5 and Theorems 12–14
consume.

With `n₃ = ⌈n/3⌉`, the counting content of Lemma 5 is packaged as three
`Finset`s per slot and their cardinality bounds:

* `quorum t` — the honest slot-`t` voters whose votes witnessed the fast
  confirmation of `B`; `2·n₃ ≤ |quorum t|` (the `≥ 2n/3` quorum), and each
  member is an honest voter of `t` voting for a descendant of `B`;
* `equiv t` — the validators seen as equivocators in a slot-`(t+1)` view;
  `|equiv t| < n₃` (the `< n/3` good event of `η`-compliance);
* `offB t` — the non-quorum contributors of counted votes conflicting with `B`;
  `|offB t| < n₃` (the paper's `≤ n/3` bound on conflicting votes).

Then `w(B) ≥ |quorum \ equiv| ≥ 2n₃ − |equiv| > n₃ > |offB| ≥ w(B′)` for every
conflicting `B′`, and `canonical_of_conflict_lt` makes `B` canonical.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  [DecidableEq Validator]

/-- The abstract fast-confirmation instantiation (Appendix B, Barrier 4), over a
fully synchronous RLMD-GHOST model. See the module docstring for provenance. -/
structure FastConfirmModel (E : Execution Block Validator View)
    (SM : SleepyModel E) (η n₃ : ℕ) extends RLMDGhostModel E SM η where
  /-- `fastConfirms v t B`: validator `v` fast confirms `B` at slot `t`. -/
  fastConfirms : Validator → Slot → Block → Prop
  /-- The honest slot-`t` voters whose votes witnessed the fast confirmation. -/
  quorum : Slot → Finset Validator
  /-- The validators seen as equivocators in a slot-`(t+1)` view. -/
  equiv : Slot → Finset Validator
  /-- The non-quorum contributors of counted votes conflicting with `B`. -/
  offB : Slot → Finset Validator
  /-- **Fast-confirmation quorum** (`≥ 2n/3`). -/
  quorum_card : ∀ {v : Validator} {t : Slot} {B : Block}, fastConfirms v t B →
    2 * n₃ ≤ (quorum t).card
  /-- Quorum members are honest voters of slot `t` voting for descendants of
  `B`. -/
  quorum_voter : ∀ {v : Validator} {t : Slot} {B : Block}, fastConfirms v t B →
    ∀ u ∈ quorum t, E.voter u t
  /-- **Low-equivocation good event** (`< n/3`, from `η`-compliance). -/
  lowEquiv : ∀ {v : Validator} {t : Slot} {B : Block}, fastConfirms v t B →
    (equiv t).card < n₃
  /-- **Conflicting-vote bound** (`< n/3`). -/
  offB_card : ∀ {v : Validator} {t : Slot} {B : Block}, fastConfirms v t B →
    (offB t).card < n₃
  /-- **Synchrony delivery of the quorum** (§B): in the effective view of an
  active validator at a fork-choice round of slot `t + 1`, each quorum member
  outside `equiv t` has its counted slot-`(t+1)` vote for a descendant of `B`. -/
  quorum_counted :
    ∀ {v : Validator} {t : Slot} {B : Block}, fastConfirms v t B →
      ∀ {w : Validator} {r : Round}, E.active w r →
        r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1) →
        ∀ u ∈ quorum t, u ∉ equiv t →
          ∃ b, toRLMDGhostModel.voteOf (toRLMDGhostModel.effView w r) (t + 1) u
                = some b ∧ B ≤ b
  /-- **Provenance of conflicting counted votes** (§B): a slot-`(t+1)` counted
  vote not for a descendant of `B` comes from a non-quorum contributor
  (`offB t`). -/
  counted_offB :
    ∀ {v : Validator} {t : Slot} {B : Block}, fastConfirms v t B →
      ∀ {w : Validator} {r : Round}, E.active w r →
        r = E.slotStart (t + 1) ∨ r = E.voteRound (t + 1) →
        ∀ u b, toRLMDGhostModel.voteOf (toRLMDGhostModel.effView w r) (t + 1) u
              = some b → ¬B ≤ b → u ∈ offB t

end RLMDGhost
