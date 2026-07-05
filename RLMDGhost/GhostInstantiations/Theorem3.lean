import Mathlib.Data.Finset.Card
import RLMDGhost.GhostInstantiations.Lemma3
import RLMDGhost.ProposeVoteMerge.Lemma1

/-!
# Theorem 3 — strong reorg resilience of LMD-GHOST with view-merge

> **Theorem 3** (Strong reorg resilience, arXiv:2302.11326). Consider an honest
> proposal `B` from a slot `t` in which network synchrony holds and
> `|H̃_t| > n/2`. Suppose that validators in `H̃_t` do not fall asleep in rounds
> `[3∆t + ∆, 3∆t + 2∆]`. Then, `B` is always canonical in all honest views
> which contain all slot `t` votes from `H̃_t`.

Rendering against the abstract interfaces:

* "honest proposal from a slot in which network synchrony holds" is `pivot t`,
  exactly the premise under which Lemma 1 makes every `H̃_t` member vote for
  `B = proposal t` at round `3∆t + ∆`;
* `H̃_t` is a `Finset Ht` of honest slot-`t` voters with `2·|H̃_t| > n`;
* LMD-GHOST is the `LMDGhost` interface below: the fork choice runs the GHOST
  descent on the latest-message votes `votes V` counted by
  `FIL_lmd ∘ FIL_eq` — at most one per validator, hence `|votes V| ≤ n`, and
  with no expiry (`η = ∞`) the `H̃_t` votes stay counted forever;
* "honest views which contain all slot `t` votes from `H̃_t`" — since LMD
  counts only each validator's *latest* message, a view contains the slot-`t`
  votes of `H̃_t` (as counted votes) when each `v ∈ H̃_t` contributes a latest
  message extending its slot-`t` vote (`hlatest`); Lemma 1 plus honest
  non-equivocation (`Spec.vote_unique`) identify that slot-`t` vote with `B`;
* "always canonical" — the conclusion holds for the fork choice of *every*
  such view at *every* slot `s`, with no sleepiness assumption after slot `t`:
  the majority `2·|H̃_t| > n` beats the total vote count in perpetuity.

The proof is the paper's: Lemma 1 gives the `H̃_t` votes for `B`, counting gives
`w(B, votes V) ≥ |H̃_t| > n/2 ≥ |votes V|/2`, and Lemma 3 forces the GHOST
output to extend `B`.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [FiniteAncestors Block]
  [SemilatticeSup View]

/-- The LMD-GHOST instantiation interface (§4.2, Barrier 4): the fork choice is
the GHOST descent over the per-view counted votes `votes V`, the latest
messages surviving `FIL_lmd ∘ FIL_eq` (no expiry, `η = ∞`).

`contributes V v b` says the latest message of validator `v` counted in view
`V` is a vote for `b`. The two counting fields are bookkeeping consequences of
"one latest message per validator": the counted votes number at most `n`, and
any set of validators contributing votes for descendants of `B` is counted into
`w(B, votes V)`. -/
structure LMDGhost (E : Execution Block Validator View) where
  /-- Total number of validators `n`. -/
  n : ℕ
  /-- The votes counted by the fork choice in view `V`: the latest messages
  surviving `FIL_lmd ∘ FIL_eq`. -/
  votes : View → Multiset Block
  /-- `contributes V v b`: the counted (latest) message of `v` in `V` is a vote
  for `b`. -/
  contributes : View → Validator → Block → Prop
  /-- One latest message per validator: at most `n` votes are counted. -/
  votes_card_le : ∀ V : View, (votes V).card ≤ n
  /-- Counting: validators contributing votes for descendants of `B` are
  pairwise-distinct contributors to the weight of `B`. -/
  count_le_weight :
    ∀ (V : View) (A : Finset Validator) (B : Block),
      (∀ v ∈ A, ∃ b, B ≤ b ∧ contributes V v b) →
      A.card ≤ weight B (votes V)
  /-- The fork choice is a GHOST descent on the counted votes. -/
  fc_ghost : ∀ (V : View) (t : Slot), GhostSelects (votes V) (E.FC V t)

/-- **Theorem 3 (Strong reorg resilience).** For LMD-GHOST with view-merge: if
`t` is a pivot slot whose honest voters include a set `H̃_t` with
`2·|H̃_t| > n`, then the proposal of slot `t` is canonical in every view whose
counted latest messages contain, for each `v ∈ H̃_t`, a vote extending `v`'s
slot-`t` vote — at every slot `s`, with no further participation assumption. -/
theorem theorem3 {E : Execution Block Validator View} (S : Spec E) (L : LMDGhost E)
    {t s : Slot} {V : View} (hpivot : E.pivot t) (Ht : Finset Validator)
    (hvoters : ∀ v ∈ Ht, E.voter v t)
    (hmaj : L.n < 2 * Ht.card)
    (hlatest : ∀ v ∈ Ht, ∃ b, L.contributes V v b ∧
      ∃ bt, E.votesFor v t bt ∧ bt ≤ b) :
    E.proposal t ≤ E.FC V s := by
  have hcount : ∀ v ∈ Ht, ∃ b, E.proposal t ≤ b ∧ L.contributes V v b := by
    intro v hv
    obtain ⟨b, hc, bt, hvote, hbt⟩ := hlatest v hv
    have hBt : bt = E.proposal t :=
      S.vote_unique (hvoters v hv) hvote (lemma1 S hpivot (hvoters v hv))
    exact ⟨b, hBt ▸ hbt, hc⟩
  have h1 : Ht.card ≤ weight (E.proposal t) (L.votes V) :=
    L.count_le_weight V Ht _ hcount
  have h2 : (L.votes V).card ≤ L.n := L.votes_card_le V
  exact lemma3 (by omega) (L.fc_ghost V s)

end RLMDGhost
