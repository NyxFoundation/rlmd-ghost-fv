import RLMDGhost.Protocol

/-!
# Proposition 1 — persistence: slot-`t` votes for `B` keep `B` canonical at slot `t+1`

> **Proposition 1** (arXiv:2302.11326). Suppose that all honest voters of slot
> `t − 1` vote for a descendant of block `B`. Then, `B` is in the canonical
> chain of all active validators in rounds `{3∆t, 3∆t + ∆}`. In particular, all
> honest voters of slot `t` vote for descendants of `B`.

Proposition 1 is stated as a *property* of an execution rather than proved
free-standing: the paper establishes it per protocol (for RLMD-GHOST in
`η`-compliant executions by Lemma 4, issue #10; for the Goldfish-style
instantiations in §4). Here it is the predicate `Persistence`, threaded as the
hypothesis of Theorem 1, exactly as the paper threads it ("Let us consider an
execution ... in which Proposition 1 holds").

The slot index is shifted from the paper's `t − 1 / t` to `t / t + 1` to avoid
truncated subtraction on `ℕ`.

The "in particular" clause *is* proved here (`Persistence.votes_carry`): it
follows from the persistence conclusion together with the voting rule
(`Spec.vote_chAt`), since a voter's vote is the tip of a canonical chain that
extends `B`.
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]

/-- **Proposition 1 (persistence)** as a predicate on executions: whenever all
honest voters of a slot `t` vote for descendants of a block `B`, the block `B`
is in the canonical chain of every honest active validator at both fork-choice
rounds `{3∆(t+1), 3∆(t+1) + ∆}` of the next slot. -/
def Persistence (E : Execution Block Validator View) : Prop :=
  ∀ (t : Slot) (B : Block),
    (∀ v : Validator, E.voter v t → E.votesForDescendant v t B) →
    ∀ v : Validator,
      (E.active v (E.slotStart (t + 1)) → B ≤ E.chAt v (E.slotStart (t + 1))) ∧
      (E.active v (E.voteRound (t + 1)) → B ≤ E.chAt v (E.voteRound (t + 1)))

namespace Persistence

variable {E : Execution Block Validator View}

/-- The "in particular" clause of Proposition 1: if all honest voters of slot
`t` vote for descendants of `B`, then all honest voters of slot `t + 1` also
vote for descendants of `B`. -/
theorem votes_carry (hP : Persistence E) (S : Spec E) {t : Slot} {B : Block}
    (hvotes : ∀ v : Validator, E.voter v t → E.votesForDescendant v t B) :
    ∀ v : Validator, E.voter v (t + 1) → E.votesForDescendant v (t + 1) B :=
  fun v hv => ⟨E.chAt v (E.voteRound (t + 1)), (hP t B hvotes v).2 hv, S.vote_chAt hv⟩

end Persistence

end RLMDGhost
