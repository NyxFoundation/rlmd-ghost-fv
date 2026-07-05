import RLMDGhost.ProposeVoteMerge.Lemma1
import RLMDGhost.ProposeVoteMerge.Proposition1

/-!
# Theorem 1 — reorg resilience: an honest proposal is never reorged

> **Theorem 1** (Reorg resilience, arXiv:2302.11326). Let us consider an
> execution of a propose-vote-merge protocol in which Proposition 1 holds.
> Then, this execution satisfies reorg resilience.

The paper's induction on slots `s ≥ t`, for an honest (pivot-slot) proposal `B`
of slot `t`:

* **Base case** `s = t`: Lemma 1 applies — all honest voters of slot `t` vote
  for `B`, which is in particular (exactly) their canonical chain at the voting
  round (`lemma1_canonical`).
* **Inductive step**: if `B` is canonical for every honest voter of slot `s`,
  then by the voting rule they all vote for descendants of `B`, and
  Proposition 1 carries `B` into the canonical chains at both fork-choice
  rounds of slot `s + 1`.

Validators only update their canonical chain at the rounds `{3∆s, 3∆s + ∆}`, so
the statement over those rounds is reorg resilience (`ReorgResilient`).
-/

namespace RLMDGhost

variable {Block Validator View : Type*} [BlockTree Block] [SemilatticeSup View]
  {E : Execution Block Validator View}

/-- **Theorem 1 (Reorg resilience).** An execution of a propose-vote-merge
protocol in which Proposition 1 (`Persistence`) holds satisfies reorg
resilience. The base case of the induction is Lemma 1 — all honest voters of a
pivot slot vote for the proposal — fed into the shared `canonical_from_base`. -/
theorem theorem1 (S : Spec E) (hP : Persistence E) : ReorgResilient E :=
  fun _t hpivot =>
    Persistence.canonical_from_base hP S
      (fun _v hv => Execution.votesForDescendant.of_votesFor (lemma1 S hpivot hv))

end RLMDGhost
