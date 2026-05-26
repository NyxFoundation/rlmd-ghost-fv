---
title: RLMD-GHOST Lean 4 Formalization Strategy
last_updated: 2026-05-26
tags:
  - lean4
  - formal-verification
  - rlmd-ghost
  - consensus
---

# RLMD-GHOST Lean 4 Formalization Strategy

This document records *how* the RLMD-GHOST consensus protocol (arXiv:2302.11326,
CSF 2024) is being formalized in Lean 4, the technical barriers we hit, and the
explicit policy decision for each. The 20 numbered statements of the paper
(Lemma 1–5, Proposition 1, Theorem 1–14) are each tracked by a GitHub issue;
this file is the cross-cutting reference those issues link back to.

The statement texts and proofs live in [`notes/paper-statements.md`](../notes/paper-statements.md)
and the per-statement segments in [`notes/_segments/`](../notes/_segments/).

RLMD-GHOST is a *propose-vote-merge* protocol parametrised by a vote-expiry
window `η`: it generalizes Goldfish (`η = 1`) and LMD-GHOST (`η = ∞`), trading
**dynamic availability** against **resilience to bounded asynchrony**. Results
are proven in the paper's **generalized sleepy model**. The analysis is largely
deterministic; the only probabilistic ingredient is the proposer-lottery fact of
Lemma 2 (a pivot slot occurs in every κ-window w.o.p.).

## Proof discipline: `sorry` vs `axiom` vs hypothesis threading

These three are **not** interchangeable. The project uses the latter two and
never the first.

| Mechanism | Meaning | Soundness | Use in this project |
|---|---|---|---|
| `sorry` | Placeholder for an omitted proof; compiles but Lean warns and every downstream proof is tainted. | ✗ Not a proof; technical debt. | **Never.** |
| `axiom` | A proposition *declared* true without proof — a deliberate, explicit assumption. | ✓ Sound relative to the assumption being a genuine idealized fact. | For idealized cryptography (signatures, proposer lottery) and for the probabilistic pivot-slot fact (Lemma 2, temporarily). |
| Hypothesis threading | An external/idealized/probabilistic fact is taken as an explicit *premise* of the theorem. | ✓ The theorem is fully proved: "premise ⇒ conclusion". | Default for all deterministic reorg / availability / asynchrony reasoning. |

A deterministic theorem takes the probabilistic conclusion of Lemma 2 (and the
crypto facts) as hypotheses and is then proved with **no `sorry` and no local
axiom**. The probabilistic fact is isolated into Lemma 2, declared as `axiom` for
now, and proved later in a dedicated Phase 2 issue.

## Barriers and decisions

### 1. Probabilistic proposer selection (Lemma 2)

Lemma 2 ("w.o.p. every κ-interval contains a pivot slot") is the single
probabilistic statement; it rests on the proposer-selection lottery and a
union/Chernoff-style bound. Reorg resilience (Theorem 1) and the GHOST
fork-choice arguments are deterministic *given* a pivot slot.

**Decision.** Thread the pivot-slot good event as a hypothesis into the
deterministic theorems (fully proved). Declare **Lemma 2** as an `axiom` (label
`needs-axiom`); it closes at **Phase 1**. The measure-theoretic proof (proposer
lottery + concentration; concentration bounds are not in core Mathlib) is tracked
in a separate **Phase 2** follow-up issue (label `phase2`) and never blocks
dependents.

### 2. Idealized cryptography

Votes are signed and the proposer of each slot is selected by a lottery
(VRF-style, with uniqueness). Equivocation discounting relies on detecting
double-votes by signature.

**Decision.** Axiomatize idealized interfaces — `SignatureUnforgeable` and the
proposer-lottery `consistency`/`uniqueness` properties — in `RLMDGhost/Axioms.lean`,
threaded into the statements that need them. Permanent assumptions (no Phase 2);
the *probabilistic* lottery bound is Barrier 1, kept separate.

### 3. The generalized sleepy model

The model distinguishes awake/asleep and active/aware validators, and is
parametrised by the `τ`-sleepy / `η`-sleepy regimes, `η`-compliance, the
`(τ, π)`-compliance used for asynchrony resilience, and the temporary period of
asynchrony `(η−1)`-tpa `(t1, t2)`. The substance of the RLMD argument (Lemma 4)
is the `η`-sleepiness inequality `|H_{t-1}| > |A_t ∪ (H_{t-η,t-2} \ H_{t-1})|`.

**Decision.** Model the sleepy environment as an abstract structure carrying the
awake/active/aware sets per round and the compliance inequalities as hypotheses.
Derive the lemmas from those hypotheses; no axiom.

### 4. Protocol mechanics: propose-vote-merge, GHOST, view filters

The notes omit Algorithms 1–5, but the statements need: the propose/vote/merge
round structure and view-merge; the GHOST fork-choice and its weight function
`w(B, M)`; and the filters `FIL_eq`, `FIL_lmd`, `FIL_η-exp`, with
`FIL_rlmd = FIL_lmd ∘ FIL_η-exp ∘ FIL_eq`.

**Decision (MVP).** Provide propose-vote-merge behaviour, the GHOST rule, and the
filter family as an **abstract interface (a structure / typeclass of
hypotheses)**, and derive the theorems from it. Lemma 3 (majority ⇒ GHOST picks a
descendant) is a self-contained combinatorial fact about `w(·,·)` proved directly.
The concrete `η = 1` / `η = ∞` specialisations (Goldfish / LMD-GHOST) instantiate
the interface.

### 5. Negative results (Theorems 4, 5, 9, 10, 11)

Five statements are **impossibility / tightness** results of the form "protocol P
is *not* X-resilient", proved by exhibiting a concrete adversarial execution.

**Decision.** Formalize each as `∃ execution ∈ <compliance class>, ¬ Property`,
constructing the explicit validator partition and message schedule from the paper
and discharging the property violation deterministically. No axiom; no Phase 2.
These do not depend on the positive results (except the tightness chain
Thm 10 ← Thm 9).

## Track structure and dependency graph

Five layers, matching the paper's organization.

- **Track A — propose-vote-merge framework (§3.6):** Lem 1, Lem 2, Prop 1,
  Thm 1, Thm 2. Abstract reorg resilience ⇒ dynamic availability.
- **Track B — GHOST instantiations & separations (§4):** Lem 3, Thm 3 (LMD-GHOST
  strong reorg resilience), Thm 4 (LMD-GHOST not dynamically-available), Thm 5
  (Goldfish not asynchrony-resilient).
- **Track C — RLMD-GHOST security (§5.2):** Lem 4, Thm 6 (η-reorg), Thm 7
  (η-dynamic-availability), Thm 8 ((η, η−1)-asynchrony-resilience).
- **Track D — tightness / limitations (App. A):** Thm 9, 10, 11.
- **Track E — fast confirmations (App. B):** Lem 5, Thm 12, 13, 14.

Dependency adjacency list (`X ← {…}`; `[prob]` is the Lemma 2 axiom of Barrier 1,
`[crypto]` the idealized-cryptography axioms of Barrier 2, `[attack]` a self-
contained adversarial construction):

```
Lem1  ← {}                       (view-merge; protocol mechanics)
Lem2  ← {[prob], [crypto]}        (axiom; pivot slot w.o.p.)
Prop1 ← {}                        (property; established per protocol — see Lem4)
Thm1  ← {Lem1, Prop1}             (reorg resilience)
Thm2  ← {Thm1, Lem2}              (dynamic availability)

Lem3  ← {}                        (GHOST weight majority; combinatorial)
Thm3  ← {Lem1, Lem3}              (LMD-GHOST strong reorg resilience)
Thm4  ← {[attack]}                (LMD-GHOST not dynamically-available)
Thm5  ← {[attack]}                (Goldfish not asynchrony-resilient)

Lem4  ← {[crypto: equiv-disc]}    (Prop1 for RLMD-GHOST, η-compliant)
Thm6  ← {Lem4, Thm1}              (η-reorg-resilient)
Thm7  ← {Lem4, Thm2}              (η-dynamically-available)
Thm8  ← {Lem4, Thm1}              ((η, η−1)-asynchrony-resilient)

Thm9  ← {[attack]}                (not τ-reorg-resilient, τ < η)
Thm10 ← {Thm9}                    (not τ-dynamically-available)
Thm11 ← {[attack]}                (not (τ,π)-asynchrony-resilient)

Lem5  ← {}                        (fast-confirmation synchrony; timing)
Thm12 ← {Lem5, Thm6}              (reorg resilience of fast confirmations)
Thm13 ← {Thm7}                    (dynamic availability with fast confirmations)
Thm14 ← {Lem5}                    (liveness of fast confirmations)
```

The graph is a **DAG** (no cyclic dependency); statements close in topological
order. Only Lemma 2 is probabilistic, so it is the sole `needs-axiom` /
`phase2` statement.

## Non-issue prerequisites (Lean scaffolding)

The following are **not** tracked by per-statement issues; they are prerequisite
scaffolding assumed by every statement issue:

| Path | Contents |
|---|---|
| `lakefile.toml`, `lean-toolchain` | Lake build config; pin a Lean toolchain and depend on Mathlib. |
| `RLMDGhost/Basic.lean` | Core types: `Validator`, `Block`/chain with prefix order `⪯`, votes/views, slots/rounds (`3∆`-slot structure), the canonical chain `ch^r_i`, the weight `w(B, M)`, and the `κ`-deep confirmation / security (`T_conf = 2κ`) notions. |
| `RLMDGhost/Model.lean` | The generalized sleepy model: awake/active/aware sets per round, `τ`-/`η`-sleepiness, `η`-compliance, `(τ, π)`-compliance, and the `(η−1)`-tpa, all as a structure of hypotheses (Barrier 3). |
| `RLMDGhost/Protocol.lean` | Abstract interface: propose-vote-merge + view-merge, the GHOST fork-choice, and the filter family `FIL_eq` / `FIL_lmd` / `FIL_η-exp` / `FIL_rlmd`, as a structure / typeclass (Barrier 4). |
| `RLMDGhost/Axioms.lean` | Declared axioms: idealized cryptography (`SignatureUnforgeable`, proposer-lottery consistency/uniqueness — Barrier 2) and the probabilistic pivot-slot good event of Lemma 2 (Barrier 1), each with a source comment. |

Reference pattern for project layout: [`Koukyosyumei/PoL`](https://github.com/Koukyosyumei/PoL)
(Apache-2.0, Lake, `Consensus/` module layout).
