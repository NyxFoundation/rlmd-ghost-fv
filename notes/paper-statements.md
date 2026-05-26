# RLMD-GHOST — paper statements and proofs (reference)

> **Source.** Francesco D'Amato, Luca Zanolini — *Recent Latest Message Driven
> GHOST: Balancing Dynamic Availability With Asynchrony Resilience.*
> IEEE Computer Security Foundations Symposium (CSF) 2024.
> arXiv:2302.11326 / IACR ePrint 2023/279. Plain-language overview:
> <https://publish.obsidian.md/single-slot-finality/RLMD-GHOST>.
>
> Local PDF: `2302.11326.pdf` (27 pp, not committed — see README).
> SHA-256 `3e328cdccd6c4150a35f19e89942a97dbc0714226eb108ea9fa6fd7bd293f7fd`.
> Text extracted with **PyMuPDF 1.27.1** (MuPDF 1.27.1).
>
> This file lists every numbered statement in the paper, with each proof as it
> appears in the main body or appendices. The paper uses **flat numbering** and
> states **5 Lemmas (1–5), 1 Proposition (1), and 14 Theorems (1–14)** — 20 items
> in all. **There are no numbered Definitions, Assumptions, or Corollaries**; the
> model (generalized sleepy model), the propose-vote-merge framework, the filter
> functions, and the security/reorg/availability/asynchrony-resilience properties
> are given as unnumbered prose in §2–§5 and summarised in the Notation glossary.
>
> Algorithms 1–5 (fork-choice / filter pseudocode), figures, and the prose of
> §1–§5, §6–§7 and the appendix intros are intentionally omitted — they are
> protocol description and commentary rather than statements to formalize.
> Several results have no proof block at their statement: Proposition 1 is a
> property established per protocol (see Lemma 4); Theorem 5's proof *precedes*
> its statement (an attack construction); Theorems 6 and 7 follow from Lemma 4
> via Theorems 1–2. These are noted in place.
>
> PDF-extraction caveat — text is preserved verbatim with known artifacts: `fi`/`ff`
> ligatures render as single glyphs (`satisﬁes`, `conﬁrmation`), subscripts wrap
> at column boundaries (`ch^r_i` as `chr i`, `Ht`), and standalone page-number /
> running-header lines have been stripped. The `(line N)` references point at the
> raw PyMuPDF line numbering.

## Notation

A glossary of the recurring symbols and notions defined in §2–§5.

| Symbol | Meaning |
|---|---|
| `n` | Number of validators. |
| `H_t`, `A_t` | Honest / adversarial validators relevant at slot `t`; `H_{t-η,t-1}` etc. denote validators active in a slot range. |
| awake / asleep, active / aware | Sleepy-model participation states; an *active* validator participates after the joining protocol, an *aware* validator additionally sees all relevant messages. |
| `∆`, GST | Network-delay bound (one slot is `3∆` rounds); Global Stabilisation Time after which synchrony holds. |
| slot `t`, round `r` | A slot spans rounds `[3∆t, 3∆t+3∆)`; proposals at `3∆t`, votes at `3∆t+∆`, merge at `3∆t+2∆`. |
| Generalized sleepy model | Pass–Shi sleepy model extended with stronger corruption/sleepiness constraints; parametrised by `τ`/`η`. |
| `τ`-sleepy / `η`-sleepy, `η`-compliant | Adversary/participation regimes; `η`-compliance bounds how fast the active honest set may shrink relative to expired votes. |
| pivot slot | A slot whose honest proposer's view-merge makes all honest voters vote for the honest proposal (Lemma 1). |
| propose-vote-merge | The protocol family (propose, vote on fork-choice output, merge buffers/views) analysed abstractly in §3. |
| view-merge | Mechanism by which voters merge the proposer's view before voting, ensuring agreement on honest proposals. |
| `FC`, GHOST | Fork-choice function; `GHOST(V,t)` the greedy-heaviest-observed-subtree rule on view `V`. |
| `w(B, M)` | Weight (vote count) of the subtree rooted at block `B` among votes `M`. |
| `FIL_lmd`, `FIL_eq`, `FIL_η-exp` | View filters: latest-message-only, equivocation-discounting, and η-expiry (drop votes older than `[t−η, t)`). |
| `FIL_rlmd` | RLMD filter `FIL_lmd ∘ FIL_η-exp ∘ FIL_eq`; RLMD-GHOST `:= GHOST ∘ FIL_rlmd`. |
| `η` | Vote-expiry window length. `η = 1` ⇒ Goldfish (GHOST-Eph); `η = ∞` ⇒ LMD-GHOST; `1 < η < ∞` interpolates. |
| `ch^r_i` | The canonical chain (ledger) of validator `i` at round `r`; `⪯` is the prefix relation. |
| κ, `T_conf` | Confirmation depth / latency; the `κ`-deep confirmation rule, security with `T_conf = 2κ` slots. |
| Security (safety + liveness) | Safety: honest chains are prefix-comparable; Liveness: transactions are confirmed within `T_conf`. |
| `τ`-reorg-resilient | An honest proposal from a slot is never reorged out, in the `τ`-sleepy model. |
| `τ`-dynamically-available | Secure (safe + live) under dynamic participation in the `τ`-sleepy model. |
| `(τ, π)`-asynchrony-resilient | Remains secure despite a temporary period of asynchrony (tpa) of length `≤ π`, with `τ`-sleepiness otherwise. |
| `(η−1)`-tpa `(t1, t2)` | A temporary period of asynchrony spanning slots `(t1, t2)` of length `≤ η−1`. |
| fast confirmation | Optimistic single-slot confirmation when `≥ 2n/3` honest validators are online (Appendix B). |

The paper's results span the abstract propose-vote-merge framework (§3.6), its
GHOST instantiations LMD-GHOST (§4.2) and Goldfish (§4.3), RLMD-GHOST itself
(§5.2), tightness limitations (Appendix A), and fast confirmations (Appendix B).

## Statements

## Propose-vote-merge protocols — §3.6

### Lemma 1 — view-merge: honest voters vote for the honest proposal in a pivot slot

**Statement.** (line 625)

```
Lemma 1. Suppose that t is a pivot slot. Then, all honest voters of slot t, i.e., Ht, vote for the honest
proposal B of slot t.
```

**Proof.** (line 627)

```
Proof. Let Vp ∪{B} be the view proposed with block B by vp, the honest proposer of slot t, i.e., Vp is the
view of vp at round 3∆t. Since vp is honest, B extends FC(Vp, t), and thus FC(Vp ∪{B}, t) = B by the
consistency property (see Section 2) of FC.
Consider an honest voter of slot t, i.e., a validator vi ∈Ht, and let Vi be its view at round 3∆t + ∆,
before merging Vi with the proposed view Vp ∪{B}. Observe that, since vi is active in round 3∆t + ∆, it
must has already been awake at round 3∆(t −1) −2∆, because otherwise it would need to follow the joining
protocol until round 3∆t + 2∆, and would thus not currently be active.
Therefore, vi was already active at round 3∆(t −1) −2∆, and in particular it merged its buﬀer Bi in its
local view then. So, Vi is the view that vi had after merging the buﬀer Bi. So, messages in Vi are delivered
to the proposer by round 3∆t, so Vi ⊆Vp.
The proposal message is received by vi before voting. Then, vi merges the proposed view Vp∪{B} with its
view Vi, resulting in the view Vi ∪(Vp ∪{B}) = Vp ∪{B}. Validator vi votes for the output of its fork-choice
at round 3∆t + ∆, which is FC(Vp ∪{B}, t) = B.
```

### Lemma 2 — w.o.p. every κ-interval contains a pivot slot

**Statement.** (line 663)

```
Lemma 2. With overwhelming probability, all slot intervals of length κ contain at least a pivot slot.
```

**Proof.** (line 664)

```
Proof. By assumption of fairness of the proposal mechanism, the proposer vp of slot t is active at round 3∆t
with probability h3∆t
n
≥h0
n , for h0 > 0. Given any κ slots, the probability of none of the κ slots having an
active proposer is ≤( n−h0
n
)κ, i.e., negligible in κ. The number of slot intervals of length κ which we need to
consider is equal to the time horizon Thor over which the protocol is executed, which is polynomial in κ, so
the probability of even one occurrence of κ consecutive slots without a pivot slot is also negligible.
```

### Proposition 1 — persistence: if slot t−1 voters back B, B stays canonical at slot t

**Statement.** (line 688)

```
Proposition 1. Suppose that all honest voters of slot t −1 vote for a descendant of block B. Then, B is in
the canonical chain of all active validators in rounds {3∆t, 3∆t + ∆}. In particular, all honest voters of slot
t vote for descendants of B.
We now show that, if Proposition 1 holds for an execution, then the execution satisﬁes reorg resilience.
The idea is the following: by the view-merge property (Lemma 1), all active validators vote for honest
proposals, and Proposition 1 ensures that this keeps holding also in future slots. We prove this result in the
following theorem, which immediately implies that a protocol is τ-reorg-resilient if Proposition 1 holds for it
in the τ-sleepy model.
```

**Proof.** (stated as a property; no direct proof here — established per protocol, e.g. for RLMD-GHOST by Lemma 4, and for Goldfish-style protocols in Sec. 4)

### Theorem 1 — Reorg resilience (from Proposition 1)

**Statement.** (line 696)

```
Theorem 1 (Reorg resilience). Let us consider an execution of a propose-vote-merge protocol in which
Proposition 1 holds. Then, this execution satisﬁes reorg resilience.
```

**Proof.** (line 698)

```
Proof. Consider a honest proposal B from slot t. We prove reorg resilience by induction on the slot. Note
that validators only ever update their canonical chain at rounds {3∆s, 3∆s + ∆}, for all slots s ≥t, upon
computing the fork-choice. Therefore, the following statement holding for all s ≥t is suﬃcient for reorg
resilience, as it implies that B is canonical in all rounds ≥3∆t + ∆.
Induction hypothesis: B is canonical in the views of active validators at rounds r ∈{3∆s, 3∆s + ∆},
for a slot s ≥t and r ≥3∆t + ∆.
Base case: The proposal slot t. Lemma 1 applies and implies that all honest voters at slot t vote for B,
which is in particular canonical in their views.
Inductive step: Suppose now that the statement holds for s ≥t. In particular, all honest voters of slot s
vote for a descendant of B, because it is canonical in their view in the voting round 3∆s + ∆. Proposition 1
then implies the desired statement for s + 1.
If an execution satisﬁes reorg resilience we obtain that, by applying the same arguments as in [7], the
κ-deep conﬁrmation rule is secure in it, in the sense that the conﬁrmed chain satisﬁes Deﬁnition 4.
In
particular, τ-reorg resilience implies τ-dynamic-availability. Because of Thereom 1, we then only need to
show that Proposition 1 holds for τ-compliant executions in order to show that a protocol is τ-dynamically-
available.
```

### Theorem 2 — Dynamic availability (reorg resilience ⇒ security, Tconf = 2κ)

**Statement.** (line 715)

```
Theorem 2 (Dynamic-availability). An execution of a propose-vote-merge protocol satisfying reorg resilience
also satisﬁes security with overwhelming probability with Tconf = 2κ slots. In particular, τ-reorg-resilience
implies τ-dynamic-availability.
```

**Proof.** (line 718)

```
Proof. Theorem 1 and Lemma 2 imply security (Deﬁnition 4) with overwhelming probability, as we now
explain. For a round r, denote by slot(r) the slot to which that round belongs. We show liveness with
conﬁrmation time Tconf = 2κ slots. Consider a round r, with t = slot(r), a round r′ with t′ = slot(r′) ≥t+2κ,
and an honest validator vi active at round r′. By Lemma 2, w.o.p, there exists a pivot slot t′′ ∈[t + 1, t + κ].
By Theorem 1, the proposal B from slot t′′ is in the canonical chain of all active validators in later slots, so
in particular it is in chr′
i . Since t′′ ≤t + κ ≤t′ −κ, B is κ-deep in chr′
i , and so it is in the conﬁrmed chain
Chr′
i as well.
To show safety, let us consider any two rounds r′ ≥r, and any two honest validators vi and vj, active
at rounds r and r′, respectively. Let also t = slot(r). Lemma 2 implies that w.o.p. there is at least a pivot
slot t′ ∈[t −κ, t), and by Theorem 1 its proposal B is canonical in all active views from round 3∆t′ + ∆.
Therefore, B is in the canonical chain of vi at round r and, since it is from a slot ≥t −κ, Chr
i ⪯B. Block
B is also in the canonical chain of vj at round r′, i.e., either B ⪯Chr′
j
or Chr′
j
⪯B. In the ﬁrst case,
Chr
i ⪯B ⪯Chr′
j . In the second case, we have both Chr
i ⪯B and Chr′
j ⪯B. Therefore, Chr
i and Chr′
j cannot
be conﬂicting, it follows that either Chr
i ⪯Chr′
j or Chr′
j ⪯Chr
i .
```

## GHOST-based protocols: LMD-GHOST — §4.2

### Lemma 3 — majority of votes for a descendant of B ⇒ GHOST outputs a descendant of B

**Statement.** (line 772)

```
Lemma 3. Let V be a view in which over a majority of the votes are for a descendant of a block B. Then,
GHOST(V, t) is a descendant of B, i.e., B is in the canonical chain output by the GHOST fork-choice.
```

**Proof.** (line 774)

```
Proof. Let M be all votes in V. Consider any height less than or equal to the height of B. In any fork at
such a height, there is one branch that contains B, and thus also the whole sub-tree rooted at B. Say the
block on that branch at that height is B′, and consider any competing sibling B′′. Since over a majority of
the votes in M are for the sub-tree rooted at B, and all votes on the sub-tree rooted at B′ are not votes on
the sub-tree rooted at B′′, w(B′, M) > |M|
> w(B′′, M). Thus, B′ is selected by the GHOST fork-choice
algorithm at that height. Therefore, B ⪯GHOST(V, t).
```

### Theorem 3 — Strong reorg resilience of LMD-GHOST with view-merge

**Statement.** (line 857)

```
Theorem 3 (Strong reorg resilience). Consider an honest proposal B from a slot t in which network syn-
chrony hold and | eHt| > n
2 . Suppose that validators in eHt do not fall asleep in rounds [3∆t + ∆, 3∆t + 2∆].
Then, B is always canonical in all honest views which contain all slot t votes from eHt.
7The Ethereum protocol has (disjoint) committees of (the whole set of) validators voting in each slot, i.e., it implements
subsampling. Neither proposer boost nor view-merge can fully prevent ex-ante reorgs in that setting, leading to a protocol with
diﬀerent security guarantees than what is described here. In particular the LMD-GHOST protocol implemented in Ethereum is
not a reorg resilient protocol, even in the full participation setting.
```

**Proof.** (line 867)

```
Proof. By Lemma 1, all honest voters of slot t broadcast a vote for B at round 3∆t + ∆. Synchrony in the
subsequent ∆rounds means that all such votes are received by those same validators before they merge their
buﬀers, since by assumption they do not fall asleep. Those votes are then in all of their views by the end of
slot t and the result follows.
On the other hand LMD-GHOST is signiﬁcantly limited in its support of dynamic participation, as shown
in the following theorem. In particular, we present a scenario in which the adversary is able to cause a reorg
of a conﬁrmed block, compromising τ-safety and, consequently, τ-dynamic-availability, while never violating
τ-sleepiness. The reason why this attack is possible is due to the fact that τ-sleepiness only considers votes
from the last τ slots, but LMD-GHOST does not have vote expiry, so all votes are relevant to the fork-
choice. Since the ∞-sleepy model allows only an extremely restrictive form of dynamic participation, almost
equivalent to requiring | eHt| > n
2 at all times, this is a fairly strong limitative result.
```

### Theorem 4 — LMD-GHOST is not τ-dynamically-available for any finite τ

**Statement.** (line 879)

```
Theorem 4. LMD-GHOST is not τ-dynamically-available for any ﬁnite τ and any conﬁrmation rule with
ﬁnite conﬁrmation time Tconf.
```

**Proof.** (line 881)

```
Proof. For some τ < ∞and a conﬁrmation rule with conﬁrmation time Tconf, we show that τ-safety and
τ-liveness are in conﬂict for LMD-GHOST. We look at a speciﬁc execution, which we assume satisﬁes liveness,
and show that it does not satisfy safety. Moreover, we show that such execution is τ-compliant. Therefore,
there are τ-compliant executions in which either liveness or safety is not satisﬁed, and consequently LMD-
GHOST is not τ-dynamically-available.
Without loss of generality, we ﬁx a ﬁnite τ ≥Tconf (we do not need to consider τ < Tconf since τ1-dynamic-
availability implies τ2-dynamic-availability for τ1 ≤τ2). We consider a validator set of size n = 2m + 1,
partitioned in three sets, V1, V2, and V3, with V1 = {v1}, |V2| = m + 1, |V3| = m −1. Validators in V2 and V3
are all initially honest, while v1 is adversarial. Let t −1 and t be two adversarial slots, i.e., controlled by v1.
In slot t, validator v1 publishes conﬂicting blocks A and B, one as a proposal for slot t −1 and the other for
slot t. By round 3∆t + ∆, the adversary delivers only A to validators in V2, and only B to validators in V3,
so that the former vote for A and the latter for B in slot t8. At this point, the adversary puts all validators
in V3 to sleep, and then does nothing for N ≫τ slots, i.e., until slot t + N. Meanwhile, validators in V2 keep
voting for A, since V2 contains m+1 > n
2 validators, so A stays canonical in all of the views of every member
of V2. Since τ ≥Tconf, this execution satisfying liveness implies that some honest proposal made after slot t is
conﬁrmed in this period, and thus that block A is conﬁrmed, since all honest proposals made in this period are
descendants of A. For any slot s ∈[0, t+1], we have that |Hs−1| = |V2 ∪V3| = 2m, so τ-sleepiness is satisﬁed.
For s ∈[t + 2, t + τ], we have that |Hs−1| = |V2| = m + 1 > m = |V1 ∪V3| = |As ∪(Hs−τ,s−2 \ Hs−1)|,
so τ-sleepiness is also satisﬁed. For s ∈[t + τ + 1, t + N −1], the ﬁrst two terms are unchanged, while
Hs−τ,s−2 \Hs = ∅, because the last vote broadcast by the validators in |V3| is from slot t < s−τ. τ-sleepiness
is then still satisﬁed. At slot t + N, the adversary corrupts a single validator v2 ∈V2, and starts voting for
B with both v1 and v2. Now, B has m + 1 votes, and descendants of A only m, so B becomes canonical
and stay so. After Tconf slots, it is conﬁrmed by all validators in V2, meaning we have a safety violation.
The adversary does not perform any more corruptions nor puts to sleep any more validators, and does not
wake up validators in V3. Therefore, for all slots s ≥t + N, we have As = {v1, v2}, V2 \ {v2} ⊆Hs−1
and Hs−τ,s−2 \ Hs−1 = ∅. τ-sleepiness is then satisﬁed, because |Hs−1| ≥m > 2 = |As ∪Hs−τ,s−2 \ Hs|.
Therefore, the executions is τ-compliant, and thus the protocol does not satisfy τ-security.
```

## Goldfish — §4.3

### Theorem 5 — Goldfish is not (τ,π)-asynchrony-resilient for any τ > π ≥ 2

**Statement.** (line 973)

```
Theorem 5. Goldﬁsh is not (τ, π)-asynchrony-resilient for any τ > π ≥2.
```

**Proof.** (the proof precedes the statement — see the (inf, 2)-compliant attack construction in Sec. 4.3 concluding at ll. 970-972)

## RLMD-GHOST properties — §5.2

### Lemma 4 — Proposition 1 holds for RLMD-GHOST in η-compliant executions

**Statement.** (line 1025)

```
Lemma 4. Proposition 1 holds for RLMD-GHOST in η-compliant executions.
```

**Proof.** (line 1026)

```
Proof. Let V be the view of an active validator at a round ∈{3∆t, 3∆t + ∆}. By the synchrony assumption,
and since the buﬀer is merged at round 3∆(t −1) + 2∆, all honest votes from slot t −1 are in V and, by
assumption, they are for descendants of B. The only votes to consider in order to decide whether B is
canonical in V are those from slots ∈[t −η, t −1], because votes from slots prior to t −η are expired at slot t.
Votes that are not for descendants of B might be those from adversarial validators in At, or from validators
in Ht−η,t−2 \ Ht−1, i.e., those that have voted in at least some slot ∈[t −η, t −2], but did not vote in slot
s −1. Observe that Ht−1 ∩At might not be empty; there might be validators that were active in slot t −1
but were (shortly after) corrupted. Therefore, V might contain more than one vote from slot t −1 from some
of these validators.
Let E ⊂Ht−1 ∩At be the set of validators in Ht−1 ∩At for which V contains more than one vote
from slot t −1. Due to equivocation discounting, votes from validators in E will not count. Observe that
the number of votes that are not for descendants of B and that are counted in V is upper bounded by
|(At \ E)∪(Ht−η,t−2 \ Ht−1)| = |(At ∪(Ht−η,t−2 \ Ht−1))\ E| = |At ∪(Ht−η,t−2 \ Ht−1)|−|E|, where the ﬁrst
equality follows from E ⊂Ht−1. Since V contains votes for descendants of B for all validators in Ht−1, the
number of votes for descendants of B and that are counted in V is lower bounded by |Ht−1\E| = |Ht−1|−|E|.
Since this is an η-compliant execution, η-sleepiness holds, i.e., |Ht−1| > |At ∪(Ht−η,t−2 \ Ht−1|), so B is
canonical in V.
As shown in Section 3, since Proposition 1 holds for RLMD-GHOST in η-compliant executions, the next
two theorems follow. Observe that, by the hierarchy of sleepy models (see Section 2), the following results
are also satisﬁed for τ ≥η. In Appendix A, we show that these results are tight.
```

### Theorem 6 — RLMD-GHOST is η-reorg-resilient

**Statement.** (line 1048)

```
Theorem 6 (Reorg resilience). RLMD-GHOST is η-reorg-resilient.
```

**Proof.** (follows from Lemma 4 via Theorem 1; no separate proof — see ll. 1045-1047)

### Theorem 7 — RLMD-GHOST is η-dynamically-available

**Statement.** (line 1049)

```
Theorem 7 (Dynamic availability). RLMD-GHOST is η-dynamically-available.
```

**Proof.** (follows from Lemma 4 via Theorem 2; no separate proof — see ll. 1045-1047)

### Theorem 8 — RLMD-GHOST is (η, η−1)-asynchrony-resilient

**Statement.** (line 1050)

```
Theorem 8 (Asynchrony resilience). RLMD-GHOST is (η, η −1)-asynchrony-resilient.
```

**Proof.** (line 1051)

```
Proof. Consider an (η, η −1)-compliant execution, with a (η −1)-tpa (t1, t2), and an honest proposal B from
a slot t ≤t1 after GST + ∆. First, since synchrony holds for slots [t, t1], and thus network synchrony holds
until round 3∆t1 + 2∆, all the properties of RLMD-GHOST hold until then, including reorg resilience. In
particular, starting from round ≥3∆t + ∆, B is in the canonical chain of all active validators in those slots,
as they coincide with the aware validators. We then only need to consider aware validators at slots s > t1.
Suppose B is in the canonical chain of all aware validators at all slots < s. In particular, B ⪯chr
i for a
validator vi ∈Ht1 which is active at a round r ∈[3∆t1 + ∆, 3∆(s −1) + ∆], because validators in Ht1 are
always aware when active. Therefore, validators in Ht1 \ As only ever broadcast votes for descendants of B
in slots [t1, s −1].
Consider ﬁrst the case s ∈(t1, t2]. Then, the aware validators at a round r ∈{3∆s, 3∆s + ∆} are exactly
the validators Ht1 which are active in r. Consider then such a validator vi ∈Ht1, and its view Vi at round
r. View Vi contains all honest votes from slot t1 because, by deﬁnition of (η −1)-tpa, vi was awake at round
3∆t1 + 2∆, at which point it received all honest votes from slot t1 and merged them into its view. Such votes
are not expired at slot s, since t2 −t1 ≤η −1 implies t1 > t2 −η ≥s −η, i.e., t1 is within the expiry period
[s −η, s −1] for slot s. All validators in Ht1 \ As are not equivocators in Vi, since they are not corrupted by
round 3∆s + ∆. Therefore, their latest votes in Vi all count for a descendant of B in Vi. The other votes
which are counted in Vi are those from As and Hs−η,s−1 \ Ht1. Since the execution is (η, η −1)-compliant,
we have |Ht1 \ As| > |As ∪(Hs−η,s−1 \ Ht1)|, and thus B is canonical in Vi.
Consider now the case s = t2 + 1. Now, aware views coincide with active views, so we let Vj be the view
of an active validator vj at a round r ∈{3∆(t2 + 1), 3∆(t2 + 1) + ∆}. Since synchrony holds from slot t2,
view Vj contains all latest votes from Ht1 \ At2+1, which are all from slots [t1, t2], and thus for descendants
of B by assumption. Moreover, t1 ≥t2 −(η −1) = (t2 + 1) −η, so all such votes are not expired at slot
t2 + 1. We can again conclude that B is canonical in Vj, because |Ht1| > |As ∪(Hs−η,s−1 \ Ht1)| holds for
s = t2 + 1 as well.
Finally, suppose s > t2 + 1. Since aware and active views coincide at slot s −1, B is canonical in all
active views at slot s −1 by assumption, so all honest votes from slot s −1 are for a descendant of B. Since
synchrony holds as well, we can apply 1 and conclude that B is canonical at all active views at slot s.
For RLMD-GHOST with η ≤2, Theorem 8 does not say anything, because a π-tpa is empty for π ≤1.
For η = 1, this is entirely to be expected, given the limitations of Goldﬁsh in this sense.
```

## Limitations of RLMD-GHOST (tightness) — Appendix A

### Theorem 9 — not τ-reorg-resilient for any 1 ≤ τ < η

**Statement.** (line 1284)

```
Theorem 9. RLMD-GHOST is not τ-reorg-resilient for any 1 ≤τ < η.
```

**Proof.** (line 1285)

```
Proof. We prove this theorem with an example. Let us consider a validator set of size n = 2m+1, partitioned
in three sets, V1, V2, and V3, with V1 = {v1}, |V2| = m + 1, |V3| = m −1. Validators in V2 and V3 are all
initially honest, while v1 is adversarial. Let t −1 and t be two adversarial slots, i.e., controlled by v1. In slot
t, validator v1 publishes conﬂicting blocks A and B, one as a proposal for slot t −1 and the other for slot
t. By round 3∆t + ∆, the adversary delivers only A to validators in V2, and only B to validators in V3, so
that the former vote for A and the latter for B in slot t. At this point, the adversary puts all validators in
V3 to sleep, and then does nothing until slot t + η −1. Meanwhile, validators in V2 keep voting for A, since
V2 contains m + 1 > n
2 validators, so A stays canonical in all of the views of every member of V2. Suppose in
particular that the proposer of slot t + 1 is in V2, so that it makes a proposal C extending A. We now show
that the adversary can induce a reorg of C, exploiting the votes of the asleep validators V3, so that reorg
resilience is not satisﬁed in this execution. We then only have to show that the execution is τ-compliant, in
order to show that the protocol is not τ-reorg-resilient.
At the voting round 3∆(t + η −1) + ∆, the adversary votes for B with v1. After the voting round,
it corrupts two validators v2, v3 ∈V2, and starts voting for B with them, broadcasting late votes for slot
t + η −1. These votes are delivered to all awake validators by round 3∆(t + η −1) + 2∆, and are therefore
in all of their views at the voting round of slot t + η. The votes of v2 and v3 are equivocations, so they are
discounted, both for B and for A. Slot t is in [t, t + η), the expiration period for slot t + η, so the votes of
V3 count at this slot. Therefore, in all views of the remaining honest validators in V2, B has m votes, i.e.,
those of V3 and v1, and descendants of A only m −1, because two have been discounted. B is then canonical
in such views, and reorg resilience (of C) is violated. The adversary does not perform any more corruptions
nor puts to sleep any more validators, and does not wake up validators in V3.
We now show that this execution is τ-compliant. For any slot s, we show that τ-sleepiness holds at slot s,
i.e., that Equation 1 holds. For any slot s ≤t + 1, this is clear, because we have |Hs−1| = |V2 ∪V3| = 2m >
1 = |V1| = |As∪(Hs−τ,s−2\Hs−1)|. For any slot s ∈[t+2, t+η−1], we have Hs−1 = V2 and As = V1, because
the two corruptions only happen after round 3∆(t + η −1) + ∆. Therefore, |Hs−1| = |V2| = m + 1 > m =
|V1∪V3| ≥|As∪(Hs−τ,s−2\Hs−1)|, so τ-sleepiness is satisﬁed. For any slot s ≥t+η, we have As = {v1, v2, v3},
V2\{v2, v3} ⊆Hs−1 and Hs−τ,s−2\Hs−1 = ∅, because η > τ implies s−τ ≥t+η−τ > t, so V3∩Hs−τ,s−2 = ∅.
τ-sleepiness is then satisﬁed, because |Hs−1| ≥m−1 > 3 = |As| = |As∪Hs−τ,s−2\Hs−1|. Since the execution
is τ-compliant, but does not satisfy reorg resilience, the protocol is not τ-reorg-resilient.
The second limitative result we present concerns dynamic availability. Unsurprisingly, an expiry period
η > τ means that RLMD-GHOST is also not τ-dynamically-available.
```

### Theorem 10 — not τ-dynamically-available for any 1 ≤ τ < η

**Statement.** (line 1319)

```
Theorem 10. RLMD-GHOST is not τ-dynamically-available for any 1 ≤τ < η and for any conﬁrmation
rule with Tconf < ⌊n−5
4 ⌋η = O(η · n) slots. In particular, it is not τ-dynamically available with the κ-deep
conﬁrmation rule, for κ < ⌊n−5
4 ⌋η.
```

**Proof.** (line 1324)

```
Proof. Consider a validator set of size n = 2m + 1, partitioned in three sets, C0, A0, and S0, standing for
corrupted, active, and sleepy, respectively, with C0 = {v1}, |A0| = m + 2, |S0| = m −2. Validators in A0 and
S0 are all initially honest, while v1 is adversarial. Let t −1 and t be two adversarial slots, i.e., controlled by
v1. In slot t, validator v1 publishes conﬂicting blocks A and B, one as a proposal for slot t −1 and the other
for slot t. By round 3∆t + ∆, the adversary delivers only A to validators in A0, and only B to validators in
S0, so that the former vote for A and the latter for B in slot t.
At this point, the adversary puts all validators in S0 to sleep, and then does nothing until immediately
after round 3∆(t + η −2) + ∆, i.e., the voting round of slot t + η −2, at which point it corrupts two
validators {v2, v3} ∈A0. Up until this point, all validators in A0 have kept voting for A, since |A0| =
m + 2 > n
2 validators. At slot t + η −1, the adversarial validators initially do not broadcast votes. By round
3∆(t + η −1) + 2∆, the adversary wakes up validators in S0, so that they are active in slot t + η. At slot
t + η, the adversary publishes three votes for B from slot t + η −1, from validators {v1, v2, v3}. By round
3∆(t+ η)+ ∆, it delivers these only to validators in A0. Since the expiration period [t, t+ η −1] for slot t+ η
contains t, the votes of S0 count at slot t + η. Therefore, in the views of the validators in S0 at slot t + η,
descendants of A have a total of m + 2 votes, from all validators in A0, including the newly corrupted ones,
while B only has m −2 votes from S0. Thus, A is canonical in their views, and they vote for it. The views
of the m remaining honest validators in A0 also include the three adversarial votes for B from slot t + η −1,
so descendants of A only have m votes, while B has m + 1. B then is canonical in their views, and they vote
for it. The three adversarial validators also do so, so B receives m + 3 votes and is canonical in the following
slots. After the voting round of slot t + η, the adversary then puts all but two of the m −2 validators in S0
to sleep.
In slot t+η+1, there are then m+2 active validators: the two which are still active from S0, and m which
are still honest from A0. There are also three adversarial validators and m−4 validators from S0 asleep from
the previous slot. We are therefore in the same situation as in slot t+1, except we have two more adversarial
validators (from A0) and two less asleep validators (from S0). We let C1 be the three adversarial validators,
A1 be the m + 2 active validators and S1 be the m −4 asleep validators. The adversary repeats the same
pattern. It corrupts two more validators from A1 after the voting round of slot (t + η) + (η −2) = t + 2η −2,
and at round 3∆(t + 2η −1) + 2∆wakes up all validators in S0 so that they are active by slot t + 2η. It then
votes with all of the ﬁve adversarial validators for the branch of A at slot t + 2η −1, but delivers such votes
only to validators in A1 by the voting round of slot t + 2η. Then, at slot t + 2η, the branch of A has m + 1
votes in the views of validators in A1, i.e., the adversarial votes plus the votes from the m −4 validators in
S1, which were put to sleep after voting for A at slot t + η. Therefore, it is canonical in their views and they
vote for it, and so does the adversary. On the other hand, the views of validators in S1 at that round do not
include the adversarial votes for A, and so all validators in S1 vote for B.
All but four of them are now put to sleep, so that at slot t + 2η + 1 there are m + 2 active validators,
m −6 asleep validators and ﬁve adversarial validators. We let these new sets of validators be A2, S2, C2,
respectively. Again, the adversary has reorged from one branch to the other, while only needing to corrupt
two asleep validators into two adversarial validators, and while otherwise preserving the same setup. They
can repeat this until the number of adversarial validators reaches m −1, which does not allow for two
additional corruptions. After the kth reorg, at slot t + kη + 1, there are m + 2 active validators Ak, 2k + 1
adversarial validators Ck, and m −2(k + 1) asleep validators Sk. Therefore, the adversary can repeat this
up to k ≤⌊m−2
2 ⌋= ⌊n−5
4 ⌋times. Each time they do so, they can reorg from one branch to the other after
η slots, for a total of ⌊n−5
4 ⌋η slots. By assumption, Tconf < ⌊n−5
4 ⌋η slots. If no conﬁrmation has been made
after Tconf slots, then liveness is violated. If one has been made, then the conﬁrmed block can still be reorged
by slot ⌊n−5
4 ⌋η, and the conﬂicting branch eventually conﬁrmed afterwards, violating safety.
To complete the proof, we only need to verify that τ-sleepiness is satisﬁed. For slots s ≤t, we have
|Hs−1| = 2m > 1 = |As ∪(Hs−τ,s−2 \ Hs−1)|, so it is indeed satisﬁed. Consider now some 1 ≤k ≤m−2
2 ,
and slots [t + (k −1)η + 1, t + kη]. For s ∈[t + (k −1)η + 1, t + kη −1], we have |Hs−1| ≥|Ak| = m + 2,
|As| ≤|Ck| = 2k+1 and |Hs−τ,s−2\Hs−1| = |Sk−1| = m−2k, so |Hs−1| ≥m+2 > m+1 = (2k+1)+(m−2k) ≥
|As ∪(Hs−τ,s−2 \ Hs−1)|, and τ-sleepiness at slot s is satisﬁed. For s = t + kη, we have |Hs−1| = m, because
two more validators have been corrupted, |As| = |Ck| = 2k + 1, and Hs−τ,s−2 \ Hs−1 = ∅, because τ < η
implies s −τ = t + kη −τ > t + (k −1)η, which is the last slot in which Sk−1 were active . Since 2k + 2 ≤m,
we have that 2k + 1 < m, so τ-sleepiness at slot t + kη is indeed satisﬁed. In slots after the last reorg, all
honest validators are active, and there are ≥m + 2 > n
2 of them, so τ-sleepiness is also satisﬁed.
```

### Theorem 11 — not (τ,π)-asynchrony-resilient for any τ > π ≥ max(η, ...)

**Statement.** (line 1388)

```
Theorem 11. RLMD-GHOST with ﬁnite η is not (τ, π)-asynchrony-resilient for any τ > π ≥max(η, 2), nor
for τ = π = ∞.
```

**Proof.** (line 1390)

```
Proof. We have to show that RLMD-GHOST is not asynchrony resilient for any τ > π ≥η, which we
do by showing that RLMD-GHOST is not (∞, π)-asynchrony-resilient, by constructing an (∞, η)-compliant
execution in which asynchrony-resilience does not hold. Since Eτ,π is monotonically decreasing in τ and
monotonically increasing in π, E∞,η ⊂Eτ,π for any τ > π ≥η, and similarly E∞,η ⊂E∞,∞, so the desired
result follows.
We consider a validator set {v1, v2, v3}, where all validators are honest at all times, and
consider an execution with a η-tpa (t, t + η), which is ̸= ∅since η ≥2. In particular, network synchrony does
not hold at slot t + η −1. Before round 3∆(t + η −1) + 2∆, validator v3 is asleep. It wakes up at that round,
and stays awake thereafter, so v3 ∈Hs for s ≥t + η. Both validators v1 and v2 are active at all rounds
≤3∆t + 2∆, so Hs = {v1, v2} for s ≤t. Validator v1 subsequently falls asleep, and only wakes up again in
round 3∆(t + η) + 2∆, while validator v2 is always awake. Upon waking up at round 3∆(t + η −1) + 2∆,
validator v3 does not see any message before merging the buﬀer into its view, due to asynchrony. Validator v3
is the proposer of slot t + η, and, due to the lack of messages in its view, it proposes a block B extending
Bgenesis, which conﬂicts with all previous honest proposals. Validator v3 then also votes for B at slot t + η,
while v2 does not. All three honest validators are active at round 3∆(t + η) + 2∆, so they receive these votes
and merge them into their view. The latest vote from v1 is from slot t, and is expired at slot t + η + 1.
Therefore, the only unexpired latest votes at the voting round of slot t + η + 1 are those from v2 and v3
from slot t + η. If B wins the tiebreaker, it is then canonical in the views of the three validators. All honest
proposals from slots ≤t are then not canonical in these active views, which are also aware views since we
are at a slot > t + η, so asynchrony-resilience is not satisﬁed in this execution. In order to show the desired
result, we then only need to show that the execution is (∞, η)-compliant. For slots s ̸∈(t, t + η], we have to
show that ∞-sleepiness holds. It suﬃces to show that |Hs−1| ≥2 > n
2 . For s ≤t, we have Hs−1 = {v1, v2},
while for s > t + η we have {v2, v3} ⊆Hs−1 , so this is indeed the case. For slots s ∈(t, t + η + 1], we have
Ht \ As = Ht = {v1, v2}, so the condition which needs to hold during the η-tpa is satisﬁed. Moreover, Ht are
awake at round 3∆t + 2∆, satisfying even the last condition of (∞, η)-compliance.
```

## Fast confirmations — Appendix B

### Lemma 5 — synchrony in a slot's voting window ⇒ honest votes carry

**Statement.** (line 1603)

```
Lemma 5. Suppose network synchrony holds for rounds [3∆t + ∆, 3∆t + 2∆], and that an honest validator
fast conﬁrms block B at slot t. Suppose also that, in the view of any active validator at slot t + 1, <
n
validators are seen as equivocators. Then, all honest voters of slot t + 1 vote for descendants of B.
```

**Proof.** (line 1608)

```
Proof. Upon fast conﬁrming B at round 3∆t+∆, the honest validator broadcasts B and all votes ≥2
3n votes
which are responsible for the fast conﬁrmation, so that they are in the view of all awake validators at round
3∆t + 2∆, by synchrony. Therefore, they are also in the view of all active validators at round 3∆(t + 1) + ∆.
Consider one such view V. By assumption, < n
3 validators are seen as equivocators in V, so over n
3 out of
the 2
3n votes are not discounted. Since they are from slot t, they are latest votes, and are the ones which
count for the respective validators. Therefore, w(B, FILulmd(V, t + 1).V) > n
3 . On the other hand, V contains
at most n
3 votes from slot t, conﬂicting with B and by a validator which is not seen as an equivocator in V.
Therefore, w(B′, FILulmd(V, t+1).V) ≤n
3 for any B′ conﬂicting with B, so B is canonical in V, and an active
validator with view V votes for a descendant of B.
```

### Theorem 12 — Reorg resilience of fast confirmations

**Statement.** (line 1624)

```
Theorem 12 (Reorg resilience of fast conﬁrmations). Consider an η-compliant execution of RLMD-GHOST.
A block fast conﬁrmed by an honest validator at a slot t after GST is always in the canonical chain of all
active validators at rounds ≥3∆(t + 1) + ∆.
```

**Proof.** (line 1627)

```
Proof. The proof follows that of Theorem 1, using Lemma 5 instead of Lemma 1 as the base case. The
assumption of Lemma 5 about equivocators is satisﬁed by (the new) deﬁnition of η-compliance. Proposition 1,
which we have proven for η-compliant executions of RLMD-GHOST in Lemma 4, is still used for the inductive
step.
```

### Theorem 13 — Dynamic availability with fast confirmations

**Statement.** (line 1631)

```
Theorem 13 (Dynamic availability). RLMD-GHOST with fast conﬁrmations is η-dynamically-available.
```

**Proof.** (line 1632)

```
Proof. η-liveness follows directly from Theorem 7, in particular from η-liveness of RLMD-GHOST without fast
conﬁrmations. This is because fast conﬁrmations are not needed for the conﬁrmed chain to make progress,
and so liveness of the standard conﬁrmations suﬃces. We then only need to show that it satisﬁes η-safety. If
an honest validator fast conﬁrms a block B at slot t in an η-compliant execution, then B is in the canonical
chain of all active validators at rounds ≥3∆(t + 1) + ∆, by Theorem 12. At slot t + κ, B is then in the κ-
slots-deep preﬁx of the canonical chain of all active validators and thus conﬁrmed by them with the standard
conﬁrmation rule. Therefore, a safety violation involving conﬂicting conﬁrmed chains Chr
i and Chr′
j can be
reduced to a safety violation for the standard conﬁrmation rule, for rounds r + 3∆(κ + 1) and r′ + 3∆(κ + 1).
Theorem 7 then implies the η-safety of the protocol.
```

### Theorem 14 — Liveness of fast confirmations

**Statement.** (line 1643)

```
Theorem 14 (Liveness of fast conﬁrmations). An honest proposal B from a slot t after GST + ∆in which
|Ht| ≥2
3n and network latency is ≤∆
2 is fast conﬁrmed by all active validators at round 3∆t + ∆.
```

**Proof.** (line 1647)

```
Proof. Firstly, note that validators in Ht are active in all rounds [3∆(t1) + 2∆, 3∆t + ∆], because falling
asleep at any point in those rounds would force them to go through the joining protocol again, and thus they
would not be active prior to at least round 3∆t + 2∆. Since network latency is ≤∆
2 , all validators in Ht
receive the honest proposal by round 3∆t + ∆
2 . By the view-merge property, Lemma 1, they all vote for B.
Again by the assumption on network latency, they all receive such votes by round 3∆t + ∆, at which point
they are merged into their views. Therefore, all of their views contain |Ht| ≥2
3n votes for B from slot t, and
B is fast conﬁrmed.
```
