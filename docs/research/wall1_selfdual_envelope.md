# Graph-lattice decoding after a worst-case reduction

For an iid uniform matrix with **511 secret coordinates**, at most 512 sample rows, modulus 3329 and independent CBD(3) secret and noise, the following widths suffice. A width is the largest horizontal oracle rank. The disjoint-subset rows use one fixed secret across the entire experiment and return one answer.

| Certificate | Width for success ≥ 1/2 | Width for success ≥ 1% |
|---|---:|---:|
| All 512 rows, overlapping exact BKZ, Babai prefix and terminal CVP | 1000 | 999 |
| Choose the row count, require a nonempty Babai prefix, same profile test | 734 (224 rows) | 726 (216 rows) |
| One reduced prefix line, energy-averaged Hermite bound | 732 (222 rows) | 725 (215 rows) |
| Same reduced line, disjoint subsets and validation | 731 (2 × 221 rows) | 724 (2 × 214 rows) |
| Choose the row count, allow the empty prefix, same profile test | 716 (205 rows) | 709 (198 rows) |
| Full-block CVP, exact first moment for the half-minimum condition | 715 (204 rows) | 708 (197 rows) |
| Same half-minimum count, disjoint subsets and validation | 714 (2 × 203 rows) | 707 (2 × 196 rows) |
| Full-block CVP, translated-ball first moment | 639 (128 rows) | 633 (122 rows) |
| Same translated-ball count, disjoint subsets and validation | **638 (4 × 127 rows)** | **632 (4 × 121 rows)** |

At width **638** the success lower bound exceeds **0.64316**, including the cost in probability of selecting a single answer using four held-out rows. A finite running-time upper bound for bounded enumeration is **less than $2^{1298}$ elementary word operations**. The corresponding width-632 bounds are **0.01898** and **$2^{1249}$**. For one prescribed subset the width-639 bounds are **0.61472** and **$2^{1304}$**. These are upper bounds on the minimum sufficient width and on work. Each table entry minimizes the certificate specified in its row. The minimum over all possible reduction predicates, decoders, proofs, or subset schedules remains open. The two smallest widths use an empty Babai prefix on each retained graph. They also admit an exact coordinate-prefix lift on the original 512-row graph. This is a statement about the iid graph ensemble above. [R102 and audit](wall1_worstcase_decoding.md)

## Raw graph events and a basis-uniform profile

Use $m$ prescribed rows, $d=511+m$, $D=q^m$, and the graph $L=\{(x,y):x=Ay\bmod q\}\subset\mathbb Z^d$. The basis with columns $(qI,0)$, $(A,I)$ has determinant $D$ for every design. With target $(b_{\rm obs},0)$ and planted point $(b_{\rm obs}-e,s)$, the displacement is $X=(e,-s)$. Conditional on the design and independent preprocessing coins its $d$ coordinates still have product CBD(3) law.

For $R<q$, each nonzero possible graph vector in the ball has nonzero secret residue, hence membership probability $1/D$. Counting opposite vectors together gives the bound $(N_d(R^2)-1)/(2D)$, where $N_d(t)$ counts integer points of squared norm at most $t$. The scaled dual $qL^*$ consists of $(u,v)$ with $v=-A^\mathsf Tu\bmod q$. The same count applies with exponent 511 in place of $m$. A union bound combines the two estimates.

For the simultaneous profile computation set the exit allowance to $1/200$ per side. For an exponent $a$ equal to $m$ or 511 put
$$
 t=\pi e q^{-2a/d},\qquad z=e^{-\pi^2/t},\qquad H=\sqrt{\pi/t}\,(1+2z/(1-z)).
$$
The upper bound $e^{tR^2}H^d/(2q^a)$ follows by Gaussian majorization and the one-dimensional Poisson formula. Use the radius squared $(a\log q-\log 100-d\log H)/t$, clipped above at $(q-1)^2$, or the deterministic integer minimum 1 when the expression is at most 1. Denote the resulting primal floor by $r$, and the **unscaled** dual floor by $a_*$ after dividing the second radius by $q$. Joint probability is at least 0.99. The numerical implementation rounds logarithmic floors down.

For a primitive rank-$j$ sublattice let $M_j$ be a lower bound on its covolume, valid for all such sublattices. With $C_j=(j/2)\log\bar\gamma_j$, $C_0=C_1=0$, use
$$
 \log M_j=\max\{j\log r-C_j,\quad
      \log D+(d-j)\log a_*-C_{d-j},\quad (j-511)_+\log q\}.
$$
Hermite on the sublattice gives the first term. Its complementary section of $L^*$ has determinant equal to its covolume divided by $D$, giving the second. For the third, the reduction modulo $q$ of any basis matrix has rank at most 511. All maximal minors are divisible by $q^{(j-511)_+}$ by Smith form, and at least one is nonzero.

This accepts higher-rank first moments as inputs as well. For each rank-$j$ integral sublattice of determinant at most $Y$, count it once using a canonical basis $(E;F)$. Its membership weight is zero unless $\ker_q F\subseteq\ker_q E$, and otherwise is $q^{-m\,\mathrm{rank}_q F}$. Sum the weights to bound the probability of any such witness. Bounded integral Plücker coordinates and bounded index in the saturation make the sum finite. A bound on this sum can raise $M_j$ after charging its failure probability. The numerical scan uses the three displayed terms. The earlier two-plane number concerns a transposed design and is not an input here. [Part 49](wall1_rankin_route.md) · [Part 172](wall1_transference.md)

Use the exact overlapping HKZ-block condition that at each zero-based index the head is shortest in its projected window of length at most $b$, including the last truncated windows. Write $g_i=\|b_i^*\|$. A shorter subwindow starting at that head inherits shortestness. For
$$
 P_0=0,\qquad
 P_j=\min_{2\le h\le\min(j+1,b)}
    \frac{C_h+\sum_{v=j-h+1}^{j-1}P_v}{h-1},
$$
Hermite on each subwindow and backward induction give $\log(g_i/g_{i+j})\le P_j$. In particular $g_i\ge r e^{-P_i}$. Use sharp constants in ranks 2–8, including $\gamma_5^5=8$, $\gamma_6^6=64/3$. In every rank also take the best available Blichfeldt cap, Mordell step from the preceding rank, and the Part 228 caps 56.21420, 56.79788, 57.84689, 58.89576, 60.99269 at 506, 510, 520, 530, 550. This uses the overlapping predicate throughout. A head approximation theorem for a finite self-dual BKZ tour has different hypotheses. [Part 48](wall1_null_terminal.md) · [Part 228](wall1_parameter_slack.md)

Let $W_i$ be the prefix lattice of rank $i$. Summing the ratio inequalities over all pairs across the cut gives
$$
 \log\det W_i\le U_i =
 \frac{i\log D+\sum_{h<i\le t<d}P_{t-h}}{d}.
$$
Here the lower endpoint of the sum is $h=0$. A usable profile is
$$
 G_i=\max\{r e^{-P_i}, M_{i+1} e^{-U_i}\}\le g_i.
$$
Indeed $g_i=\det W_{i+1}/\det W_i$. More importantly, **every** primitive vector in the projection perpendicular to $W_i$ lifts to a primitive rank-$(i+1)$ extension of determinant $\det W_i$ times its projected length. Thus $M_{i+1}e^{-U_i}$ bounds the actual quotient minimum from below for every selected prefix. At $i=d-b$ shortestness in the terminal block gives $\lambda_1(\pi L)=g_i$, so both terms of $G_i$ apply. This is the step that allows the random-design event to precede basis selection. Parts 205–231 concern a particular changing window and its history. Their unresolved selected-plane and long-winner probabilities are not used here. [Part 47](wall1_decoupled.md) · [Proof-gap index](../PROOF_GAP.md)

## From the profile to success

Solve terminal CVP first, then lift with Babai on the prefix. Write $k=d-b$, $w_i=b_i^*/g_i$, $\pi$ for the rank-$b$ terminal projector, and $J=\|X\|^2$. On a good design it suffices that
$$
 2\|\pi X\|<G_k,\qquad 2|\langle X,w_i\rangle|<G_i\quad(0\le i<k).
$$
Two explicit tests were scanned.

1. Require $2\sqrt J<\min_{0\le i\le k}G_i$. The probability of $J=j$ is $[z^j](10+15z+6z^4+z^9)^d/32^d$. Multiply its accepted mass by 0.99.
2. Require each prefix floor to exceed $\sqrt{12\log(1000d)}$. The conditional strip failure is then at most 0.002, using $2e^{-G_i^2/12}$ per strip. The scalar CBD moments are $\mathbb E X_i^2=3/2$ and $\mathbb E X_i^4=6$. For any fixed rank-$b$ orthogonal projector the energy has mean $3b/2$ and variance $9b/2-(3/4)\sum_i\pi_{ii}^2\le9b/2$. For a target probability $p$ as a fraction, set $u=p/0.99+0.002$. Cantelli suffices if $G_k^2/4>3b/2+\sqrt{(9b/2)u/(1-u)}$. The union bound does not require independence between lifting and terminal decoding.

| Samples | Width | Prefix rank | Primal floor | Dual floor | Terminal floor | One-shot success from test 1 |
|---:|---:|---:|---:|---:|---:|---:|
| 512 | 506 | 517 | 446.2880 | 0.133002 | 0.287619 | only zero energy is credited |
| 512 | 999 | 24 | 446.2880 | 0.133002 | 76.1497 | > 0.08260 |
| 512 | 1000 | 23 | 446.2880 | 0.133002 | 79.6707 | > 0.79229 |
| 224 | 734 | 1 | 77.2031 | 0.550428 | 66.8599 | > 0.61071 |
| 216 | 726 | 1 | 72.1574 | 0.582427 | 62.4901 | > 0.01258 |
| 205 | 716 | 0 | 65.5981 | 0.630847 | 65.5981 | > 0.51150 |
| 198 | 709 | 0 | 61.6468 | 0.664633 | 61.6468 | > 0.01227 |

Floors in the table are rounded down. At width 506, even the largest terminal floor across all 512 sample counts is below 0.879, attained at 21 rows. The full-sample terminal floor is less than 0.288 versus $\sqrt{6b}>55.10$. The latter is twice the root-mean-square projected norm, before adding any success margin. The scan covered $1\le m\le512$. It first computed optimistic floors by allowing every window length in the ratio inequalities. Adding inequalities can only decrease $P$ and $U$, hence can only increase the calculated floors. It then rechecked the minimizing pairs at the **actual** width. The script rounds logarithmic inequalities outward on a $10^{-9}$ grid and uses integer comparisons for the CBD quantiles. The minima apply to these specified tests and caps.

At both nonempty-prefix optima of the fixed 99% profile test only one prefix line is needed. There is a bounded reduction realizing the two numerical floors without computing a global BKZ fixed point. Start with the primitive line generated by $v=q e_1$ in a sample coordinate. Solve exact SVP in the projection perpendicular to $v$, lift the shortest primitive quotient vector, and subtract a nearest multiple of $v$. If the resulting lift is shorter than $v$, use it as the new primitive line and repeat. Each change strictly decreases the positive integer $\|v\|^2$. On exit the longitudinal component of the lift is at most $\|v\|/2$, so the quotient minimum is at least $\sqrt3\,\|v\|/2\ge\sqrt3\,r/2$. This proves the floors used at widths 734 and 726. The budget is at most $3329^2=11{,}082{,}241$ exact SVP calls of rank $b$, one exact CVP of rank $b$, and scalar rounding for the lift. This construction has its own stopping rule.

The same line-reduction theorem yields a stronger certificate by integrating the raw minimum at the realized energy. Conditional on $J=j$, it suffices that $\lambda_1(L)^2>16j/3$. Then both the prefix spacing and the quotient minimum exceed $2\sqrt j$. The conditional credit is
$$
 f_{16/3}(j)=\left[1-\frac{N_d(\lfloor16j/3\rfloor)-1}{2q^m}\right]_+ .
$$
The first one-half crossing for this one-line certificate is **732** with 222 samples (success $>0.54759$, preceding credit $<0.41966$). The first 1% crossing is **725** with 215 samples (success $>0.01786$, preceding credit $<0.00799$). The same geometry holds for every exact overlapping width-$(d-1)$ basis, since $P_1=\log(2/\sqrt3)$ using the sharp rank-two constant. The explicit line reduction supplies a bounded implementation of the required two inequalities.

## Empty prefix and exact integer-ball counts

Allowing $b=d$ removes all selection of a quotient. Conditional on $J=j$, define two success credits
$$
 f_4(j)=\left[1-\frac{N_d(4j)-1}{2q^m}\right]_+,
 \qquad f_1(j)=\left[1-\frac{N_d(j)-1}{q^m}\right]_+ .
$$
The first is the half-minimum proof at the actual noise energy, averaged without fixing a design exit allowance. For the second, fix the **whole** displacement $X$. A competing nonzero graph vector must lie in the closed ball about $X$ of radius $\sqrt j$. As $X$ is integral this ball contains exactly $N_d(j)$ integer points, including zero. Every possible nonzero competitor has nonzero secret residue since its norm is at most $2\sqrt j\le 6\sqrt d<q$. Its graph membership has probability $q^{-m}$; candidates inconsistent with the graph have probability zero. A union bound counts ties as failures. The shifted ball has no sign-pair discount. Averaging over $J$ gives a certificate for the same exact CVP output, at the less restrictive uniqueness condition. No embedding coordinate is involved.

| Credit | Target | First width | Samples | Credit at preceding width | Credit at crossing | Largest credited $j$ |
|---|---:|---:|---:|---:|---:|---:|
| $f_4$ | 1/2 | 715 | 204 | 0.43975 | 0.57286 | 1084 |
| $f_4$ | 1% | 708 | 197 | 0.00728 | 0.01694 | 957 |
| $f_1$ | 1/2 | 639 | 128 | 0.45761 | 0.61472 | 975 |
| $f_1$ | 1% | 633 | 122 | 0.00756 | 0.02020 | 854 |

Credits in the table are rounded down. The checker forms $N_d$ from the coefficients of $(1+2z+2z^4+2z^9+\cdots)^d$ by exact integer arithmetic. The search also rules out earlier sample counts for the stated credits. On an interval $l\le m\le h$ one can upper-bound the credit by using dimension $511+l$ for both counts and the energy law, and $q^h$ in the denominator. Padding with zeros proves monotonicity for point counts, and adjoining independent CBD coordinates proves stochastic monotonicity for energy. The remaining intervals are scanned individually. The energy cutoff is checked to reach zero credit before truncation.

### The same certificates with a prescribed Babai prefix

On the original 512-row graph, put the $k=512-m$ discarded sample axes $q e_i$ first in the basis. This is a primitive prefix, since a graph point supported on those axes has zero secret part and sample entries divisible by $q$. Its GS lengths all equal $q$. Its orthogonal quotient is **exactly** the graph of the retained rows, with determinant $q^m$. Every point of the smaller graph extends by choosing the missing sample residues. Equivalently, for the fixed prefix the determinant of a rank-$(k+1)$ extension is $q^k$ times the length of its quotient generator. The quotient first moment can therefore be applied directly to those extensions without paying for every possible rational prefix. Given a correct terminal CVP result, every prefix Babai decision is correct because $|e_i|\le3<q/2$. Thus all the full-block rows above also describe decoders with a nonempty **prescribed** prefix on the original graph. Its rectangular prefix is already HKZ in any disjoint coordinate blocks. This construction makes no global overlapping-BKZ assertion for that basis. For disjoint-subset repetitions, choose terminal ties independently of the discarded rows. The returned secret then depends only on the retained group, as required by the following calculation.

## Repetitions on the same secret

Choose $r$ disjoint groups of $m$ rows and leave $h=512-rm$ independent validation rows. The partition can be fixed or chosen independently of all data. Conditional on the actual secret the group experiments are independent. For $a\in\{1,4,16/3\}$ and secret energy $t$ put
$$
 v(t)=\sum_j\Pr(\|e\|^2=j)f_a(t+j).
$$
This lower bound holds for each secret of energy $t$. Thus the probability of at least one correct candidate is at least $\mathbb E_s[1-(1-v(\|s\|^2))^r]$. Filter candidates to the secret support and retain those whose centered residuals on the validation rows all lie in $[-3,3]$. A fixed wrong candidate in the support differs from the true secret modulo $q$, and its residual in a fresh row is uniform modulo $q$. The true candidate always passes. Returning one passing candidate, with arbitrary tie resolution, costs at most $r(7/q)^h$ in probability. The single-group certificate needs no validation charge. In the multi-group computation at least one validation row is reserved.

| Credit | Groups | Width | Held out | Single-answer success | Finite work upper bound |
|---|---:|---:|---:|---:|---:|
| $f_{16/3}$ | 2 × 221 | 731 | 70 | > 0.54453 | $2^{10079}$ word ops |
| $f_{16/3}$ | 2 × 214 | 724 | 84 | > 0.01397 | $2^{9983}$ word ops |
| $f_4$ | 2 × 203 | 714 | 106 | > 0.56192 | $2^{1338}$ word ops |
| $f_4$ | 2 × 196 | 707 | 120 | > 0.01267 | $2^{1292}$ word ops |
| $f_1$ | 4 × 127 | 638 | 4 | > 0.64316 | $2^{1298}$ word ops |
| $f_1$ | 4 × 121 | 632 | 28 | > 0.01898 | $2^{1249}$ word ops |

The script minimizes over equal-size disjoint groups, rounding $v(t)$ down to a multiple of $10^{-9}$. The union bound $r\mathbb E[v]$ screens groups that cannot reach a target with this credit. Arbitrary overlapping subsets have dependent row data even given the secret. Exponentiating the one-shot average would also miss the conditioning on secret energy.

## Cost and reproducibility

Each empty-prefix run costs one full-block CVP call. Deterministic exact CVP has a proved $\widetilde O(4^b)$ time and $\widetilde O(2^b)$ space bound. The bound suppresses polynomial factors, including the dependence on input bit length. [Micciancio and Voulgaris, deterministic Voronoi algorithm](https://eccc.weizmann.ac.il/report/2010/014/)

For a separate finite count, let $J_0$ be the largest energy credited by the relevant integer-ball test. A radius-capped exact search reports a miss for an empty ball and finds a closest point whenever the ball is nonempty. Every event credited above contains the planted point in that ball. For the triangular graph basis, there are at most $N_{511}(J_0)$ possible final-coordinate vectors. For each, its nearest sample-coordinate lift is componentwise modular centering. Scoring all of them and retaining the closest within the radius suffices. A depth-first traversal of the integer ball has at most $(511+1)N_{511}(J_0)$ nodes, since every partial vector extends by zeros. Walking the admissible next integers outwards from zero and stopping at the squared-radius limit costs at most 40 elementary operations per node, including visits to children and end tests. Computing the modular inner products and the squared distance costs at most $12d^2$ operations per leaf. Thus $64d^2 N_{511}(J_0)$ bounds a run, including recording a best vector. Charge a further $64(1+h)d$ per run for validation and selection. These are conservative unit-cost word bounds with 64-bit integer arithmetic, loads, stores, comparisons and remainder by the fixed word $q$. Data, products, norm accumulators and traversal indices fit in a word; the traversal never stores the leaf count. With one group the resulting base-two exponents rounded up are 1344 and 1298 for the two $f_4$ rows, 1304 and 1255 for the two $f_1$ rows, in the order shown. These are mathematical work bounds, with no runtime benchmark.

For the one-line reductions there is also a coarse finite price for the oracle budget. Write $H=\|v\|^2\le q^2$. Since $q\mathbb Z^d\subset L$, at least one projected coordinate vector $q e_i$ witnesses a quotient minimum at most $q$. A shortest projection therefore has a size-reduced integral lift of squared norm at most $q^2+H/4$. Counting the box $[-2q,2q]^d$ suffices for each projected SVP. Compare the integer scores $H\|z\|^2-\langle z,v\rangle^2$ of lattice witnesses with positive score. For projected CVP the planted displacement guarantees a projected distance at most $3\sqrt d$ and a residual lift of squared norm at most $9d+H/4<q^2$. The target coset intersected with $[-q,q]^d$ therefore contains a closest projected residual. Once its class is known, lifting needs one nearest-integer rounding along $v$. Each box point needs one graph congruence, two inner products and a constant number of scalar operations. The same $64d^2$ per point covers lexicographic traversal, full scoring and recording the witness, with 64-bit accumulators at these dimensions. The resulting bound is
$$
 64d^2\big[q^2(4q+1)^d+(2q+1)^d\big].
$$
For the energy-averaged one-shot optima this gives fewer than $2^{10092}$ word operations at 732 and $2^{9996}$ at 725. For the fixed 99% profile it is below $2^{10119}$ word operations at width 734 and $2^{10010}$ at width 726. These loose finite bounds price only rank-$b$ projected questions, represented in $d=b+1$ ambient coordinates. They do not price a general fixed-point BKZ tour.

Part 140 gives an explicit real-RAM sampler bound for **SVP** on integral basis inputs, with $2^{799.23}$ operations at its rank-647 instance. Part 141 gives $2^{794.98}$ word operations on its structured rank-647 input or its two structured rank-646 inputs combined. Neither prices a terminal CVP. For the nonempty-prefix construction the projected SVP calls would additionally need integral representations, their entry bounds, sampler failure budgets and a separate terminal-CVP cost to use that sampler in the end-to-end bound. For the optimal empty-prefix rows there are zero preprocessing SVP calls. The finite costs above come from bounded enumeration. [Part 140](wall1_adrs_explicit.md) · [Part 141](wall1_sampler_wordram.md) · [Part 228](wall1_parameter_slack.md)

Run the certificate checker from the repository root with `python docs/research/scripts/wall1_selfdual_envelope.py`. It needs Python 3 and mpmath. It computes counts and probability bounds without constructing a challenge or running a decoder. [Reproduction script](scripts/wall1_selfdual_envelope.py)

## Audit

**Verdict.** The width-638 certificate passes. For one iid uniform $512\times511$ design, one CBD(3) secret and independent CBD(3) errors, the lower bound for returning that secret is $0.643162094166\ldots$. Width measures the largest CVP rank. The guarantee averages over the design and planting, with the groups fixed in advance. The explicit enumeration cost also passes, but a direct exhaustive search has a smaller finite work bound at the same success target.

**Translated ball.** Fix the whole secret and the errors in one group. For an integer representative of the observed vector, subtract the planted point $(b-e,s)$ from every candidate. The target becomes $X=(e,-s)$ and the candidate differences range over $L$. The closed ball $B(X,\|X\|)$ contains zero and exactly $N_d(j)-1$ other integer points, where $j=\|X\|^2$. For each fixed difference $(u,v)$ with $v\ne0\bmod q$, each row equation $A_i v=u_i\bmod q$ has probability $1/q$ because $q$ is prime. The rows are independent. If $v=0\bmod q$, membership requires $u=0\bmod q$ too. The only such point in this ball is zero since every difference has norm at most $2\sqrt j\le6\sqrt d<q$. Thus differences with zero secret part and a nonzero sample part have membership probability zero. Charging all $N_d(j)-1$ points at $q^{-m}$ gives an upper bound on the first moment. The exact expectation would omit the impossible points. No independence among competitors or sign-pair discount enters the bound. The closed ball charges all ties.

**Shared secret and validation.** The squared-coordinate masses at $0,1,4,9$ are $(10,15,6,1)/32$. For each fixed $s$, averaging $f_1(\|s\|^2+\|e\|^2)$ over a group's errors gives $v(\|s\|^2)$. All energies above the last positive credit contribute zero with their original probability mass. Conditional on $s$, the group inputs are independent, so the chance that all groups miss is at most $(1-v(\|s\|^2))^r$. This inequality holds for every $s$ before averaging over the secret. The coordinate projection maps onto the entire retained graph and its kernel is generated by the discarded $q e_i$. Given the planted quotient point, each missing residue has a unique lift nearest the target because $|e_i|<q/2$. This lift preserves the secret even when performed after candidate selection. Keeping the terminal tie rule local to each group makes the candidates independent of the validation rows conditional on $s$.

Condition on $s$ and the candidate list. Every wrong support-filtered candidate differs from $s$ modulo $q$. Its residual in a fresh row is uniform even conditional on that row's error. It passes all $h$ rows with probability $(7/q)^h$. The true candidate passes surely. A union bound over the list pays for arbitrary selection among passing candidates, including when several groups returned the same secret.

**Independent numerical check.** The full checker exited successfully. I separately multiplied the one-coordinate shell and energy polynomials one dimension at a time, truncated after degree 1000, and summed the conditional probabilities directly using integers. For each row below, the first zero credit occurs at $J_0+1<1000$ and all later credits vanish by monotonicity. The computations agree after applying the checker's downward $10^{-9}$ grid to each conditional group credit for repeated runs. The probability columns below show decimal approximations.

| Width | Groups | $J_0$ | $\Pr(J\le J_0)$ per group | One-group credit | Combined credit before validation | Validation charge | Single-answer bound |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 638 | $4\times127$ | 954 | 0.485047113 | 0.457619015 | 0.643162094245 | $7.819824\times10^{-11}$ | 0.643162094166 |
| 632 | $4\times121$ | 835 | 0.008764798 | 0.007561756 | 0.018988940460 | $4.365348\times10^{-75}$ | 0.018988940460 |
| 639 | $1\times128$ | 975 | 0.640261373 | 0.614728335 | 0.614728334590 | 0 | 0.614728334590 |

**Finite work and exhaustive search.** In the capped search every possible secret coordinate vector is in the integer ball of squared radius $J_0$. For each vector, modular centering minimizes the sample contribution exactly. At every fixed depth, zero extension injects the visited prefixes into the full ball. Charging 40 operations per node and $12d^2$ per leaf therefore fits within $64d^2N_{511}(J_0)$. At the largest audited cutoff each secret entry has absolute value at most 31. Even an unreduced row dot product has magnitude at most $511\cdot3328\cdot31$, and centered residual squares summed over 512 rows fit in a signed 64-bit word. Using the stated validation allowance, the base-two logarithms of the work bounds are $1297.684871$, $1248.573378$, and $1303.711423$, rounded **up** in table order. This prices a radius-capped search that may report a miss outside the credited event.

The full support has $7^{511}=2^{1434.558\ldots}$ secrets. The Shannon entropy is $511H(\mathrm{CBD}(3))\approx1192.3480$ bits, using the seven masses $\binom{6}{k}/64$. Entropy alone gives no finite guess budget at 64.31% success. For a direct comparison, the secret ball of squared radius 785 has CBD mass $0.6722932266\ldots$ and $\log_2 N_{511}(785)\approx1199.218286$. These numbers follow from the same two polynomials in dimension 511. Testing its support-filtered candidates against all 512 rows gives total false-accept probability at most $N_{511}(785)(7/q)^{512}<2^{-3354}$. Under the same traversal and scoring allowance, $64(511+512)^2N_{511}(785)<2^{1226}$ word operations suffice for success above 67.22%. Thus the width-638 enumeration improves on a scan of every possible key but loses to a CBD-aware exhaustive search at matched or higher success. In fact its specified full traversal already visits $N_{511}(954)>2^{1271}$ leaves per call.

**Exact-CVP alternatives.** Aggarwal, Dadush and Stephens-Davidowitz give randomized exact Euclidean CVP in $2^{b+o(b)}$ time and space. At $b=638$, four sequential calls have leading time factor $4\cdot2^{638}=2^{640}$ and leading space factor $2^{638}$. The lower-order exponent and input costs still need concrete bounds at this rank. If the per-call failure is at most $\eta$, subtracting $4\eta$ from the geometric certificate suffices. The asymptotic theorem supplies no explicit word count for comparison to $2^{1226}$. Part 140's $2^{799.23}$ real-RAM operations and Part 141's $2^{794.98}$ word operations price exact **SVP** at their specified structured instances. Transferring either exponent to rank-638 **CVP** would require a separately costed reduction. [ADS, Corollary 5.7](https://homepages.cwi.nl/~dadush/papers/fastcvp.pdf) · [Part 140](wall1_adrs_explicit.md) · [Part 141](wall1_sampler_wordram.md)
