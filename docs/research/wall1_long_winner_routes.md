# Thresholds, nearest-plane witnesses and conditional moments for long winners

The small-$g$ crossing remains open. The strongest unconditional result here concerns an explicit family of witnesses on the **actual finite mark group**. For any ordering of independent projected coordinate directions, nearest-plane rounding in the corresponding saturated flag finds a witness at **any positive height** with conditional probability below **$5.38\cdot10^{-37}$** at $1.10g$, on each unresolved entry. Even exact search in the first twelve flag dimensions raises this upper bound only to **0.0100**. These are upper bounds on what these searches can witness. Other vectors in the same cosets can still make the actual winner short.

A two-threshold moment test also suffices. On draws 11–405, conditional ceilings of **0.60 above $1.05g$ and 0.15 above $1.15g$ together** give crossing probability below **$4.22\cdot10^{-14}$**. This allows the conditional probability above $1.10g$ to exceed 0.1795. Neither of the two new ceilings is established.

## 1. Threshold tradeoff on the scalar determinant path

Use $n=506, d=505, q=3329, a=d/n, Q=\log q, V_j=\pi^{j/2}/\Gamma(1+j/2)$. Set $x_i=\log g_i, X=\log 34.807, h=\sqrt{56.2142}\,V_n^{1/n}$ and $Y_i=\log(s_i/g_i)$. Then $x_1=(400Q-\log V_n)/n$, $x_{i+1}=ax_i-Y_i/n$, and $s_i\le\min(q,hg_i)$. The first 405 freezes use the same window dimension. [Part 216](wall1_small_g_frequency.md) · [Part 217](wall1_long_winner_ceiling.md)

For **every real** $1\le t\le1.15$, the following integer-valued function gives the sharp necessary count from these two caps. Write $F_b(x)=\max(x-Q/n,ax-\log(b)/n)$, with compositions acting from right to left. For an individual incoming draw $j+1$, replace 405 by $j$.
\[
 N(t)=\min\{k\in\{0,\ldots,405\}:F_h^k F_t^{405-k}(x_1)<X\}.                 \tag{1}
\]
For at most $k$ strict exceedances, monotonicity and $F_h F_t\le F_t F_h$ put the smallest terminal floor at the ordering in (1). The exchange inequality follows by comparing the four affine branches as in Part 216. Both maps send $X$ below itself, so a crossing on draws 396–406 implies at least $N(t)$ exceedances by draw 405 (extend an earlier comparison by ordinary capped steps). Equality in the scalar update is allowed in this relaxation. This also shows why the entire continuum cannot give a deterministic exclusion: the very same unrestricted cap path ends below the target, for all choices of the threshold or any mixture of them.

Here $E$ is the initial number of draws on which $t g_i\ge q$ follows from the unrestricted scalar floor. The last column rounds **down** the unique $p$ at which the ordinary binomial tail with $405-E$ trials and cutoff $N(t)$ equals $2.72513\cdot10^{-11}$. A uniform predictable ceiling at or below the displayed value suffices by sequential Bernoulli domination. The weighted test of Part 217 can give higher ceilings.

| $t$ | $N(t)$ | $E$ | Sufficient per-draw ceiling |
|---:|---:|---:|---:|
| 1.00 | 175 | 1 | .2793 |
| 1.01 | 169 | 1 | .2661 |
| 1.02 | 162 | 2 | .2517 |
| 1.03 | 156 | 3 | .2395 |
| 1.04 | 149 | 3 | .2247 |
| 1.05 | 142 | 4 | .2106 |
| 1.06 | 134 | 4 | .1941 |
| 1.07 | 127 | 5 | .1804 |
| 1.08 | 118 | 5 | .1624 |
| 1.09 | 110 | 6 | .1472 |
| 1.10 | 100 | 7 | .1285 |
| 1.11 | 91 | 7 | .1117 |
| 1.12 | 81 | 8 | .0940 |
| 1.13 | 70 | 8 | .0751 |
| 1.14 | 58 | 9 | .0557 |
| 1.15 | 46 | 9 | .0378 |

A closed form evaluates the count **between** table entries as well. Put $l=\log t$, $H_0=\log h$, $P=\lceil n(x_1+l-Q)/Q\rceil$ and $x_P'=x_1-PQ/n$. Then
\[
 C(t)=\frac{X+H_0-a^{405-P}(x_P'+l)}{H_0-l},
 \qquad N(t)=1+\left\lfloor\frac{\log C(t)}{\log a}\right\rfloor.
\]
Indeed monotonicity and the endpoint counts place the transition between $k=45$ and $k=175$. Thus there are at least 230 ordinary steps in the ordered word. Their first $P$ updates use the period (either branch agrees at a tie), and subsequent ordinary steps use the affine cap. At step 230 even $F_1^{230}(x_1)<\log(172)<Q-H_0$. All exceptional updates in the transition range are therefore affine. Expanding their composition, the crossing inequality becomes $a^k<C(t)$. The strict comparison accounts for the floor plus one even at a breakpoint.

Monotonicity gives $N(t)\le175$ and $405-E(t)\ge396$ throughout the interval. A dimension-only Poisson heuristic for the **appended** lattice gives $\exp(-t^{506}/2)$, about 0.607 at 1 and below $10^{-33}$ at 1.01. The conditional distribution here draws one mark in a fixed finite quotient. No estimate of the discrepancy for this void event follows from the dimension. The failure of some specific Gaussian and collision estimates in Part 219 does not itself imply a lower bound on the true ball-indicator variance. [Part 219](wall1_covering_ceiling.md)

## 2. Nearest-plane coverage under the two sampling laws

Let $M\subset K=P\mathbb Z^N$ have retained rank $d$, $D=\det M=V_n g^n$, $L=D^{1/d}$, and $H=K/M$. At an unresolved entry $g>32.18553$, $R=tg<q$ and $\lambda_1(M)>R$. A witness at height $k$ needs horizontal norm at most $\rho_k=\sqrt{R^2-k^2}$. Each $1\le k\le R$ acts by a permutation on $H$. All heights use the same input mark. [Part 212](wall1_integrality_bound.md) · [Part 219](wall1_covering_ceiling.md)

### Full torus and arbitrary ordered basis

Write $\ell_j$ for the Gram–Schmidt lengths of a basis of $M$. On the full Haar torus the nearest-plane residual is uniform in the orthogonal box with these side lengths. Its squared norm is $S=\sum_j\ell_j^2 U_j^2$ with independent centered unit uniforms. It is the squared length returned by rounding. True squared distance to the lattice is at most $S$. The rectangular partition is described by [Bollauf, Vaishampayan and Costa](https://arxiv.org/abs/1701.08456).

AM–GM gives $\mathbb E S\ge dL^2/12$. Throughout this range even the largest height-one radius ($t=1.15$) has $dL^2/(12\rho_1^2)>1.0667$. For a stronger, basis-independent lower-tail test set $f(z)=\int_0^1e^{-z^2u^2}\,du$. Its log derivative in $\log z$ is $1/\int_0^1e^{z^2(1-u^2)}du-1$, decreasing. Jensen at fixed $\prod\ell_j=D$ and exponential Markov therefore give, for every $z>0$,
\[
 \Pr_{\rm torus}(S\le\rho_1^2)
 \le e^{4z^2\rho_1^2/L^2}\prod_j f(z\ell_j/L)
 \le e^{4z^2\rho_1^2/L^2} f(z)^d .
\]
The ratio $\rho_1/L$ decreases with $g$ when $(tg)^2>506$. At $t=1.00,1.05,1.10,1.15$, respectively, the upper bounds are $1.96\cdot10^{-13},1.07\cdot10^{-7},0.00130,0.285$ using $z=1.12,.95,.75,.49$. These are per-height-one torus results, including after basis reordering.

### Finite subgroup and an arbitrary flag

Fix the basis flag $0=W_0\subset\cdots\subset W_d$. In the line $W_j\ominus W_{j-1}$, let $\kappa_j$ be the spacing of the projection of $K\cap W_j$. The projected spacing for $M\cap W_j$ is $\ell_j=m_j\kappa_j$, with $m_j\in\{1,q\}$ since $qK\subset M$. The number of indices with $m_j=q$ is $r=\log_q|H|\le400$ by Part 212.

Reveal the Babai residual coordinates in descending order. Given the already revealed coordinates, the next coordinate modulo $\ell_j$ is uniform on a **shifted $m_j$-point grid** of spacing $\kappa_j$. Indeed the remaining fiber is a translate of $(K\cap W_j)/(M\cap W_j)$, its map to the next line has image order $m_j$ and its kernel is the preceding flag quotient. Use a half-open cell for ties. This gives an exact sampling rule including the singleton levels. The grid phases can depend on the higher digits.

For example a phase-uniform upper bound on the conditional second moment of that digit is $\ell_j^2(1/12+1/(6m_j^2))$. It is the maximum of the shifted equally spaced square sum, attained when one point is at the cell endpoint (convexity between consecutive wraps). Bounded-difference Hoeffding with those conditional means has a positive upper-tail exponent only when the target squared radius exceeds their sum. The sum is already at least $dL^2/12>\rho_1^2$. One-sided Bernstein with the same centering faces the same sign problem. Tighter **actual phase** information could change this calculation. The Lean predicate LaterDeterminantFloor gives a lower bound on the product of GS lengths at a time index. It gives no list of the separate lengths or phases. The Hermite caps on the selected minima also do not supply such a list. [Predicate and physical floor](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledConcreteBounds.lean)

### Finite subgroup, reordered coordinate flags and an exact prefix

A **coordinate flag** below is obtained by successively taking spans of independent projected ambient unit vectors, in any order. Take bases of the saturated flag sections of $M$. Each $\kappa_j\le1$, because the new projected unit vector belongs to $K\cap W_j$ and has a nonzero projection of length at most one. Such flags exist at every entry. The following bound works conditionally on the prefix and allows the flag choice to depend on that prefix.

Allow exact closest-point search on the first $b$ dimensions after nearest-plane rounding on the remaining dimensions. Let $J=\{j>b:m_j=q\}$, $s=|J|$ and $v=r-s\le b$. At a fixed height its success probability is at most
\[
 \frac{2 V_s(\rho_k^2+\tfrac14\sum_{j\in J}\kappa_j^2)^{s/2}}
 {\prod_{j\in J}\ell_j}.                                           \tag{2}
\]
In fact (2) holds on arbitrary flags with their actual spacings. For a successful output, the centered active tail coordinates $e_j$ satisfy $\sum_{j\in J} e_j^2\le\rho_k^2$. Add independent jitters uniform on $[-\kappa_j/2,\kappa_j/2]$, then center each sum modulo $\ell_j$. Conditional on all higher finite digits and higher jitters the next active sum is uniform on its whole interval, by the shifted-grid rule. Thus the smoothed coordinates are jointly uniform on a box of volume $\prod_{j\in J}\ell_j$. Conditional instead on the entire original mark, with probability at least one half the inner product of its active residual with the jitter is nonpositive, by symmetry. On this event the new squared length is at most $\sum e_j^2+\sum\kappa_j^2/4$ since recentering can only reduce length. Integrating both statements proves (2). Exact work in the prefix cannot alter these tail coordinates. The same argument permits a prescribed alternative rounding choice at each tail level depending on the higher digits and the current digit: this changes subsequent phases, while centering the current digit can only shorten it. The choice must allow the higher digits to be generated before reading lower ones.

For a coordinate flag, $\prod_{j\in J}\ell_j\ge D/q^v$: the inactive lengths are at most 1 and each omitted active length is at most $q$. Put $A=\sqrt{(tg)^2+100}$. Summing (2) over all positive heights bounds the witnessed probability by
\[
 \max_{0\le v\le b}\frac{2tg\,q^v V_{400-v} A^{400-v}}{V_n g^n}
 \qquad(0\le b\le 12).                                             \tag{3}
\]
Indeed $s\le400-v$ and $V_s A^s$ increases for $s\le400$. One proof is $V_{s+1}/V_s\ge\sqrt{2\pi/(s+2)}$ by Cauchy–Schwarz on the gamma integral. Each term in (3) decreases with $g$, since its log derivative in $\log g$ is at most $1+400-v-n<0$. It increases with $t$. The uniform numbers below use the low endpoint $32.18553$. No independence between heights or searches is used.

| $t$ | Exact prefix dimensions $b$ | Upper probability of finding any positive-height witness |
|---:|---:|---:|
| 1.10 | 0 | $5.38\cdot10^{-37}$ |
| 1.10 | 5 | $1.05\cdot10^{-22}$ |
| 1.10 | 10 | $1.97\cdot10^{-8}$ |
| 1.10 | 12 | 0.0100 |
| 1.15 | 0 | $8.40\cdot10^{-30}$ |
| 1.15 | 10 | 0.204 |

Even taking the best result from $10^{36}$ full coordinate-flag roundings witnesses at most 0.538 of the marks at $1.10g$ by the union bound, below the required 0.8205. These estimates cover coordinate flags in any order. A general reduced-basis flag can have $\kappa_j>1$, and choosing a flag after inspecting the mark requires accounting for the family of choices. Neither (3) nor the torus estimate gives an upper bound on actual finite-subgroup coverage by exact CVP. The remaining possibility here is a different flag with controlled individual spacings in (2), or a larger exact subproblem with a distinct coverage proof.

## 3. Weighted exponential moments and mixed thresholds

Take the first ten draws unrestricted and write $x^*_{11}=F_h^{10}(x_1)$, $w_i=a^{405-i}$ for $11\le i\le405$. Define
\[
 B=n(a^{395}x^*_{11}-X)\in(45.86630,45.86632),\qquad
 W=\sum_i w_i\in(274.37217,274.37219).
\]
For a first crossing at draw $j+1$, stop the increments after draw $j$ and use zero increments in the remaining affine comparison. This preserves a comparison below $X$, since $aX<X$. Hence a crossing implies $\sum_i w_iY_i^{\rm stop}> B$. One can also stop when a prefix gate fails or continuation is impossible, for a joint bound on crossings reached before such an exit. An upper comparison using nonnegative increments can be stopped in the same way. This argument avoids replacing a weighted sum of signed increments by an unweighted sum.

If $\mathbb E[e^{\lambda Y_i}\mid\mathcal F_{i-1}]\le M$ at tested entries, $M\ge1$, concavity of $u^{w_i}$ gives a bound $M^{w_i}$ for the stopped weighted increment moment. Iteration (or the corresponding normalized nonnegative supermartingale) gives $\Pr(\text{crossing})\le e^{-\lambda B}M^W$. A conditional bound sufficient to meet the budget is therefore
\[
 M\le\exp\big((\lambda B+\log(2.72513\cdot10^{-11}))/W\big).
\]
For $\lambda=4,8,16$, admissible rounded-down values are **1.7860, 3.4857, 13.2769**. The pointwise cap $h^\lambda$ alone gives respectively **3.497, 12.229, 149.535** rounded up. In particular at $\lambda=4$ the comparison needs control of the fourth moment of the normalized length. The unrestricted scalar path shows why changing $\lambda$ alone cannot supply it. The exact missing input at an entry admits the layer-cake expression $\mathbb E[(s_i/g_i)^\lambda]=\int_0^h\lambda u^{\lambda-1}\Pr(s_i>ug_i\mid\mathcal F_{i-1})\,du$. The integrand is the common-mark void fraction from Part 216, with its horizontal test.

For a mixture let $1\le t_1<\cdots<t_m<h$, $t_{m+1}=h$, and let $p_j$ upper-bound the conditional tail at $t_j$. For every $u>0$ one has the pointwise majorant
\[
 e^{uY_i}\le t_1^u+\sum_{j=1}^m(t_{j+1}^u-t_j^u)\mathbf1_{s_i>t_jg_i}.
\]
Taking the log of the product of the resulting conditional bounds at $u=\lambda w_i$, then subtracting $\lambda B$, gives a log crossing bound. The log-length version itself is $Y_i\le\log t_1+\sum_j\log(t_{j+1}/t_j)\mathbf1_{s_i>t_jg_i}$, so the corresponding weighted sum of the nested indicators must exceed $B-W\log t_1$ on a crossing (use zero indicators after stopping). Both formulas retain the nesting within a draw. With $t_1=1.05,t_2=1.15,p_1=.60,p_2=.15,\lambda=5.7$, the per-draw moment factor is
\[
 .40(1.05)^{5.7 w_i}+.45(1.15)^{5.7 w_i}+.15 h^{5.7 w_i}.
\]
The bound is in $(4.21,4.22)\cdot10^{-14}$. This comparison needs the two tail ceilings on the still relevant tested entries, including entries where only the lower-threshold indicator could fire. A single-threshold horizontal exclusion cannot silently exempt both tests. No such pair of conditional estimates, or fourth-moment bound of 1.7860, follows from the audited inputs used here. Thus the budget of $2.72513\cdot10^{-11}$ remains outstanding for the actual crossing.

## Reproduction

Run the embedded interval verifier from the research scripts directory. It is embedded to keep the single-file delivery.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_long_winner_routes.md | python -B -)
```

```python
from math import comb, factorial
from mpmath import iv

iv.dps = 65
I, log, exp = iv.mpf, iv.ln, iv.exp
q, n, d = 3329, 506, 505
a, Q, X = I(d)/n, log(q), log(I('34.807'))
budget = I('2.72513e-11')
V = [I(1), I(2)]
for j in range(2, n+1):
    V.append(2*iv.pi*V[j-2]/j)
x1 = (400*Q-log(V[n]))/n
lh = log(I('56.2142'))/2+log(V[n])/n

def step(x, lb):
    period, hermite = x-Q/n, a*x-lb/n
    assert period < hermite or period > hermite
    return max(period, hermite)

floor = [x1]
for _ in range(405):
    floor.append(step(floor[-1], lh))
assert floor[-1] < X
ordinary = x1
for _ in range(230):
    ordinary = step(ordinary, I(0))
assert ordinary < log(172) < Q-lh
counts = [175,169,162,156,149,142,134,127,118,110,100,91,81,70,58,46]
exempt = [1,1,2,3,3,4,4,5,5,6,7,7,8,8,9,9]
basis_points = [2793,2661,2517,2395,2247,2106,1941,1804,
                1624,1472,1285,1117,940,751,557,378]
for u, (k, e, bp) in enumerate(zip(counts, exempt, basis_points)):
    lt = log(I(100+u)/100)
    assert all(x+lt > Q for x in floor[:e])
    assert all(x+lt < Q for x in floor[e:405])
    for count in (k-1, k):
        x = x1
        for i in range(405):
            x = step(x, lt if i < 405-count else lh)
        assert x > X if count < k else x < X
    periods = n*(x1+lt-Q)/Q
    assert e-1 < periods < e
    C = (X+lh-a**(405-e)*(x1-e*Q/n+lt))/(lh-lt)
    assert k-1 < log(C)/log(a) < k
    N = 405-e
    # Exact rational binomial tails versus 272513 / 10^16.
    for numerator in (bp, bp+1):
        total = sum(comb(N,j)*numerator**j*(10000-numerator)**(N-j)
                    for j in range(k,N+1))
        delta = total*10**16 - 272513*10000**N
        assert delta < 0 if numerator == bp else delta > 0
assert exp(-(I('1.01')**506)/2) < I('1e-33')
assert I('.6065') < exp(-I(1)/2) < I('.6066')

g = I('32.18553')
D = V[n]*g**n
L = D**(I(1)/d)
for t, z, cap in [('1','1.12','1.96e-13'), ('1.05','.95','1.07e-7'),
                   ('1.10','.75','.00130'), ('1.15','.49','.285')]:
    R, z = I(t)*g, I(z)
    rho2 = R**2-1
    assert R**2 > 506 and d*L**2/(12*rho2) > I('1.0667')
    # Even Taylor polynomial majorizes exp(-y) for every y >= 0.
    f_upper = sum((-z*z)**j/(factorial(j)*(2*j+1)) for j in range(21))
    assert exp(4*z*z*rho2/L**2)*f_upper**d < I(cap)
for t, b, cap in [('1.10',0,'5.38e-37'), ('1.10',5,'1.05e-22'),
                  ('1.10',10,'1.97e-8'), ('1.10',12,'.0100'),
                  ('1.15',0,'8.40e-30'), ('1.15',10,'.204')]:
    R = I(t)*g
    A = iv.sqrt(R*R+100)
    assert A*iv.sqrt(2*iv.pi/402) > 1
    for v in range(b+1):
        assert 2*R*q**v*V[400-v]*A**(400-v)/D < I(cap)

w = [a**j for j in range(395)]
W = sum(w)
B = n*(a**395*floor[10]-X)
assert I('45.86630') < B < I('45.86632')
assert I('274.37217') < W < I('274.37219')
for lam, accepted, cap in [(4,'1.7860','3.497'),(8,'3.4857','12.229'),
                           (16,'13.2769','149.535')]:
    target = exp((lam*B+log(budget))/W)
    assert I(accepted) < target < exp(lam*lh) < I(cap)
lam = I('5.7')
def mixed_factor(u):
    return (I('.40')*exp(u*log(I('1.05'))) +
            I('.45')*exp(u*log(I('1.15'))) + I('.15')*exp(u*lh))
bound = exp(sum(log(mixed_factor(lam*weight)) for weight in w)-lam*B)
assert I('4.21e-14') < bound < I('4.22e-14') < budget
print('Verified 16 count and binomial brackets, both rounding laws’ numerical bounds, and the moment certificates.')
```

## Audit

**Verdict.** All three requested claims are confirmed. The embedded interval verifier ran successfully, including all 16 count and binomial brackets.

**Threshold counts.** I independently minimized the scalar floor by dynamic programming, allowing either cap at each draw. The table gives the two terminal floors bracketing the first strict crossing of $34.807$.

| $t$ | $N(t)$ | Floor with $N(t)-1$ exceptions | Floor with $N(t)$ exceptions |
|---:|---:|---:|---:|
| 1.00 | 175 | 34.811490 | 34.796232 |
| 1.10 | 100 | 34.818595 | 34.806284 |
| 1.15 | 46 | 34.810817 | 34.799918 |

For intermediate real $t$, the exchange inequality places the exceptions last. Monotonicity in $t$ and the endpoint counts leave at least 230 ordinary steps in each schedule bracketing the transition. After the $P$ period steps, expanding the two affine runs gives the strict condition $a^k<C(t)$, including at a period-branch tie. At an integer value of $\log C(t)/\log a$, equality reaches $X$ and one more exception is necessary. An earlier crossing persists in the scalar comparison when extended by ordinary steps because $F_t(X)<X$.

**Finite-group search.** Conditional on the incoming history, each allowed height permutes the uniform mark. On a coordinate flag fixed by that history, jitter fills each active tail interval uniformly conditional on higher digits and jitters. Iterating gives uniform volume on their product. On a successful mark, symmetry keeps at least half its jitter mass within the enlarged ball of (2). Exact search in the first $b$ dimensions preserves the rounded tail. Maximizing (3) at the lower endpoint gives approximately $5.37182\cdot10^{-37}$ for $b=0$ and $0.009991740$ for $b=12$ (maximum at $v=12$). The union over heights uses the same mark throughout. The figure $0.8205$ is the coverage needed for Part 217's particular $0.1795$ ceiling on an unresolved entry. A missed mark can still contain a short representative, so the true void probability remains open.

**Moment criteria.** Keep the increment on the draw producing the first crossing. The decision to include that draw depends only on its incoming history. After crossing, zero increments propagate the comparison by $x\mapsto ax$, preserving $x<X$. With $I_i$ the predictable indicator that the draw is still tested, conditional Jensen gives $\mathbb E[\exp(4w_i I_iY_i)\mid\mathcal F_{i-1}]\le 1.7860^{w_i}$ under the stated fourth-moment hypothesis. Dividing the successive exponential products by the products of these deterministic bounds gives a nonnegative supermartingale starting at one. Terminal Markov then gives $e^{-4B}1.7860^W\approx2.69977\cdot10^{-11}$ for the crossing. The nested tail majorant at $5.7w_i$ likewise gives approximately $4.21341\cdot10^{-14}$ under the two stated ceilings. Both arguments use conditional expectations on the live histories and allow dependence across draws. For a gate-restricted hypothesis, the bounds cover crossings reached before exit.

One notation correction applies to the layer-cake identity in §3. Its left side should read $\mathbb E[(s_i/g_i)^\lambda\mid\mathcal F_{i-1}]$, matching the conditional probability in the integrand. The constants are unchanged. Establishing either sufficient hypothesis for the actual chain remains open.
