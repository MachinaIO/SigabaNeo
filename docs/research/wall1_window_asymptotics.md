# A geometric window at the Gaussian-heuristic slope

Normalize the head length to one. Write $g_j=r^j=e^{-aj}$ for $0\le j<w$, $V_k=\pi^{k/2}/\Gamma(1+k/2)$, and $D_k=e^{-ak(k-1)/2}$. Balance in the specified volume convention means $V_w=D_w$. Thus
$$
 r_w=V_w^{2/[w(w-1)]},\qquad a=a_0+\varepsilon,\quad a_0=-\log r_w,\qquad
 M_k=V_k/D_k,\quad M_w=e^{w(w-1)\varepsilon/2}.
$$
This convention specifies a geometric model for the lengths. It imposes no HKZ shortest-vector constraints on the coefficients.

## The exact mean and its crossover

**Theorem 1.** For independent uniform centered size-reduction coefficients, the expected number of unoriented nonzero pairs strictly shorter than one is
$$
 E=\sum_{j=1}^{w-1} M_j\sum_{1\le m<e^{aj}}
       (1-m^2 e^{-2aj})^{j/2}.
$$
Double this for signed vectors. Uniformly along sequences $w\to\infty, 0\le\varepsilon=o(1)$,
$$
 E=(1+o(1))\tfrac12 e^{w(w-1)\varepsilon/2}.
$$
In particular balance gives a limiting half-pair in expectation. A slope excess of order $1/w^2$ changes this mean by a constant factor.

**Proof.** Fix the last nonzero index $j$ and take its coefficient $m>0$. Successively summing each earlier integer coefficient and integrating its uniform phase unfolds the horizontal ball with density $1/D_j$. This yields the displayed discrete sum, including nonprimitive vectors. The fixed-profile identity is explicit in [Part 55](wall1_volume_svp_weights.md), in the chart of [Part 46](wall1_haar_prefix_law.md).

The contribution at $j$ is between $M_{j+1}/2-M_j$ and $M_{j+1}/2$. Indeed the right-endpoint sum of the decreasing slice function differs from its integral by at most its height at zero, and integrating the slices gives a half-ball. For clarity, the following bounds justify neglecting the earlier layers even at balance. Superscript zero denotes evaluation at $a_0$. Stirling gives $wa_0=\log(w/(2\pi e))+O(\log w/w)$. For $k\le\sqrt w$, $M_k^0\le(C/\sqrt k)^k$ for an absolute constant. For $\sqrt w\le k\le 3w/4$, Stirling gives
$$
 k^{-1}\log M_k^0\le C'-\tfrac12[\log k-(k/w)\log w].
$$
The bracket is concave and at both endpoints exceeds $0.2\log w$ eventually. For $3w/4\le k<w$, $M_{k+1}^0/M_k^0=e^{ka_0}V_{k+1}/V_k\gg w^{1/4}$, by the gamma ratio. Hence the sum on this final range excluding $w$ is $O(w^{-1/4})$, since $M_w^0=1$. For every $k\le w$, $M_k/M_w\le M_k^0$. The normalized earlier layers with $j+1>K$ are consequently bounded by a summable tail tending to zero as $K\to\infty$, plus $o(1)$. Each fixed earlier slice tends to zero because $a\to0$. Finally the last layer divided by $M_w$ differs from $1/2$ by at most $M_{w-1}^0=o(1)$.

For scale, direct floating-point evaluation at $w=406$ gives $r_w\approx0.9921639701$.

| Log excess | Exact sum evaluated numerically (pairs) | Half-volume approximation |
|---:|---:|---:|
| 0 | 0.92688 | 0.50000 |
| 0.0001 | 1860.47 | 1860.04 |
| 0.0002 | 6919491.78 | 6919491.34 |

## What the best independent family computes

Fix the horizontal rank $t$ before observing the cross block. Given horizontal lattice $D$ and lower matrix $H$, enumerate primitive integer suffixes up to sign with $\|Hv\|<1$. Give each weight
$$
 p_v=\operatorname{vol}_{\mathbb R^t/D}
 (B_t(\sqrt{1-\|Hv\|^2})\bmod D)
$$
in probability normalization. These torus volumes count hits, including every translate only once. The following finite formula computes the conditional optimum for any two blocks. Sort weights $p_1\ge\cdots\ge p_L>0$, set $p_{L+1}=0$, and let $b_i$ be the rational rank of the first $i$ suffixes. Then
$$
 S_t=\sum_{i=1}^L(p_i-p_{i+1})b_i.
$$
Indeed greedy insertion when rank increases simultaneously attains all prefix rank bounds. If one elects to use at most $t$ suffixes, replace $b_i$ by $\min(b_i,t)$. Full row rank alone permits **$w-t$** suffixes, even when $t=1$.

For a deterministic best-cut linear score define $E'(w,\varepsilon)=\max_t\int S_t\,dD\,dH$, integrating the independent diagonal-block coefficient cubes with uniform probability. This integral and the rank sum are an exact expression involving only $w,\varepsilon$. For acceptance the best single-cut product certificate is instead
$$
 \min_t\int\prod_{i:b_i>b_{i-1}}(1-p_i)\,dD\,dH,\qquad b_0=0.
$$
The same greedy order optimizes the logarithmic weights. This follows from [Part 60](wall1_poisson_smallball.md). Exponentiating the negative *average* linear score is not a valid replacement for this integral (Jensen has the opposite direction). Choosing among cuts after inspecting unrevealed randomness likewise needs a fresh conditioning proof.

**Theorem 2.** The unrestricted score satisfies
$$
 \min(1,2\sqrt{1-r^2})\le E'\le\min(E,w-1).
$$
The first bound uses the first suffix unit at $t=1$. For the second, every hit in the chosen family contributes a distinct short sign pair, and each weight is at most one. The restricted best-cut cap is $\lfloor w/2\rfloor$. Thus $E'/E\to0$ whenever $w(w-1)\varepsilon/2-\log w\to+\infty$. At $w=406$, excess $0.0002$, the unrestricted ratio is below $0.00006$ using the numerical sum above. There is no uniform $\Theta(E)$ law. The rank cap alone gives no separation when $E=O(1)$.

The unrestricted linear order is sharp in a small-excess regime. Suppose $\varepsilon=o(1)$ and $w\varepsilon/\log w\to\infty$. At $t=1$ put $d=w-1$ and let $k$ count the successive minima of the suffix lattice be at most $1/2$. Every minimum is at least $r^d$ by the last nonzero coordinate. Minkowski's second theorem for the Euclidean ball gives
$$
 r^{dk}2^{-(d-k)}\le\prod_{i=1}^d\lambda_i\le 2^d e^{-ad(d+1)/2}/V_d.
$$
Since $ad\gg\log w$ and $\log V_d=O(d\log d)$, rearrangement gives $k\ge(1/2-o(1))d$. These independent short vectors can be divided to primitive ones and each has $p=1$ on the horizontal circle. Thus $E'=\Theta(w)$ there and the window fails surely. This steep regime asserts nothing about survival near the exact balance point.

## Disjoint windows and the rank-1023 obstruction

**Theorem 3 (linear-score obstruction).** For $h$ disjoint windows of ranks $w_i$ and one cut per window in rank $N$, every realization satisfies
$$
 \sum_i S_{t_i}\le\sum_i(w_i-t_i)\le N-h.
$$
With the additional list-length limit $t_i$, the cap is $\sum_i\min(t_i,w_i-t_i)\le\lfloor N/2\rfloor$. These are dimension counts regardless of the profile or any support exclusions. At $N=1023$ the caps are at most 1022 and 511. The triangular number 522753 counts all cross-coordinate slots in the full triangular array. It is not the disjoint-window suffix rank. Fixed-profile disjoint windows use independent coefficients, so their acceptance bounds may indeed be multiplied. A relaxation using only factors $e^{-S_t}$ retains at least $e^{-1022}$ of any positive reference intensity to which it alone is applied. If that intensity has log mass 34000, the resulting upper-bound expression still has log mass at least 32978.

**No corresponding obstruction holds for the exact product by counting dimensions.** A single width-two window with $r>\sqrt3/2$ close enough to that threshold has miss probability $1-2\sqrt{1-r^2}$ as close to zero as desired. At equality it vanishes. With at most 1022 factors, log suppression of 34000 requires at least one miss probability at most $e^{-34000/1022}<4\cdot10^{-15}$ in the conditional product. This necessary condition is not a certificate of such suppression after integration.

The 34000 benchmark belongs to the relaxed Part 50 witness boxes. Part 61 proves a row exponent above 227 there and then excludes those boxes entirely by packing. It supplies no lower bound of 34000 on the log mass remaining at the target radii. The obstruction compares budgets pointwise and conditionally on the size of the reference integral. It does not prove that the surviving integral is large. Width three already detects competitors at $r=.99$, although Part 69's extra overlapping-lift correction becomes prominent around $r=.92$. [Part 61](wall1_poisson_exponent.md) · [Part 69](wall1_joint_acceptance.md) · [Wall 1 frontier](../PROOF_GAP.md)

The unresolved quantity is the integral of the joint void weight against the bad-profile intensity on the surviving domain. One sufficient advance would bound the uncovered torus measure for many dependent primitive suffixes, with correlation errors small at the scale of the void probability. Pairwise independence alone gives no such estimate. Other routes include proving near-coverage for independent lists on the relevant profiles or bounding the intensity of those profiles directly. A Poisson prediction $e^{-E}$ for sign pairs remains heuristic here. Neither the first-moment asymptotic nor the geometric ansatz locates the mass of the rank-1023 integral.
