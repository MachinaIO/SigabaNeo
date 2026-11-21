# What determinant drift controls in a sliding SVP window

At width 506 the inherited first-pass kernel gives a deterministic lower bound of **28.8095 on the terminal horizontal Gaussian-heuristic radius**. Part 103's necessary physical minimum is 27.4538. Thus a lower-tail theorem at approximately **0.953 times the block's own GH** would suffice for this numerical comparison. The missing probability estimate concerns shape. Even a perfect estimate of the drift of the determinant would leave that estimate open.

## A scalar recursion on the actual first pass

Use the precise no-lookahead, qI-first selector of [Part 108](wall1_first_tour.md). Write b for its full window width, d=b−1 for the retained horizontal rank, and G_j for the inverse j-th root of the j-dimensional unit ball volume. Assume b≤511. After the horizontal axes have been processed the retained lattice is a scaled d-dimensional cube with determinant q^d. Each of the next 512 appends has perpendicular height one. Let Z_t be the natural logarithm of the retained determinant after t graph appends, and s_t the exact SVP length on append t. Define the log shape error e_t by

$$
e_t=\log s_t-\log G_b-Z_{t-1}/b,\qquad a=d/b.
$$

The window determinant is exp(Z_{t−1}). Dividing it by the primitive selected length gives the next retained determinant. Consequently

$$
Z_T=a^T d\log q-b(1-a^T)\log G_b
       -\sum_{t=1}^T a^{T-t}e_t.
$$

This is a contracting affine recursion even with completely dependent errors. It discounts early errors but retains 28.3% / 36.3% of the initial log determinant at widths 406 / 506 after 512 appends. It describes one pass with fresh graph columns. Iterating the equation for another 512 height-one appends would describe a different experiment.

In particular if $s_t\le C\exp(Z_{t-1}/b)$ throughout, the final GH radius satisfies

$$
h_T=G_d\exp(Z_T/d)\ \ge\ G_d q^{a^T} C^{-(1-a^T)/a}.
$$

Exact SVP permits $C=\sqrt{\gamma_b}$ on every history. Using the outward caps 45.6963 and 56.2142 on the **squared** factors gives the following evaluations for q=3329 and T=512. The middle radius column is a counterfactual evaluation with every log shape error zero. All lengths are physical. [Hermite caps](wall1_hermite_caps.md) · [Necessary floor and rank convention](wall1_width_scan.md)

| Full width b | Horizontal d | GH floor from Hermite, rounded down | GH at zero errors | Necessary minimum F | F / Hermite GH floor |
|---:|---:|---:|---:|---:|---:|
|406|405|12.3365|15.505|24.5807|1.993|
|506|505|28.8095|35.178|27.4538|0.9530|

At 506 a terminal ratio of 0.954 suffices with the deterministic estimate. At 406 even the zero-error calculation would require a ratio above 1.58. Neither calculation upper-bounds the actual radius. Part 103 certifies a **minimum** of 8.088 at final rank 506 under its own reducer hypotheses. The 28.8095 here bounds a different observable for a specified first pass. Reaching F tests only a necessary condition for 99% conditional height-zero success. The other heights and the design/plant failure budget remain as in [Parts 94–103](../PROOF_GAP.md).

## Prefix bounds for tours

For an arbitrary output basis in rank N, write $x_i=\log\|b_i^*\|$ with indices starting at one. Set $k=N-d$, $S_k=\sum_{i=1}^k x_i$, and $D=\det L$. Any simultaneous upper caps $x_i\le u_i$ imply

$$
h(Q)=G_d\exp((\log D-S_k)/d)
\ge G_d\exp((\log D-\textstyle\sum_{i\le k}u_i)/d).
$$

This bound is sharp given just the caps and determinant (choose orthogonal axes attaining the caps). For a proposed terminal shape floor $R=\lambda_1(Q)/h(Q)\ge r$, the sufficient prefix budget for minimum F is $S_k\le\log D-d\log(F/(rG_d))$. Only the sum must be controlled, at the same time in the run. Previously recorded SVP outputs at individual positions need not equal final GS lengths after subsequent tours.

Li–Nguyen supply such a sum bound directly. For their exact algorithm on a 3/4-LLL input after the Theorem 2 tour threshold, specialize their **2020 manuscript** to algorithm width d, tolerance $0<\epsilon\le1$, and $k=N-d$. The resulting GH lower bound is

$$
G_d D^{1/N}(1+\epsilon)^{-\sqrt{k}/d}
\gamma_d^{-k(1+(d-2)/N)/(2(d-1))}.
$$

For N=1023, D=3329^511, d=505 or 646, Blichfeldt's cap $2\Gamma(2+d/2)^{2/d}/\pi$ gives respectively 13.416 and 44.669 in the limiting envelope as ε decreases to zero. A finite tour guarantee includes the displayed tolerance factor. The corresponding Part 103 necessary floors are 27.454 and 31.058, and its certified minima are 8.088 and 10.621. This comparison uses a horizontal width-d tour, distinct from Part 108's width-(d+1) append and project. The formula is cited in its manuscript version. [Li–Nguyen, Theorem 2](https://pure.royalholloway.ac.uk/ws/portalfiles/portal/39276060/BKZ2020.10.10.pdf) · [Part 107 and its audit](wall1_lit_random_bases.md)

There is no positive minimum floor from a prefix sum and determinant alone in d≥2. Fix the prefix, then choose tail axes $u,u^{-1}c,1,\ldots,1$ with c the required tail determinant and u arbitrarily small. Sorting the tail increasingly makes it exactly HKZ-reduced. Even simultaneous upper SVP/GH tests on overlapping windows permit ascending orthogonal axes: their minimum is their first side and is at most their geometric mean. In particular the globally sorted determinant-one example with N−1 sides u and last side $u^{1-N}$ passes these tests (at high ranks even with the GH cap), while its terminal minimum tends to zero. At small ranks use the Hermite cap or the geometric mean for this example. This concerns general lattices, with no claim about the frequency of such profiles on the graph ensemble. An absolute lower bound would follow from a lower tail-product bound **and** upper caps on all the other d−1 tail lengths, if the head is an exact terminal minimum. Alternatively the minimum is at least the smallest tail GS length, by the last nonzero coefficient argument. A product alone provides neither kind of control.

## Which drift hypothesis could be used?

For the first-pass radius a sufficient statistic is the single weighted error sum above. For example, with the pre-append history $\mathcal F_{t-1}$, suppose for a fixed $\theta>0$, weights $w_t=a^{T-t}$, and deterministic budgets $m_t,v_t$ one proves

$$
E[\exp(\theta w_t(e_t-m_t))\mid\mathcal F_{t-1}]
\le \exp(\theta^2 w_t^2 v_t/2).
$$

The exponential of the cumulative centered sum minus its cumulative log budget is then a nonnegative supermartingale (multiply by the next factor and take conditional expectation). Thus except with probability p the sum of weighted errors is at most $\sum w_tm_t+(\theta/2)\sum w_t^2v_t+\log(1/p)/\theta$. A stopped version may charge the probability of exiting a specified good set of marked histories separately. A mean bound alone cannot justify this concentration step. One could instead integrate the exponential of the weighted sum directly under the finite transition kernel and use Markov, allowing rare histories large conditional costs.

Part 108 gives a genuine conditional input to this calculation: at each graph append the conditional moment is exactly the average over the marked finite subgroup of the exponential involving the SVP length of that displaced window. This identity and the Hermite ceiling are available today. No small conditional mean or variance around GH has been established for typical inherited states. Part 105 concerns removal of a shortest vector in a Haar parent. It does not refresh the appended column or supply its posterior after another tour. Part 106 rules out a selector-uniform lower shape tail. Parts 109–112 exhibit reachable bad histories, loss in repeated lift estimates, singular shape laws, and positive correlations after void conditioning. None rules out an unconditional terminal observable bound for this kernel. [Selection law](wall1_selection_law.md) · [Direct program summary](../PROOF_GAP.md)

For multiple tours a candidate theorem would first prove a tour comparison $P_{j+1}\le AP_j+c+\xi_j$ for centered log prefix determinants, with a specified nonnegative contracting operator A and boundary term c for the actual insertion/extraction rules. Iteration weights the errors by rows of powers of A. Exponential moments for those scalar projections would bound the upper envelope by the fixed point plus a transient and a stochastic allowance. HPS and Li–Nguyen justify deterministic comparisons for their respective rules. Substituting a Haar average for their Hermite parameter requires rederiving the comparison including intermediate prefix changes. A one-sided comparison allows a profile far below its fixed point, and independent upper envelopes on adjacent prefix sums cannot be subtracted to bound a GS length. Two-sided control of adjacent differences, or a separate terminal shape estimate, is essential for a GSA-like profile claim. For a constant-slope log profile with adjacent drop s, the log head/geometric-mean ratio in a full b-window is $(b-1)s/2$. Setting it equal to $\log G_b$ gives the idealized root Hermite factor $\exp(s/2)=G_b^{1/(b-1)}$. The algebra specifies a candidate bulk slope only. [HPS dynamical comparison](https://www.xpujol.net/publications/bkz.pdf) · [Li–Nguyen](https://pure.royalholloway.ac.uk/ws/portalfiles/portal/39276060/BKZ2020.10.10.pdf)

## Simulated log-volume profiles (heuristic sanity check)

I simulated the scalar first-pass profile with independent Poisson-volume draws in place of the actual selected shape errors. Each trajectory supplies log heads $\log G_b+Z_{t-1}/b+e_t$ and a final retained log volume. For 200 trajectories the second-smallest and second-largest terminal GH radii were [15.4979, 15.5057] at 406 and [35.1664, 35.1793] at 506. These order statistics measure variability **inside the toy model**. The cubic start already exposes its bias: in the first graph window a surviving horizontal axis has length q, whereas the zero-error head prediction can exceed q. The model samples no actual reduced bases or terminal minima.

```python
from math import exp, lgamma, log, pi
from random import Random

for b in (406, 506):
    d = b - 1
    logG = lambda j: lgamma(1 + j/2)/j - log(pi)/2
    rng = Random(71)
    radii = []
    for run in range(200):
        z = d * log(3329)
        for step in range(512):
            error = log(rng.expovariate(0.5))/b
            z = (d/b)*z - logG(b) - error
        radii.append(exp(logG(d) + z/d))
    print(b, sorted(radii)[1], sorted(radii)[-2])
```

For the first-pass question at 506, the most direct remaining probability target is the terminal event $R_T<0.954$ under the marked kernel, or the less restrictive joint event $R_T h_T<F$. A 1% upper bound on the latter would certify the necessary-floor comparison alone. The exact volume recurrence removes a potential source of uncertainty from this question. It supplies no bound on the probability of that event and no 99% average-case fixed-point theorem.

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

**The deterministic bound h_T ≥ 28.8095.** Here h_T is the physical GH radius of the rank-505 retained lattice after the first
pass, at b = 506. The bound holds:

* D_0 = q^d for every tie choice.
* D_t = D_{t−1}/s_t exactly.
* Hermite caps from Part 98 give s_t ≤ √γ_b·D_{t−1}^{1/b}.

The sharp caps matter. Minkowski alone gives only 22.6039.

**Outward enclosures.**

| b | h_T bound | Zero-error value | Necessary floor F |
|---:|---:|---:|---:|
| 406 | 12.3366 | 15.5046 | 24.5807 |
| 506 | 28.8095 | 35.1775 | 27.4538 |

At b = 506, 0.954·28.8095 = 27.4843 > F. The 406 statement concerns only the first-pass counterfactual: an all-zero graph
column history keeps the q-cube, so 15.505 is not a ceiling on actual outcomes.

**Minor issue.** The 506 simulation bracket should read [35.1663, 35.1794] as an outward enclosure. The simulations are a
heuristic toy model.
