# Height one in the terminal Voronoi cell

At horizontal ranks 505 and 506, a physical minimum of at least **24.66 together with a full GS floor of 9** suffices for the height-one budget of 0.0025. The same minimum alone does not imply the budget for general fixed lattices, even with the reported covolume floor. A minimum of **61.3** suffices without any profile information. These are sufficient tests at physical scale. The selected graph quotient remains unresolved.

## The CBD half-space and its theta sum

Fix the lattice and orthogonal projection independently of the plant. Write
$T(t)=\sum_{h\in H}\exp(-t\|h\|^2)$ and $S=T(1/12)-1$.
Since $Qh=h$, a height-one tie or improvement requires
$-\langle X,h\rangle\ge\|h\|^2/2$ for some nonzero $h$. Each CBD(3) coordinate is a sum of six independent fair half-signs. Its mgf is $\cosh(s/2)^6\le e^{3s^2/4}$, with variance proxy $3/2$ (also its variance). Independence bounds the linear mgf by $\exp(3s^2\|h\|^2/4)$. Taking $s=1/3$ gives $e^{-\|h\|^2/12}$ per vector, hence failure probability at most $S$. Both signs of each vector are included. Negative height one duplicates the same event. [Exact criterion](wall1_threshold.md) · [Part 97 allocation](wall1_dist_unique.md)

## Using a minimum and GS lengths together

Put $t=1/12$. For certified lower bounds $L\le\lambda_1(H)$ and $g_i\le\|b_i^*\|$, every $0<u\le t$ gives
$$
S\le e^{-(t-u)L^2}(T(u)-1)
\le e^{-(t-u)L^2}\left[\prod_{i=1}^d
\left(1+\frac{2e^{-u g_i^2}}{1-e^{-u g_i^2}}\right)-1\right].
$$
At fixed later integer coefficients, the first coefficient contributes a shifted one-dimensional Gaussian series. Poisson summation bounds it by the unshifted series since the dual Gaussian coefficients are positive. Iterate in basis order and use $n^2\ge n$ for positive integers. The exponential prefactor uses the minimum only on the nonzero terms. This formula also accepts nonuniform profiles.

* With $u=t$, a common GS floor of 12.5 suffices on its own.
* With $u=0.06$, a common floor of 9 and $L=24.66$ give $S<0.0018$. On such a profile, satisfying the height-zero necessary minimum at rank 506 already pays for height one. The same numerical test applies at rank 505 with the stated $L$.

For a minimum-only test, Poisson summation on the full lattice gives $T(u)\le(t/u)^{d/2}T(t)$ since the dual Gaussian decreases termwise when $u$ decreases. Thus $S\le c(1+S)$ for $c=e^{-(t-u)L^2}(t/u)^{d/2}$. Taking $u=d/(2L^2)<t$ at $L=61.3$ gives $S\le c/(1-c)<0.0025$ at both ranks. Alternatively, on the Part 97 cap $\|y\|^2\le1.9d$, only $\|h\|\le2\sqrt{1.9d}$ can contribute by Cauchy–Schwarz. A strict minimum above that radius eliminates the capped cost entirely. Charge the cap exception once across all heights.

## What the available data certify

At horizontal rank 506 Part 92 gives $L=7.41883519$ on its design event. Dropping the shortest head gives $L=7.41883519\sqrt3/2$ at rank 505. Part 97 gives $(\det H)^{1/d}>7.259112$ and $>7.22$, respectively. Part 95's prescribed dual completion controls 60 suffix rows. Even its deterministic literal last floor at width 506 is about $0.964$ in physical units ($0.01677121$ in normalized units). The 60 estimates do not give a full profile. The determinant fixes a product of heights and cannot substitute for individual floors in the theta product. Part 95's Haar head and Part 97's higher-height dual sums concern different hypotheses or events. [Graph minimum](wall1_qary_gap.md) · [Terminal flag](wall1_hkz_terminal.md) · [Higher heights](wall1_theta_heights.md) · [Wall 1](../PROOF_GAP.md)

Part 94's height-zero condition for 99% success implies the **necessary** minimum $\lambda_1(H)>\sqrt{1+1.2d}$, about 24.66 at rank 506. Its sufficient height-zero minimum on the Part 97 cap is instead $\lambda_1(H)>\sqrt{1+1.9d}$, about 31.03 at rank 506. The gap between two sufficient tests would not by itself show that height one adds a condition. The following example separates the necessary scalar floor from actual Voronoi success.

## A fixed-lattice counterexample to the scalar implication

Take $m=d-1$ and choose an $m$-lattice $J$ of determinant equal to the volume of the radius-25 ball with $\lambda_1(J)>25$. Such a lattice exists by Siegel's mean value theorem: at this determinant the mean number of nonzero points in the closed ball is one, and every nonempty count is at least two. Use a coordinate projection onto the first $d$ coordinates and set $H=OJ\oplus M\mathbb Z$ for an orthogonal rotation $O$ of the first $m$ axes. Choose $M>25$ large enough to exceed either geometric-mean floor. [Siegel mean value formula](https://www.math.chalmers.se/~andesod/LLdual.pdf)

To fix the rotation, average it independently of the CBD draw. At radius $r\ge26$ the fraction of directions inside the Voronoi cell of $J$ is at most $(25/r)^m$. Indeed the cones of these directions up to radius $r$ lie inside the cell by convexity, and its volume is $\det J$. For $Z=\sum_{i=1}^m X_i^2$, independence gives mean $3m/2$ and variance $15m/4$ (the fourth moment of six fair half-signs is 6). Chebyshev gives $\Pr(Z<26^2)\le(15m/4)/(3m/2-676)^2$. The rotation-averaged failure probability therefore exceeds 0.69 at both ranks. Some fixed rotation attains at least that failure probability, independently of future draws. Failure in the first factor implies failure for $H$.

Thus even the actual CBD failure can exceed budget above the 24.66 floor. This example concerns arbitrary fixed lattices and the determinant lower bound. Whether the selected q-ary quotient has enough additional shape information, or whether a proof of the stronger height-zero success event for that quotient could imply height-one success, remains open.

## Interval checks

Run this block with Python 3 and mpmath. All nonintegral inputs enter as decimal strings or interval quotients.

```python
from mpmath import iv as I

I.dps = 50
v = I.mpf
t = v(1)/12
budget = v('.0025')
for d in (505, 506):
    for u, g, L, bound in [(t, '12.5', '0', budget),
                            (v('.06'), '9', '24.66', v('.0018'))]:
        q = I.exp(-u*v(g)**2)
        product = (1 + 2*q/(1-q))**d
        assert I.exp(-(t-u)*v(L)**2)*(product-1) < bound
    L = v('61.3')
    u = d/(2*L**2)
    c = I.exp(-(t-u)*L**2)*(t/u)**(v(d)/2)
    assert 0 < u < t and c < 1 and c/(1-c) < budget
    m = d-1
    mean = v(3)*m/2
    assert mean > 676
    p = 1-(v(15)*m/4)/(mean-676)**2
    assert p*(1-(v(25)/26)**m) > v('.69')
    assert I.sqrt(1+v('1.2')*d) < 25
unit = I.exp(511*I.ln(3329)/1023)
assert v('.963') < unit*v('.01677121') < v('.965')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT. The 50-digit interval checks and the scripts of Parts 92, 94, 95 and 97 pass. The failure
upper bounds are:

| Rank | λ1 ≥ 24.66 and GS floor ≥ 9 | λ1 ≥ 61.3 alone |
|---:|---:|---:|
| 505 | 0.00172658 | 0.00185397 |
| 506 | 0.00175356 | 0.00206404 |

The counterexample's failure lower bounds are 0.70468749 at rank 505 and 0.71489329 at rank 506. At rank 505 the value 24.66 is
a separate hypothesis, since the necessary floor there is 24.637. The profile-free bound uses Poisson summation only. Height one
remains open for the selected q-ary quotient.
