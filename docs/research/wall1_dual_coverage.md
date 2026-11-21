# Dual smoothing and fresh-column coverage at rank 1023

On all twelve Part 77 boxes, **zero deep columns reach the finite Gaussian hard-coverage threshold** derived below, even with the exact smoothing parameter. For the dual-minimum bound at error $2^{-j}$, zero deep columns reach even the Gaussian root-mean-square radius. The usual exponential Gaussian-tail bound thus adds **zero nats**. Using the exact continuous Gaussian tail instead can give positive suppression, but even an optimistic allowance for it leaves more than 216866 nats at the closest target.

## The dual upper tail and its normalization

Fix a window start, write $g_0=R$ in local indices, and put $d=\det D_j=\prod_{k<j}g_k$, $r=(R^2-g_j^2)_+^{1/2}$. The fresh height-one shift is Haar on the prefix torus conditional on its basis. Other heights have smaller section radii and use multiples of the same shift. All coverage estimates below concern the height-one test. Write $\eta_\epsilon$ in the convention $\sum_{0\ne u\in D_j^*}e^{-\pi s^2\|u\|^2}\le\epsilon$.

The logarithmic Micciancio–Regev upper bound uses $\lambda_j(D_j)$. Substituting $1/\lambda_1(D_j^*)$ is unjustified. Indeed unimodular lattices exist in growing dimensions with dual minimum $\Omega(\sqrt j)$ by the Siegel mean formula applied to a ball of volume less than one. Yet Poisson summation gives $s^j\ge d/(1+\epsilon)$ at smoothing, so the proposed substitution would contradict this at fixed error. The applicable minimum-based bound is $\eta_{2^{-j}}(D_j)\le\sqrt j/\lambda_1(D_j^*)$. [Micciancio–Regev bound as stated by Peikert](https://web.eecs.umich.edu/~cpeikert/pubs/ideal_lattices.pdf)

Let $h_k=1/g_{j-1-k}$. For any threshold $\tau$, V9 and unfolding give the marginal failure bound $p_j\le\min(1,M_j)$, where
$$
M_j=\sum_{k=0}^{j-1}\sum_{1\le m<\tau/h_k}
\frac{V_k(\tau^2-m^2h_k^2)^{k/2}}{\prod_{l<k}h_l}.
$$
These count sign pairs by their last positive integer coordinate, including the deterministic line at $k=0$. In particular $\tau_j=\min_k h_k$ gives $M_j=0$ at every endpoint, hence zero total Markov failure. Increasing thresholds cannot overcome the numerical obstruction below, which already grants exact smoothing on every good history. [Dual chart](wall1_void_duality.md) · [Section formula](wall1_window_asymptotics.md)

## Two finite Gaussian tests

The Gaussian of density $s^{-j}e^{-\pi\|x\|^2/s^2}$ wraps to a density between $1-\epsilon$ and $1+\epsilon$ relative to normalized Haar, by its absolutely convergent Fourier series. A Gaussian landing above an uncovered phase has norm at least $r$. Thus with $Y\sim\chi^2_j$ and $x=2\pi r^2/s^2$ the conditional pass probability is at most
$$
q=\min\{1,\Pr(Y\ge x)/(1-\epsilon),\ 1-\Pr(Y<x)/(1+\epsilon)\}.
$$
The last term follows by wrapping the inside of the ball. For $x=j(1+\delta)^2$, $\delta>0$, the upper tail is at most $\exp[-j((1+\delta)^2-1-2\log(1+\delta))/2]$ by exponential Markov. This quantifies partial coverage without any asymptotic remainder.

For hard coverage compare the wrapped densities at widths $s$ and $as$, $a>1$. At a hole the former is at most $a^j e^{-\pi(1-a^{-2})r^2/s^2}$ times the latter, term by term. Hence every phase is covered if
$$
r^2>H^2=\frac{s^2}{\pi}\frac{j\log a+\log((1+\epsilon)/(1-\epsilon))}{1-a^{-2}}.
$$
Importantly $H^2\ge d^{2/j}j/(2\pi)$ for $j\ge2$. Put $t=1-a^{-2}$. The ratio $2\pi H^2/(js^2)$ is at least $1+(2/j)\log((1+\epsilon)/(1-\epsilon))$, using $-\log(1-t)\ge t$. This dominates $(1+\epsilon)^{2/j}$ by concavity. Now use the Poisson determinant inequality above.

## Certificate for every start and depth

Set $b_j=r/(d^{1/j}\sqrt{j/(2\pi)})$. Part 77 certifies $j\log R-\log d\le H_j$ for each prefix and adjacent ratios at least $e^{-u}$, $u=.055002$, throughout each box. Therefore
$$
 b_j\le B_j=\sqrt{(1-e^{-2uj})2\pi/j}\,
 \exp\min\{H_j/j,u(j-1)/2\}.
$$
The bound covers every endpoint, including across the dent. A deep column ($g_j/R<1/\sqrt2$, or the first crossing of the Part 77 shallow cutoff $e^{-.32}$) requires $j\ge6$. Over $6\le j\le799$, $B_j<.997$ and $B_j(1+2^{-j})^{1/j}<1$. The first inequality excludes the hard threshold for **every** $a$ and $0<\epsilon<1$. The second excludes positive $\delta$ at the valid minimum-based smoothing width. These are statements about sufficient tests; the actual covering radius can be smaller. [All-width caps and adjacent ratios](wall1_lcz_all_widths.md) · [Earlier transference test](wall1_dense_packing_ld.md)

Even at arbitrary smoothing error, $x\le z_j=j B_j^2 2^{2/j}$. Both exact-tail expressions inside the minimum defining $q$ are at least $\Pr(Y\ge z_j)$. Integration over $[v,v+\sqrt j]$, $v=\max(j,z_j)$, gives a lower bound using the density at the right endpoint, since this interval lies beyond its mode. The certificate verifies this lower bound exceeds $0.1$. Thus the optimistic exact-tail penalty from this test is less than $\log 10$ per fresh column even if the good event is certain. At rank 1023, along a single chain this costs less than 2356 nats for 1023 columns. This allowance also covers selecting the best single start at each endpoint by a prefix-measurable rule. A joint estimate for several starts at one endpoint would need additional information.

| Width | Deep hard hits at each of the three cuts | Part 77 residual lower, in cut order .25/.5/.85 | Residual lower after granting 2356 more nats |
|---:|---:|---:|---:|
|406|0|796562 / 811370 / 813763|794206 / 809014 / 811407|
|506|0|559914 / 576648 / 581065|557558 / 574292 / 578709|
|647|0|361765 / 376362 / 381267|359409 / 374006 / 378911|
|800|0|219222 / 235721 / 241940|216866 / 233365 / 239584|

The comparison concerns the log of the upper-bound integral. The existing shallow and width-three budgets are those of Part 77. No positive exponent growing sufficiently fast in the primal mean is proved. [Combined estimates](wall1_void_combined.md) · [Affine coverage](wall1_void_affine.md)

For clarity, let $S_i$ denote survival through step $i$. If the conditional pass bound on good prefixes is $q_i$, and bad prefixes have marginal probability at most $p_i$, then $P(S_i)\le q_i P(S_{i-1})+(1-q_i)p_i$. Iterating gives a product plus additive errors weighted by subsequent products. Subtracting marginal failure probabilities from a sum of log penalties has no tower-property justification. Even on disjoint fresh columns the history selects the prefix. A sharper covering theorem using other geometry, or a direct conditional uncovered-fraction estimate, remains open. No heuristic independence or numerical sampling enters the comparison.

## Reproduction

Run the following Python at the repository root. It uses Part 77's published integer cap certificates and checks every possible deep rank by outward-rounded interval arithmetic.

```python
from pathlib import Path
from mpmath import iv as I

I.dps = 40
source = Path("docs/research/wall1_lcz_all_widths.md").read_text()
rows = source.split("## All dimensions")[1].split("\n```text\n")[1].split("```")[0]
seen = []
for line in rows.strip().splitlines()[1:]:
    j, _, _, lcz, old = map(int, line.split())
    if not 6 <= j <= 799:
        continue
    seen.append(j)
    u = I.mpf(".055002")
    cap = I.mpf(min(lcz, old))/(10**9*j)
    B = I.sqrt((1-I.exp(-2*u*j))*2*I.pi/j)*I.exp(min(cap, u*(j-1)/2))
    invj = 1/I.mpf(j)
    assert B < I.mpf(".997") and B*(1+I.mpf(2)**(-j))**invj < 1
    z = j*B**2*I.mpf(2)**(2*invj)
    y = max(I.mpf(j), z.b) + I.sqrt(j)
    k = I.mpf(j)/2
    logmass = I.ln(j)/2 + (k-1)*I.ln(y)-y/2-k*I.ln(2)-I.loggamma(k)
    assert logmass > -I.ln(10)
assert seen == list(range(6,800))
assert 1023*I.ln(10) < 2356
print("794 prefix ranks verified")
```
