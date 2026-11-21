# Wall 1. What terminal minimum suffices for the projected plant?

**Verdict.** For the full terminal block, Parts 88/92 do not certify 99% uniqueness at either quoted width. At horizontal ranks 406 and 506 a rigorous all-heights, norm-only certificate needs respectively **35.02 and 19.41 times** the corresponding $0.85$ GSA length (rounded up). The Part 92 radii fall short of this sufficient certificate by factors about **221 and 123**. These are gaps to a proof, not necessary improvements to the reducer. The exact 99% threshold for CBD plants does not follow from the reported GS lengths. The sharp deterministic threshold for a given norm and the quantile of that threshold are different objects.

There is a literal exception to any claim about *every* block of dimension at most $\beta$. Project away the entire horizontal basis. The projected lattice is the integer height axis, and the image of the plant is its unit generator for every sample. The minimal required lower bound is zero (zero times either GSA target), with success probability one. This certifies only a projected image. The substantive comparisons below retain the terminal horizontal block; shrinking it changes the recovery question and the prefix one would have to lift through.

## Exact criterion conditional on the reducer

Put $N=1023$, $D=3329^{511/1023}$ and condition on the design and independent reducer coins. For a horizontal basis prefix spanning $W$, write $Q$ for horizontal orthogonal projection off $W$, $d=\operatorname{rank} Q$, $H=QL_0$, $y=QX$, $R=\sqrt{1+\|y\|^2}$, where $X$ has independent CBD(3) entries. Part 47's unique additive splitting gives the projected vectors $(h+ky,k)$ with $h\in H$. Conditional on the prefix and lattice, $X$ retains its original law. The oracle rank is $d+1$. [Part 47](wall1_decoupled.md) · [Lean splitting and fiber count](../../SigabaNeo/Lib/Lattices/Research/Wall1/Decoupled.lean)

For $d>0$, the following three strict conditions together are necessary and sufficient:

1. $\lambda_1(H)>R$.
2. $y$ belongs to the open Voronoi cell of zero in $H$.
3. For each integer $2\le k\le R$, $\operatorname{dist}(ky,H)^2>R^2-k^2$.

Indeed, test squared lengths at heights zero, one, and $k\ge2$ respectively. Sign symmetry covers negative heights, and larger heights already exceed $R$. Strictness excludes ties. Thus an exact conditional probability is the sum of the indicator of these tests over $X\in\{-3,\ldots,3\}^N$, weighted by $\prod_i\binom{6}{3+X_i}/64$. This also specifies exactly what it would mean to certify 0.99 for a particular output. GS lengths alone do not specify the open Voronoi cell, the other coset distances, or the orientation of $Q$ relative to the CBD axes.

## Sharp uniform certificate from the norm and horizontal minimum

Set
$$
T(R)=\max_{k=0,\ldots,\lfloor R\rfloor}
\left(k\sqrt{R^2-1}+\sqrt{R^2-k^2}\right).
$$
Any competitor with $h\ne0$ of length at most $R$ forces $\|h\|\le T(R)$ by the triangle inequality. Those with $h=0$ are just multiples of the plant. Hence $\lambda_1(H)>T(R)$ suffices. The function is nondecreasing. For each fixed $R$ this cutoff is sharp among unrestricted horizontal lattices and plant directions of that norm: take a shortest generator of length $T(R)$ antiparallel to $y$, and complete orthogonally with longer generators. At a maximizing height the competitor ties. At $y=0$ use any direction. Thus even a factor two times the plant length is unsafe as a deterministic criterion. Sharpness here does not imply a 1% frequency of aligned CBD plants, or realization of the extremizer by the specified graph ensemble. [Earlier all-heights bound](wall1_height_union_fix.md)

At a fixed projection the smallest non-strict upper cutoff for this norm-only argument is the conditional 0.99 quantile of $T(R)$, with a **strict** minimum bound above it. We bound that quantile uniformly. For $0<t<1/3$,
$$
\Pr(\|QX\|^2\ge h)\le e^{-th}(1-3t)^{-d/2}.
$$
Indeed each coordinate has mgf $\cosh(s/2)^6\le e^{3s^2/4}$. Introduce an independent standard Gaussian $G$ in the image of $Q$ and average $\exp(\sqrt{2t}\langle G,X\rangle)$ first over $G$, then in reverse order. The latter expectation is bounded by the Gaussian squared-norm mgf. Optimize at $t=(1-3d/(2h))/3$ for $h>3d/2$. The certificates below round the solution for $h$ upward to a thousandth. They use no Gaussian approximation to CBD.

The terminal head equals $\lambda_1(H)$ under the exact terminal SVP test **at horizontal rank $d$**. Without that test, a common lower bound on all remaining GS lengths suffices by the last nonzero integer coefficient argument. A single arbitrary GS length cannot replace the minimum.

| Horizontal rank $d$ | Final rank | Squared horizontal norm cap $h$ | Sufficient physical cutoff $T(\sqrt{1+h})$, rounded up | Cutoff divided by $D$ (approx.) | Multiple of $0.85$ GSA at $d$ |
|---:|---:|---:|---:|---:|---:|
|405|406|746.430|741.957|12.911|35.296|
|406|407|748.090|742.966|12.928|35.016|
|505|506|911.528|909.286|15.822|19.515|
|506|507|913.171|910.327|15.840|19.405|

For a hard final cap of 406 or 506, use rows 405 or 505 respectively. Relative to the *published* width-406/506 GSA denominators these cutoffs are about 34.97 and 19.38 times target. Part 92 certifies physical minima 3.36337038 and 7.41883519 at ranks **406 and 506**. One can drop the shortest head of such a block: the next quotient minimum is at least $\sqrt{3}/2$ times the old minimum, since any vector in the quotient lifts with parallel component at most half the shortest length by rounding. Thus for the strict final budgets the inherited sufficient-certificate gaps are about **255 and 142** in multiplicative terms. A fresh reduction at the smaller width would require its own certificate. At unchanged horizontal widths the normalized shortfalls are about 12.870 and 15.711; even the Haar radii 0.1253 and 0.3619 fall far below these cutoffs. Part 93's other widths concern Haar lattices. No nontrivial full-terminal crossing below 647 follows from these comparisons. [Part 88](wall1_li_walter.md) · [Part 92](wall1_qary_gap.md) · [Part 93](wall1_combined_reducer.md)

Even height zero demands substantially more information. Writing $Z=\|QX\|^2$, its mean is $3d/2$ and its second moment is at most $(3/2)^2(d^2+2d)$ by independence, $Q^2=Q$, and the nonpositive fourth cumulant of a sum of fair signs. Paley–Zygmund gives $\Pr(Z>0.8\,\mathbb EZ)\ge0.04d/(d+2)>0.01$ at these widths. Hence a fixed lattice giving 99% uniqueness must actually have $\lambda_1(H)>\sqrt{1+1.2d}$ (the event above already forces failure for smaller or equal minima). This necessary floor is about 22.1 and 24.7 at ranks 406 and 506. A certificate below the floor leaves the actual minimum unresolved. Neither this floor nor the norm-only sufficient cutoff determines the minimal probabilistic scalar certificate over the graph ensemble. A conditional 99% plant guarantee on a 99% design event would yield only 98.01% by multiplication if both budgets were exhausted.

## A smaller sufficient bound if every tail GS length is available

Let $e_i$ denote the GS unit directions of the horizontal quotient basis. On the event $R^2\le 1+2d$ and $\max_i|\langle y,e_i\rangle|\le a=\sqrt{3\log(400d)}$, every competing correction $h\ne0$ with last nonzero coefficient at $i$ satisfies
$$
g_i\le |\langle h,e_i\rangle|\le k a+\sqrt{R^2-k^2}\le R\sqrt{1+a^2}.
$$
The last step is Cauchy–Schwarz. Thus a common tail GS bound strictly above $\sqrt{(1+2d)(1+a^2)}$ suffices. The same CBD mgf bounds the coordinate-event failure by $2d\exp(-a^2/3)=0.005$, and the norm-event failure is below 0.005 by the script. At horizontal ranks 406 and 506 these cutoffs are 173.424 and 195.304 rounded up, about 8.17 and 4.16 times $0.85$ GSA. These stronger profile hypotheses are not certified by the terminal-minimum rows. This illustrates why a gap to the scalar norm-only certificate cannot be interpreted as necessary for all proofs.

## Interval reproduction

Run with Python 3 and mpmath. Decimal strings are inputs to outward-rounded interval arithmetic. The adjacent thousandth check brackets the optimized Chernoff cutoff, not the actual CBD quantile.

```python
from math import isqrt
from mpmath import iv as I
I.dps = 50
D = I.exp(I.ln(3329)*511/1023)
def tail(d,h):
    t = (1-3*d/(2*h))/3
    assert 0 < t and 3*t < 1
    return I.exp(-t*h)*(1-3*t)**(-I.mpf(d)/2)
def target(b):
    s = (I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    return I.mpf('.85')*I.exp((2*b-1024)*s)
for d,j,cap,ratio in [(405,746430,741957,35296),(406,748090,742966,35016),
                      (505,911528,909286,19515),(506,913171,910327,19405)]:
    h = I.mpf(j)/1000
    assert tail(d,h) < I.mpf('.01') < tail(d,h-I.mpf('.001'))
    values = [k*I.sqrt(h)+I.sqrt(1+h-k*k)
              for k in range(isqrt((1000+j)//1000)+1)]
    T = I.mpf([max(x.a for x in values),max(x.b for x in values)])
    assert T < I.mpf(cap)/1000
    assert abs(T/(D*target(d))-I.mpf(ratio)/1000) < I.mpf('.001')
    b = 406 if d <= 406 else 506
    old = I.mpf('3.36337038' if b == 406 else '7.41883519')
    inherited = old if d == b else old*I.sqrt(3)/2
    gap = T/inherited
    expected = {405:255,406:221,505:142,506:123}[d]
    assert abs(gap-expected) < 1
    profile = I.sqrt((1+2*d)*(1+3*I.ln(400*d)))
    assert tail(d,I.mpf(2*d)) < I.mpf('.005')
    assert profile < I.mpf({405:173193,406:173424,505:195096,506:195304}[d])/1000
    print(d,T,T/D,T/(D*target(b)),gap)
```

## Audit note (Nov 2026)

Independent audit: CORRECT WITH MINOR ISSUES. The all-heights criterion, the sharpness extremizer, the CBD(3) Chernoff numbers
and the tail-GS bound were all verified, and the embedded script passes. Corrections and clarifications:

* The profile-cutoff multiples have been corrected to 8.17 / 4.16.
* Ranks: "horizontal rank 406/506" means final rank 407/507. At those ranks the multiples are 35.02 / 19.41 and the gaps to
  Part 92 are 221 / 123. The 34.97 / 19.38 and 254.73 / 141.53 figures are for final rank 406/506.
* Why the certificate is so demanding: T(R) ≤ R² (Cauchy–Schwarz), with near-equality at k ≈ |y|. A norm-only certificate has
  to exclude a lattice vector aligned against k·y, and that vector can be as long as about |y|². The estimator heuristic instead
  treats coset positions as random.
* The width scan is stronger than the text says. The norm-only cutoff stays above 0.85·GSA at every final width up to 1023. The
  tail-GS profile cutoff first drops below it at final width 892.
