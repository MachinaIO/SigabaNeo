# Thin-shell sieving on the Part 39 planted lattice

**Theorem 1 (zero terminal acceptance).** Fix any integer plant, any matrix, and any dimension
$647\le D\le662$ of the Part 39 family, with $q=3329$, $n=512$, $r=D-513$, and unit embedding height.
The terminal shell prescribed in equations (2)–(3) of Doulgerakis–Laarhoven has no points of
the embedding lattice. Its S1 relative population error is exactly one. The probability that
the prescribed terminal difference scan returns the planted pair is zero, including conditional
on the pair being uniquely shortest. Thus this sieve gives no certified time exponent at these
parameters for any failure bound $\varepsilon<1$. This is a finite-dimensional statement about
the prescribed schedule. [DL26, §2.2](https://arxiv.org/html/2609.37482v1#S2.SS2) · [Part 39](wall1_projected_reference.md)

## Proof and numerical certificate

The lattice consists of integer triples $(x,y,t)$ with $x+Ay=t(e+As)\pmod q$. The map defining
this kernel is onto by the identity block on $x$, hence its covolume is $q^r$. Write
$G=(q^r\Gamma(1+D/2))^{1/D}/\sqrt\pi$ for the physical radius of a ball of volume $q^r$.
For $\ell=\lceil\ln D\rceil=7$, the terminal squared norm must lie in
$$
 I_D=\tfrac43 e^{2/7}G^2\,[(1-D^{-2})^2,(1+D^{-2})^2].
$$
In particular $G=33.2106\ldots$ at 647 and $38.8584\ldots$ at 662. The value near 31
describes the typical plant length more closely. At the endpoints the respective squared
intervals are contained in $(1956.928,1956.948)$ and $(2679.108,2679.133)$.
The following reproducible interval calculation checks all sixteen closed intervals.
The gamma factor uses exact integer factorials and the half-integer formula.

```python
from math import factorial
from mpmath import iv
iv.dps = 50
for d in range(647, 663):
    j = d // 2
    g = iv.mpf(factorial(j))
    if d % 2:
        g = iv.mpf(factorial(2*j+2))*iv.sqrt(iv.pi)/(4**(j+1)*factorial(j+1))
    one = iv.mpf(1)
    center = (4*one/3)*iv.exp(2*one/7)*(iv.mpf(3329)**(d-513)*g)**(2*one/d)/iv.pi
    lo, hi = center*(1-one/d**2)**2, center*(1+one/d**2)**2
    h = int(float(lo.mid))
    assert h < lo and hi < h+1
```

Every squared norm is integral. The interval check therefore excludes even ambient integer
points. The continuous shell has positive volume. Every accepted last-step difference would
belong to this empty set, and its difference set is empty as well. All raw positive moments
of its population vanish. In particular the discrepancy already at order one is the entire
Siegel prediction $\operatorname{vol}(S)/q^r$. On every tuple workload requiring a point
in this shell, all integer modular-coincidence and plant contributions are **exactly zero**.
This proves the theorem and rules out a comparison with only those two error sources.

## Haar hypotheses and moment orders

Here volumes use determinant-one coordinates. Write $U_R=L\cap S_R$, $\gamma=1-1/\ell$.
Stage 3 distinguishes (A) volume estimates, (B) list randomness and (C) the projected-block law.
The Haar sieve obtains exact conditional uniformity on finite shells by sampling and rejection.
Applying it to a prescribed coordinate projection requires a separate distributional argument.
The all-order Rogers and spherical Gram identities discharge the two classical formula inputs
on the Haar side. [Stage 3](../PROOF_GAP.md#stage-3-sieving-assumption-b) · [Lean bridge](../../SigabaNeo/Lib/Lattices/Reduction/Rogers/Laa26Bridge.lean) · [Laarhoven](https://arxiv.org/abs/2609.13635)

| Property in the repository analysis | Haar input and use |
|---|---|
| S1. Shell population within 1% of volume at every scheduled level | Siegel gives the mean, Rogers at order two bounds the variance. Apply Chebyshev and sum failures over levels. |
| S2. For every source mover and every target difference, the respective eligible-center and representation counts are between one third and twice the reference lens scales $\alpha_R,\beta_R$ | Near the critical radius the proof controls centered moments of degree $2h$ with a marked point, $h$ of order $\log D$. Orders through three give no such simultaneous estimate in this proof. |
| S3. The terminal difference set covers the catalogue ball of radius $\gamma R_m$ | The full near-critical coverage result uses the stronger lens estimates. For exact SVP the repository substitutes S3′, coverage through $(1+1/\ell)G$. Its marked second-moment argument uses one slot for the mark and up to two for its representations. The constant, cross and square terms use orders one, two and three respectively, together with geometric estimates. |
| S4. The shortest length lies below the scan cutoff | Order one controls the short tail. A ball second moment and Chebyshev bound the void probability at $(1+1/\ell)G$. The additional comparison of this radius with the catalogue radius is asymptotic. At $\ell=7$, $R_{\rm cat}/G=1.141733\ldots <8/7$, so the repository's literal chained S4 inequality also fails here. |
| S5. A sufficiently short basis is computable within the initialization budget | Dual Siegel first moment, transference and algorithmic basis reduction. A moment identity alone supplies no algorithm. For Part 39, lifting the free $y,t$ axes with centered $x$ entries and adjoining $qI_r$ gives an explicit basis of maximum norm at most $\max(q,\sqrt{1+r(q/2)^2})$. |

For a good bank and nonempty shells, cancellation gives each target the same mass.
The repository's acceptance lower bound is $99/1212$ under its population and bank hypotheses.
At the last merge there is no conditional law given acceptance. Even exhaustive pair search
cannot produce a terminal difference. In the Haar analysis, attaining
$c=\tfrac12\log_2(3/2)=0.292481\ldots$ additionally uses common-cap pair-work estimates and
a product-code search theorem. [Static hypotheses and S3′](provable_sieving.md) · [Corrected search argument](search_lemma.md) · [DL26](https://arxiv.org/abs/2609.37482)

## Theorem 2 (exact planted tuple mean)

Condition on $v=(e,s,1)$ and sample the retained $r$ rows of $A$ independently uniformly.
For a tuple $z_i=(x_i,y_i,t_i)$ let $Y$ and $X$ have respective rows $y_i-t_i s$ and
$x_i-t_i e$. Write $a=\operatorname{rank}_q Y$, $b=\operatorname{rank}_q[Y\ X]$.
For any finitely supported weight $F$ on integer tuples,
$$
 \mathbb E_A\sum_{z\in L_A^k}F(z)=\sum_z F(z)\,\mathbf1_{a=b}\,q^{-ra}.
$$
Indeed each column of $-X$ prescribes the image under $Y$ of one independent uniform
row of $A$ (transposed). A specified image has probability $q^{-a}$ if it lies in the
column space, zero otherwise. Multiplication gives the formula including rank zero.
This is the inhomogeneous form of Q1. The exponent uses the **retained check count** $r$.
The Lean theorems for the homogeneous kernel use a different sampling law.
[QAry.meanValue, firstMoment and secondMoment](../../SigabaNeo/Lib/Lattices/QAry.lean) · [Q1–Q3](qary.md)

For one point the three weights are $q^{-r}$ for $Y\ne0$, one for $X=Y=0$, and zero
otherwise (all tests modulo $q$). At physical outer radius $R$ with $R\sqrt{10}<q$,
the CBD(3) coordinate bound implies $|x_j-t e_j|,|y_j-t s_j|\le R\sqrt{10}$.
Thus deterministic points there are precisely the multiples of $v$. There are also
mixed correlations. Translating any slot separately by an integer multiple of $v$
preserves both matrices and membership. For example the pair $z,z+v$ with $Y(z)\ne0$
has weight $q^{-r}$, even when neither slot lies on the plant line.

**Exact modular correction at other radii.** Define $a_0,b_0$ by the same ranks over
the rationals. Group the weighted integer tuples by these four ranks, with total
weight $N_{a_0 b_0 a b}$. Relative to using rational ranks in the discrete formula,
the exact signed correction is
$$
 \sum N_{a_0 b_0 a b}
 (\mathbf1_{a=b}q^{-ra}-\mathbf1_{a_0=b_0}q^{-ra_0}).
$$
This includes changes of consistency. Even the rational-rank sum still needs an
integer-sum versus integral estimate on each relation space (the Q3 issue).
Q2 applies to the matrices whose minors are tested. The sheared rows can exceed
the physical radius by a large factor. For ordinary unsheared triples $31^2=961<3329$
but $31^3=29791>3329$. The deficit can actually occur inside this ball. Take $t=x=0$
and pad the following three $y$ rows with zero coordinates:
$(15,1,0),(0,15,1),(-1,3,15)$. Their determinant is $3329$ and a two-row minor
is $225$. All lengths are below 16. This ordered triple contributes an excess
$q^{-2r}(1-q^{-r})$ over its rational-rank weight; permutations and coordinate
placements give further terms. This is an example for a ball, not an estimate of
shell occupancies. For the actual terminal workload Theorem 1 evaluates the entire
correction as zero. For populated earlier shells the displayed finite sum specifies
the correction exactly; a small uniform relative bound is open here. The uniform-residue
rank frequencies in Q3's companion note do not count short integer tuples. [Modular deficits](qary.md)

## Changes of metric and the remaining guarantee

Scalar rescaling multiplies the squared spectrum and both interval endpoints by the
same positive number. An integer height multiplier still gives integral squared norms,
but changes the determinant and the plant length, requiring fresh endpoint and uniqueness
checks. A nonintegral height changes the attainable labels to $j+h^2t^2$ for integer
$j,t$. Widening to relative half-width $1/D$ gives squared interval length $4R_m^2/D>12$
at 647 and 662. It removes the missing-label obstruction. Even snapping to a single
attainable ambient label leaves a parity constraint: differences of two integer vectors
of equal squared norm have even squared norm. A plant of odd squared norm cannot be
obtained that way. Gaussian weights of full support remove the empty-shell conditioning
but require a new output distribution and success analysis. For a changed schedule one
still needs simultaneous bank degree bounds, coverage of the fixed plant and a search
work bound for the changed distribution. [Wide-shell acceptance](wide_shell_sieve.md) · [Reverse Minkowski counterexamples](reverse_minkowski_blocks.md)

Part 39 separately certifies unique shortestness with failure at most $0.00483352$
at 647 and $1.423\cdot10^{-20}$ at 662, averaged over the specified CBD plant and
uniform matrix. An independent worst-case exact SVP solver with conditional failure
at most $\delta$ adds at most $\delta$ to those failure bounds. For example ADRS gives
randomized $2^{D+o(D)}$ time and space. This is an independent solver exponent.
Neither a modified planted sieve exponent nor a finite operation count follows here.
[Part 39 certificate](wall1_projected_reference.md) · [ADRS](https://arxiv.org/abs/1412.7994)
