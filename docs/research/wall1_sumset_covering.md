# Deferred columns and sumsets at the long-winner radius

**At threshold $1.10g$, the aperiodic Kneser inequality certifies at most
$6.043\cdot10^{-129}$ coverage, even if its per-height lower bounds are added
as though disjoint.** The required fractions are $0.8205$ or $0.874$,
depending on the window. This is an upper bound on the value of a proposed
*lower-bound certificate*. The actual union could cover every mark. The loss
occurs at the last doubling, even if one starts it with the **exact**
half-radius image and proves the sumset has trivial stabilizer. No earlier
dyadic iterations can repair that loss. The calculation applies prefix by
prefix, including on the late windows of Part 225.

## What the prefix reveals

Use the no-lookahead first pass, including its fixed tie rule. Write the
incoming raw syndrome as $\sigma(x,y)=x-A_{\rm old}y$ and the fresh column
as $a\in\mathbb F_q^{400}$, $q=3329$. For a possible old transcript $T$,
let $\Omega_T$ be the set of old matrices producing it. Under the original
uniform law the compatible matrices form the Cartesian product of $\Omega_T$
with the unrestricted columns. A membership test on a specified old lift is
an equality of syndromes. An exclusion of that lift is the complement of that
vector equality. For an exclusion of a projected candidate one must exclude
every admissible lift. Winner comparisons, ties, and first-hit exclusions
made before the append can all be included in $\Omega_T$ because their truth depends
only on the prefix. This argument needs neither a linear description of
$\Omega_T$ nor independence among its exclusions. It does require that
survival be decided by that time. Conditioning on passing a later gate or
on a future crossing can reweight $a$. [Part 108](wall1_first_tour.md) ·
[Part 172](wall1_transference.md)

Fix the full old matrix and frame. Let $F$ be the frozen span,
$P=P_{F^\perp}$, $S_F=F\cap\mathbb Z^N$,
$K=P\mathbb Z^N$ and $M=P\ker\sigma$, where the raw kernel is taken
in $\mathbb Z^N$. Projection identifies
$$
 H=K/M\simeq\mathbb F_q^{400}/\sigma(S_F),\qquad
 [Pz]\longmapsto\sigma(z)\bmod\sigma(S_F).
$$
Indeed two raw lifts of the same projection differ by $S_F$, and a
syndrome in $\sigma(S_F)$ can be canceled by such a difference.
Surjectivity follows from the output coordinates. For a **fixed raw**
candidate $(z,k)$ the test is $\sigma(z)=ka$. For its **projected**
candidate $(Pz,k)$ the test is $[Pz]=kU$, with $U$ the class of $a$
in $H$. Every class has equally many preimages. A raw test at invertible
height fixes one column, whereas a projected test fixes one mark. With a
coarser transcript one averages the following formula over its compatible old
matrices, unless the transcript already determines the marked state.
[Part 212](wall1_integrality_bound.md)

Put $n=506, d=505, h=|H|, D=\det M=h\det K=V_n g^n$, where $V_j$ is
the Euclidean unit ball volume. For $r=tg$, the period vector or a nonzero
horizontal vector settles the draw whenever $r\ge q$ or
$\lambda_1(M)\le r$. Otherwise set
$$
 X(b)=\{[y]:y\in K,\ \|y\|\le b\},\quad
 \rho_k=\sqrt{r^2-k^2},\quad
 \mathcal C=\bigcup_{k=1}^{\lfloor r\rfloor} k^{-1}X(\rho_k).
$$
Then $\Pr(s_i>r\mid\text{prefix})=1-|\mathcal C|/h$. Each positive height
is invertible and the negative height gives the same set by symmetry.
Two candidates $(y,k),(z,l)$ hit on the same mark exactly when
$ly-kz\in M$. Otherwise their mark events are disjoint. This is precisely
the all-heights experiment of Parts 217 and 219. The dilations preserve each
projective line of $H$. Heights cannot move points from a represented line
to a missing one. Adding two labels for the *same* mark keeps their common
slope when the sum height is invertible. Labels for different marks do not
have that property. These facts preclude adding coverage probabilities across
heights without controlling overlap. [Part 217](wall1_long_winner_ceiling.md) ·
[Part 219](wall1_covering_ceiling.md)

## The size available at the last doubling

For $A_k=X(\rho_k/2)$, the triangle inequality gives
$A_k+A_k\subseteq X(\rho_k)$. At this half radius projection modulo $M$
is injective on the lattice ball. Two distinct representatives of one mark
would differ by a nonzero horizontal vector of norm at most
$\rho_k\le r<\lambda_1(M)$. Thus the exact seed size is available without
any collision estimate. The obstruction is how small even this size is
relative to $h$.

**Half-radius bound.** Write $b=tg/2$, $v=2\pi^2 b^2/d$, and
$$
 E_t(g)=\frac{(2\pi e/d)^{d/2}(t/2)^d}{V_n g}
        \left(1+\frac{2e^{-v}}{1-e^{-3v}}\right)^d .
$$
For every eligible $k$, $|A_k|/h\le E_t(g)$.
In fact $1_{\|y\|\le b}\le e^{d/2}\exp[-d\|y\|^2/(2b^2)]$.
Sum on $K$, divide by $h$, and apply Gaussian Poisson summation.
The prefactor is $e^{d/2}(2\pi b^2/d)^{d/2}/D$. The remaining sum is
$\sum_{w\in K^*}e^{-v\|w\|^2}$. Since
$K^*=F^\perp\cap\mathbb Z^N$, one can choose $d$ coordinate rows
injective on its span. Dropping the other coordinates bounds the sum by
$(\sum_{j\in\mathbb Z}e^{-vj^2})^d$. For $j\ge1$ use
$j^2\ge1+3(j-1)$. This proves the formula, including the discrete-grid
correction. It counts all grid points at the enlarged radius $b$, so also
bounds the seed at every smaller radius. [Part 217, grid majorant](wall1_long_winner_ceiling.md#a-uniform-estimate-of-the-height-one-mean)

Let $J_k=\operatorname{Stab}(A_k+A_k)$. Kneser's theorem gives the lower
bound $L_k=2|A_k+J_k|-|J_k|$ on $|A_k+A_k|$. When $J_k=0$,
$L_k=2|A_k|-1$. Any inner dyadic sumset offered as input to the last step
is a subset of $A_k$, and gives no larger aperiodic guarantee. The same
size obstruction applies to Cauchy–Davenport on a prime cyclic quotient
unless one also proves a lower bound on the sizes of the lifted fibers.
Plünnecke's upper bounds for iterated growth under small doubling give no
lower bound of the required magnitude here. [DeVos, proof of Kneser's addition theorem](https://arxiv.org/abs/1303.3539)

Use the audited deterministic floor $g>g_0=32.18553$ through draw 405.
Both $E_t(g)$ and $gE_t(g)$ decrease with $g$. Even crediting every
height separately gives, in the aperiodic case,
$$
 \sum_{k\le r} L_k/h
 \le 2\lfloor tg\rfloor E_t(g)\le 2t g_0 E_t(g_0)=B_t.
$$
This sum is a deliberately favorable accounting of the separate guarantees.
Only their maximum is assured for the union from the guarantees alone.
[Part 220, unresolved entries](wall1_long_winner_routes.md)

| $t$ | Upper bound on the exact half-radius seed fraction | Upper bound on $B_t$ | Required coverage | Necessary stabilizer rank for the full Kneser expression to reach that target, even with disjoint credit |
|---:|---:|---:|---:|---:|
| 1.05 | $5.403\cdot10^{-141}$ | $3.652\cdot10^{-139}$ | $0.40$ | 40 |
| 1.10 | $8.535\cdot10^{-131}$ | $6.043\cdot10^{-129}$ | $0.8205$ or $0.874$ | 37 |
| 1.15 | $4.774\cdot10^{-121}$ | $3.534\cdot10^{-119}$ | $0.85$ | 34 |

For the last column let $J_{\max}=\max_k|J_k|$. The full expression satisfies
$L_k\le2|J_k||A_k|$, so the sum of its guarantees is at most
$J_{\max}B_t$ after normalization. Reaching fraction $\delta$ this way
requires a stabilizer of rank at least
$\lceil\log_q(\delta/B_t)\rceil$ at some height. Its presence alone does
not settle the occupancy count. In $H/J_k$, the expression divided by $h$ equals
$(2m_k-1)/[H:J_k]$, where $m_k$ is the number of occupied quotient
cosets. This is still an occupancy requirement. In particular, proving
aperiodicity would remove the only possible enlargement in this expression.
The actual doubling ratio could be far larger than Kneser's guarantee.

## What a stabilizer says about the dual

Let $J\le H$ and $K_J=\{y\in K:[y]\in J\}$. Its annihilator in
$\widehat H=M^*/K^*$ is $K_J^*/K^*$, of order $[H:J]$. A union of
$J$-cosets has Fourier support in that annihilator, by translating each
coefficient by $j\in J$. This identifies character classes. It supplies no
upper bound on the Euclidean length of a representative of a nonzero class.
Also, $X(b)$ spans the whole mark group for $b\ge1$ because it contains every
projected unit coordinate, which together generate $K$. Spanning and
being invariant under a subgroup are different tests.

Two explicit Euclidean examples distinguish these assertions. Both use
$q=3329$, $qK\subseteq M\subseteq K$, an appended unit-height coordinate,
$\lambda_1(M)>r$, and $\lambda_1(M^*)>0.201$. They test the group and
dual-minimum implications only. Neither is asserted to be a reachable prefix
or to have the prescribed $r/g$.

* **Trivial stabilizer, full span, sparse coverage.** Take $M=4\mathbb Z^2$,
  $K=(4/q)\mathbb Z^2$, and $r^2=1+(8/q)^2$. Only height one contributes.
  In grid coordinates the half-radius seed consists of zero and four unit
  vectors. Its double is the integer disk of radius two, of size 13. It
  equals the full covered set, spans $H$, and has trivial stabilizer because
  $q\nmid13$. The coverage is $13/q^2<1.174\cdot10^{-6}$. In one
  coordinate the same construction attains the prime-field bound exactly:
  the three-element seed doubles to five marks out of 3329.
* **A proper period with no short dual representative.** Take
  $M=2\mathbb Z\oplus(24/5)\mathbb Z^{12}$. Enlarge it to $K$ by
  adjoining $(2/q,0)$ and $(0,(24/(5q))(1,2,\ldots,2^{11}))$, where
  the twelve entries are successive powers of two. Then
  $H\simeq\mathbb F_q^2$. Every nonzero multiple of the second mark has
  distance at least $6/5$ from $M$. Starting with a nonzero centered
  residue, double its absolute value until it first reaches $q/4$.
  This takes at most ten doublings and there is no wrap before that step.
  Set $\rho_1=1.1$ and $r=\sqrt{1+\rho_1^2}<2$. The half-radius seed
  consists of first-coordinate residues from $-915$ to 915. Its double
  fills the first mark line. The radius-$\rho_1$ ball still misses every
  other line coset. Thus the stabilizer has order $q$, coverage is $1/q$,
  and the shortest nonzero vector of $M^*$ has norm $5/24>0.201$.
  This example has period rank one. Whether periods as large as the table
  requires can occur on the relevant gated prefixes is a separate question.
  Excluding them would only strengthen the numerical obstruction to this
  certificate.

## Consequence for the probability windows

For Part 225's direct residual, the targets are the two tails in (A) on
156–405, the conditional fourth moment in (B) on 132–405, or coverage
$0.874$ in (C) on 129–380. For the crossing alone the respective windows
are 71–405, 60–405 and 52–380. Outside its draw-55 exception a crossing
requires at least 36 exceedances of $1.15g_i$ on draws 55–405. The
half-radius estimates bound the strength of the certificate on each of those
draws. They imply neither a lower bound on actual misses nor a fourth-moment
estimate. The remaining question is whether the actual full-radius images
and their height dilations cover enough marks on the selected prefixes.
There is no new crossing or residual probability bound from dyadic Kneser
growth. [Part 222](wall1_long_winner_handle.md) · [Part 225](wall1_raw_graph_winner_cap.md) · [Part 227](wall1_frozen_contraction.md)

## Reproduction

Run the embedded verifier from the existing research scripts directory.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_sumset_covering.md | python -B -)
```

```python
from fractions import Fraction
from math import factorial
from mpmath import iv

iv.dps = 70
I, exp = iv.mpf, iv.exp
q, d = 3329, 505
g0 = I("32.18553")
Vn = iv.pi**253 / factorial(253)
for t, seed_bound, total_bound, targets, rank in [
    ("1.05", "5.403e-141", "3.652e-139", [".40"], 40),
    ("1.10", "8.535e-131", "6.043e-129", [".8205", ".874"], 37),
    ("1.15", "4.774e-121", "3.534e-119", [".85"], 34),
]:
    t = I(t)
    b = t*g0/2
    v = 2*iv.pi**2*b**2/d
    theta = 1 + 2*exp(-v)/(1-exp(-3*v))
    seed = (2*iv.pi*exp(1)/d)**(I(d)/2)*(t/2)**d * theta**d/(Vn*g0)
    total = 2*t*g0*seed
    assert seed < I(seed_bound) and total < I(total_bound)
    for target in map(I, targets):
        assert total*q**(rank-1) < target < total*q**rank

disk = {(x, y) for x in range(-2, 3) for y in range(-2, 3) if x*x+y*y <= 4}
seed = {(x, y) for x, y in disk if x*x+y*y <= 1}
assert {(x+u, y+v) for x,y in seed for u,v in seed} == disk
assert len(disk) == 13 and Fraction(13, q*q) < Fraction("1.174e-6")
half_width = Fraction(11, 20)*q//2
assert half_width == 915 and 4*half_width+1 >= q
for a in range(1, q):
    abs_residues = [min(z, q-z) for j in range(12) for z in [(a*2**j) % q]]
    assert 4*max(abs_residues) >= q
assert Fraction(5, 24) > Fraction(".201")
print("Verified three seed and all-height bounds, four rank tests, and both examples.")
```

## Audit

**Confirmed.** The note's interval verifier and the embedded checks in Parts 108, 217, 219, 225 and 227 passed. No numerical or mathematical correction is required.

On fixing the old matrix and frame, each fiber of the fresh-column map to $H$ has size $|\sigma(S_F)|$. The horizontal layer at height $k$ is the coset $kU$. Thus its hit set is $k^{-1}X(\rho_k)$, and the union over positive heights uses a single uniform $U$. In particular every height's hit set contains the zero mark, so any two such sets overlap.

An independent log-domain evaluation using $V_j=2\pi V_{j-2}/j$ gave the following values at the deterministic floor. The last column gives $\log_q(\delta/B_t)$ for each stated target, before rounding up.

| $t$ | $E_t(g_0)$ (approx.) | $B_t$ (approx.) | Rank threshold (approx.) |
|---:|---:|---:|---:|
| 1.05 | $5.402464\cdot10^{-141}$ | $3.651504\cdot10^{-139}$ | 39.19003 |
| 1.10 | $8.534210\cdot10^{-131}$ | $6.042918\cdot10^{-129}$ | 36.37746, 36.38525 |
| 1.15 | $4.773510\cdot10^{-121}$ | $3.533673\cdot10^{-119}$ | 33.60893 |

At $t=1.10$, rank at least 37 at some height is necessary for the sum of the full Kneser expressions to reach either target. The occupied coset counts must also satisfy $\sum_k(2m_k-1)/[H:J_k]\ge\delta$ even under disjoint credit. The true covered fraction on these prefixes remains open. The absence of a dual length bound from the group alone also follows by scaling both lattices by a common factor $c>0$. The quotient and corresponding subgroups are preserved, while the minimum representative length of each nonzero character class scales by $1/c$.

Direct enumeration modulo 3329 gave 13 marks and trivial stabilizer for the first disk, and five marks for its one-dimensional double. In the second example the 1,831 first-coordinate residues double to all 3,329 residues. Minimizing the sum of the twelve squared centered residues over every nonzero second mark gave $3{,}039{,}062$. Its minimum horizontal distance is therefore $(24/(5q))\sqrt{3{,}039{,}062}>2.5136$, above both tested horizontal radii. The resulting covered line has fraction $1/q$. A dual vector supported on the first of the twelve coordinates with entry $5/24$ represents a nontrivial character annihilating that line and attains the dual minimum.
