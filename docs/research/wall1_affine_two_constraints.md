# Two-relation counting closes the draw-13 raw-void step

For the original width-506 restart and the smaller-radius void b_i of Part 246,
this paper proof gives

\[
                  \Pr(b_{13}>0.280)<2.432\cdot10^{-12}.     \tag{1}
\]

Together with Part 250, the union over draws 7--13 is below 2.5035e-12. The
remaining sufficient history target is now
Pr(max_(14<=i<=404) b_i>0.280)<=3.922e-12. This is not the complete BKZ theorem:
that target, later projection control, and the separate score/horizontal/prefix
obligations remain open. The new proof is not Lean-formalized or independently
audited. Its finite regressions and outward interval checks pass.

## 1. Extracting a second relation

Part 260 reduces the missing term to compatible full ten-point configurations
of rank r in {4,5,6,7}, whose input matroid is connected, has no three-circuit,
and contains a four-circuit C. Let V=span(C), of dimension three, in augmented
input coordinates. Let O be the inputs outside V. Then span(O) intersects V
nontrivially: otherwise the inputs in V and those in O would form a nontrivial
direct-sum decomposition of the matroid, contradicting connectedness.

Project the O inputs modulo V. A dependence among their projections with nonzero
lift into V exists. The kernel of a finite vector configuration is spanned by its
circuit relations: subtract a circuit relation to remove a nonzero coordinate
and induct on support size. Thus at least one projected circuit has nonzero lift.
Choose its t inputs. They are independent before projection, since their unique
projected relation has nonzero lift, and have rank t-1 after projection. Each
projection is nonzero, so t>=2; also t<=r-2.

Express the nonzero lift using a minimal independent subset of C, of size
1<=a<=3. These a inputs and the t outer inputs form a circuit D of size d=t+a:
any relation must involve all projected-circuit inputs, and minimality of the
representation forces every chosen C input to occur. Since there is no
three-circuit, d>=4. The union has h=4+t inputs and rank t+2=h-2.

It follows that every missing configuration has a pair of circuits with these
properties, not just two arbitrary overlapping relations. In particular the
union has h>=6; five-point dependent unions are not needed as anchors here.
For compatible full outputs the same relations, ranks, and circuit properties
hold for the full candidate points.

## 2. Two equations and a positive Fourier sum

Fix the positions of C and D and normalize each nonzero relation independently.
Both relations have coefficient sum zero, since inputs are augmented with 1.
There are at most q^2 choices for C and q^(d-2) for D, hence at most q^d pairs.
Their two rows are independent because D contains inputs outside C. Only pairs
that arise from a configuration without a three-circuit need be counted.

For beta>0 define

\[
 F_\beta(u)=\sum_{z\in\mathbb Z}e^{-\beta z^2}e^{2\pi iuz/q}
 =\sqrt{\pi/\beta}\sum_{n\in\mathbb Z}
                       e^{-\pi^2(n+u/q)^2/\beta}>0.
\]

For the h nonzero columns l_i of the two-row relation matrix, character
orthogonality gives the exact one-coordinate constrained Gaussian sum

\[
             q^{-2}\sum_{u,v\in\mathbb F_q}
                                  \prod_{i=1}^h F_\beta(l_i(u,v)).       \tag{2}
\]

We next give a bound U_h(beta) uniform over every eligible relation pair.

## 3. The six-column improvement

When h=6, no projective direction among the l_i can occur three times. Otherwise
a nonzero row combination vanishes on those three columns and is supported on at
most three inputs, contrary to the absence of circuits of sizes one, two and three.
Partition the six columns into two triples with distinct directions in each.
Such a partition exists whenever each direction occurs at most twice: assign
one copy of each doubled direction to each triple and distribute the singletons.

Cauchy--Schwarz bounds (2) by the geometric mean of the two triple products with
each factor squared. Each triple consists of pairwise independent linear forms.
After a linear change of variables its factors are f(cu)^2, f(ev)^2, f(u+v)^2,
for nonzero c,e and a common symmetric decreasing majorant f of F_beta.

The required rearrangement follows from Pollard's theorem for prime cyclic groups.
In the notation r_(A,B)(x)=#\{a+b=x\}, it states
sum_x min(t,r_(A,B)(x))>=t min(q,|A|+|B|-t). See Theorem 2 in
[Nazarewicz--O'Brien--O'Neill--Staples, *Equality in Pollard's theorem*](https://www1.cmc.edu/pages/faculty/MONeill/papers/12/actarith1.pdf).
For odd-cardinality sets A,B,C this implies that sum_(x in C) r_(A,B)(x) is
maximized by centered intervals of the same sizes: bound it by
|A||B|-t min(q,|A|+|B|-t)+|C|t, then minimize over integer t. Centered intervals
attain this minimum by taking t at the boundary convolution value. Layer-cake
integration extends this to functions with odd-cardinality nonempty level sets.

Here we need no monotonicity assertion for a theta function. For centered u put

\[
 T_\beta=\sqrt{\pi/\beta},\quad A=\pi^2/\beta,\quad
 \alpha=A/q^2,\quad \delta=2e^{-A/4}/(1-e^{-2A}),
 \qquad f(u)=T_\beta(e^{-\alpha u^2}+\delta).
\]

The n!=0 terms in the Poisson sum are bounded by delta, since
|n+u/q|>=|n|-1/2. Thus F_beta<=f. The function f is symmetric decreasing, and
its nonempty level sets have odd cardinality. The rearrangement argument proves

\[
 (2)\le q^{-2}\sum_{u,v}f(u)^2f(v)^2f(u+v)^2.
\]

Write theta(x)=sum_(n in Z) exp(-x n^2). Expanding the delta error costs at most
sum_(j=1)^6 binomial(6,j) delta^j. On nonwrapping pairs, the remaining Gaussian
sum is bounded by the infinite two-dimensional sum; completing the square gives
4 alpha (u+v/2)^2+3 alpha v^2. A shifted Gaussian sum is at most its unshifted
sum by Poisson summation. Wrapping pairs have u^2+v^2>=q^2/8. Therefore

\[
 U_6(\beta)=T_\beta^6\left[
  \frac{\theta(4\alpha)\theta(3\alpha)}{q^2}
    +e^{-A/4}+\sum_{j=1}^{6}{6\choose j}\delta^j\right]             \tag{3}
\]

is a rigorous upper bound for (2). The two-dimensional theta factor is the gain
that was lost by treating the two equations separately.

## 4. Larger anchor unions

For h=7 or 8, the projective direction multiplicities are at most h/2: the
C-exclusive group has size at most three, the D-exclusive group has size h-4,
and every shared group has size at most three. Duplicate the column list and
pair its 2h columns across different directions. A perfect pairing exists when
no class occupies more than half the list; induction pairs two largest classes.
Apply Holder with exponent h to the h square-root pair factors. Each pair is a
uniform invertible change of variables, giving

\[
 (2)\le M_{h/2}(\beta)^2,
 \qquad M_s(\beta)=q^{-1}\sum_u F_\beta(u)^s.
\]

For h=9, pair the four C columns with four D-exclusive columns, and bound the
remaining column by theta(beta). Holder gives theta(beta) M_4(beta)^2.
These cover every h=4+t arising above, because t<=r-2<=5.

For computation, Minkowski's inequality applied to f gives

\[
 M_s(\beta)\le\frac{T_\beta^s}{q}
 \left[\theta(As/q^2)^{1/s}+q^{1/s}\delta\right]^s.                \tag{4}
\]

Use (3) for h=6, (4) squared for h=7,8, and theta(beta) times (4) squared with
s=4 for h=9. Theta is bounded using its positive geometric tail, with Poisson
summation when its argument is small. All operations used in the verifier are
outward interval operations; no heuristic Gaussian replacement is used.

## 5. Counting the complete configurations

There are N=517 integer coordinates at draw 13. Exponentially majorize the ball
condition on each anchor point. For a fixed placement of C and D, the number
of eligible anchor unions in the radius-R ball is at most

\[
                 B_{t,a}=q^{t+a}e^{(t+4)\beta R^2}
                              U_{t+4}(\beta)^N,
 \qquad \beta=\frac{(t+2)N}{2(t+4)R^2}.                         \tag{5}
\]

This is an upper bound obtained by dropping restrictions, not an assumption of
independence between candidate points. The same two modular equations hold in
each coordinate, which is why the Gaussian bound is raised to N.

Choose C's four positions, the t outside positions, the a overlapping positions
in C, and r-t-2 further basis positions. There are at most

\[
 L_{r,t,a}={10\choose4}{6\choose t}{4\choose a}
                                      {6-t\choose r-t-2}
\]

choices. For valid anchors the union rank is t+2. Bound each further basis
point by the full candidate count C=q^m mu; each of the 8-r remaining points has
at most q^(r-1) choices in the affine full-point span. Each compatible full
configuration costs q^(-mr). Thus the positive remainder in Part 260, after
using c_10/H(0)^2<=mu^(-10), is bounded by

\[
 \frac1{0.280\mu^{10}}
 \sum_{r=4}^{7}\sum_{t=2}^{r-2}
 \sum_{\substack{1\le a\le3\\t+a\ge4}}
 L_{r,t,a} B_{t,a} q^{-400(t+2)}
                 \mu^{r-t-2}q^{(r-1)(8-r)}.                    \tag{6}
\]

Every configuration has an anchor witness by section 1. Multiple witnesses only
increase this upper count. The Gaussian count in (5) may also include other
ranks, but the completion bound is applied to valid fixed-rank anchors before
upper-bounding their number; invalid anchors are not assumed to fix a span.
All powers of mu after normalization are negative, so the existing candidate
lower count is sufficient.

The interval verifier bounds (6) by 3.510e-31. Adding the unrounded charges
from Parts 258--260 proves (1). A sufficient remaining vertical-history condition
is now

\[
       \Pr(\max_{14\le i\le404}b_i>0.280)\le3.922\cdot10^{-12}.
\]

Indeed 7.150e-14+2.432e-12+3.922e-12+1.174e-12<7.6e-12, including Part 249's
compensator tail. This remaining condition is not proved, and the raw-ball
obstruction at draw 16 prevents simply repeating the same fixed-radius method
through the whole tour.

## Verification and limitations

Run `python3 docs/research/scripts/wall1_affine_two_constraints.py`. It checks:

- 4160 exact odd-set rearrangement cases over F_3 and F_5;
- 282 exact six-linear-form product bounds and their two-triple partitions;
- 132 first-extension witnesses from four-circuits in subsets of the binary cube
  over F_3, including the rank and nonzero-projection conditions;
- the concrete Gaussian bounds, full completion sum, draw-13 bound, and remaining
  history allowance using outward 80-digit interval arithmetic.

The finite cases do not replace the general arguments above. Pollard's theorem
is an external mathematical input stated precisely in section 3; the rearrangement
corollary and its use here are derived in this note. This proof and the earlier
geometric/moment transfers have not received an independent audit. Lean currently
covers only the earlier finite probability and centered-cancellation layer.
