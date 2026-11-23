# Two-relation envelopes for every shortest-circuit size

This extends Part 261's four-circuit argument to every girth and rank needed by
Part 277. At the actual draw-14 parameters, the full-incidence transfer from all
circuits, all rank-two components, and other connected components through size
eleven is below 6.541e-17, including their proper-subset density errors. Larger
components remain unresolved. Including size twelve already makes the present
envelope exceed 7.48e-5 before the later refinements.
[Part 282](wall1_unique_four_circuit.md) now strengthens both the Gaussian and
witness counts; the current verifier includes those changes. The full transfer
target and draw-14 failure bound remain unproved. The rank-sensitive refinement is Part 279; the fixed-position and three-group
refinements below are Part 280. These are paper arguments with exact
finite and interval checks, not a Lean proof.

## Extracting two relations, including extensions inside the first span

Let T be a connected augmented-input matroid of size h, rank r, nullity at least
two, and girth c. Fix any shortest circuit C of size c. There exists a circuit D
such that, writing t=|D\C| and a=|D intersect C|,

\[
 1\le t\le r-c+2,\quad 1\le a\le c-1,\quad t+a\ge c,
 \qquad |C\cup D|=c+t=:H,\quad\operatorname{rank}(C\cup D)=H-2. \tag{1}
\]

There is a stronger choice of witness:

\[
 t_{\min}(r,c)=\begin{cases}1,&r=c-1,\\2,&r>c-1,\end{cases}
 \qquad t\ge t_{\min}(r,c).                                \tag{1a}
\]

If r=c-1, every input lies in V=span(C). Choose an input outside C and express it
using a minimal independent subset of C. Together they form D; t=1, and girth
forces a=c-1.

If r>c-1, partition T into the inputs in V and those outside V. Both parts are
nonempty, and the first spans V. Connectedness forces the span of the second to
intersect V nontrivially. This is true even if T has additional inputs inside V;
there is no need to choose an inside extension. Every outside input has nonzero
projection modulo V, so a projected circuit has at least two elements. Decompose a
projected relation with nonzero lift into projected circuit relations; at least
one has nonzero lift. Its t inputs are independent before projection and have
rank t-1 afterwards. Express its lift using a minimal independent subset of C,
of size a. This gives the circuit D, as in Part 261. Rank bounds give (1).
The assumption h>=r+2 ensures an input outside C exists when r=c-1; when
r>c-1, the rank itself ensures an input outside V exists.

The two circuit rows are independent and have coefficient sum zero. Their H
columns are nonzero. No projective direction occurs more than H-c times:
otherwise a nonzero row combination vanishing on that direction would be a
relation supported on fewer than c columns. This also applies to compatible
full candidate points, whose input and full-point matroids coincide.

## A weighted three-direction Holder bound

Consider H nonzero linear forms on F_q^2, divided into projective direction
classes. Suppose no class has more than A members, where

\[
                    H=2A+B,\qquad A\ge B>0.
\]

The vector (1,...,1) lies in the convex hull of vectors assigning weights A,A,B
to three columns from three distinct classes, and zero to other columns.
To see this, take any linear functional on the H coordinates, replace its values
in each class by their maximum, and sort these class maxima. Each class has mass
at most A and total mass is H. Filling the largest maxima first bounds the
functional by A times each of the first two maxima plus B times the third.
This is exactly the maximum on the stated vertices. The finite convex-hull
separation criterion proves the claim, also for negative functional values.

Apply generalized Holder to such a convex decomposition. Each factor involves
three pairwise independent forms with exponents A,A,B. A linear change of
variables and the unequal-function version of Part 261's Pollard rearrangement
bound its expectation by

\[
                   q^{-2}\sum_{u,v} f(u)^A f(v)^A f(u+v)^B,    \tag{2}
\]

where f is the common symmetric decreasing majorant of the positive Fourier
Gaussian F_beta. Multiplying by a nonzero scalar only permutes each function's
level sets, so their cardinalities remain odd as required by that argument.
The bound applies even when forms within a direction have different scalars.

For a two-relation anchor of girth c with H<2c, choose

\[
                  A=\max(H-c,H/3),\qquad B=H-2A.
\]

Then the direction multiplicity bound implies the hypothesis. Both exponents
are at least one in the anchor ranges here. This includes equal exponents H/3
when H<=3c/2, and unequal exponents otherwise.

For completeness, set T_beta=sqrt(pi/beta), L=pi^2/beta,
alpha=L/q^2, delta=2 exp(-L/4)/(1-exp(-2L)), as in Part 261. Then
f(u)=T_beta(exp(-alpha u^2)+delta). For p>=1 and 0<=x<=1,
(x+delta)^p<=x^p+e_p, with e_p=p delta(1+delta)^p, by the mean-value bound.
Completing the square on nonwrapping pairs and bounding wrapping pairs gives

\[
 U_{H,c}(\beta)=T_\beta^H\left[
 \frac{\theta((A+B)\alpha)
       \theta(A(A+2B)\alpha/(A+B))}{q^2}
 +e^{-AL/8}+2e_A+e_B+e_A^2+2e_Ae_B+e_A^2e_B\right].           \tag{3}
\]

Indeed the nonwrapping exponent is
(A+B)(u+Bv/(A+B))^2+A(A+2B)v^2/(A+B); a shifted one-dimensional Gaussian sum is
at most its unshifted sum. On wrapping pairs u^2+v^2>=q^2/8. The remaining terms
are the positive expansion of (1+e_A)^2(1+e_B)-1. Equation (3) bounds (2).

For every H, a simpler alternative is

\[
 \theta(\beta)^{H-2p}M_p(\beta)^2,\qquad p=\min(H/2,c),        \tag{4}
\]

with M_p=q^(-1) sum F_beta(u)^p bounded as in Part 261. If H<=2c, duplicate the
columns and pair across different directions, then apply Holder. If H>2c,
choose 2c columns with each direction occurring at most c times, pair them, and
bound the remaining factors by theta(beta). Such a selection exists since at
least c columns lie outside a largest direction class; if every class has fewer
than c members, any suitable 2c-column selection works. The verifier uses the
smaller of (3), when available, and (4). Every chosen bound is valid separately.

## Retaining the three circuit groups

For a fixed overlap a, partition the H columns into C-only, D-only and shared
columns, of sizes c-a, t and a. Choose one column from each group. These three
forms always have different directions, since the two exclusive groups have
one zero coefficient each, while a shared column has both coefficients nonzero.
Average over all such triples with equal weights. Assign the group sizes as
exponents to each triple; every original column then has total exponent one.
Generalized Holder followed by the unequal-function rearrangement bounds the
Fourier expectation by

\[
 q^{-2}\sum_{u,v} f(u)^{c-a}f(v)^t f(u+v)^a.                \tag{4a}
\]

This argument does not assume that all shared columns have the same direction.
Permuting the three exponents is valid by invertible changes of variables and
the symmetry f(-u)=f(u). Put A>=B>=C for the sorted group sizes and
Delta=AB+AC+BC. The same square-completion and tail argument as (3) gives

\[
 T_\beta^H\left[
 \frac{\theta((A+C)\alpha)\theta(\Delta\alpha/(A+C))}{q^2}
 +e^{-BL/8}+e_A+e_B+e_C+e_Ae_B+e_Ae_C+e_Be_C+e_Ae_Be_C\right]. \tag{4b}
\]

All error terms are positive. The verifier takes the smaller of this overlap-specific
bound and the earlier bounds. Thus U in (5) may now depend on a as well as c,t.
This refinement is valid for every positive triple of group sizes, including
H>=2c where the earlier symmetric three-direction bound was unavailable.

## Counting and completing the anchors

Let U be that Gaussian bound. For fixed positions of C and D, there are at most
q^(c-2) q^(t+a-2) normalized coefficient pairs with sum zero. Character
orthogonality and the positive Fourier representation give a one-coordinate
Gaussian sum bounded by U. Hence the anchor joint-incidence count is bounded by

\[
 B_{c,t,a}=q^{c+t+a-4} e^{H\beta R^2} U(\beta)^N q^{-m(H-2)},
 \qquad \beta=\frac{(H-2)N}{2HR^2}.                           \tag{5}
\]

This only counts coefficient pairs compatible with the rank and girth conditions
before dropping restrictions in the Gaussian count. It does not apply a girth
bound to arbitrary, ineligible coefficient pairs.

Choose the c circuit positions, the t new positions, the a overlap positions,
and r-H+2 further basis positions. Complete the remaining h-r-2 positions in the
rank-r affine full-point span. Thus the ordered connected full-incidence count
in the (h,r,c) stratum is at most

\[
 \sum_{t=t_{\min}(r,c)}^{r-c+2}\ \sum_{\substack{1\le a<c\\t+a\ge c}}
 {h\choose c}{h-c\choose t}{c\choose a}{h-c-t\choose r-c-t+2}
 B_{c,t,a}\mu^{r-c-t+2}q^{(r-1)(h-r-2)}.                      \tag{6}
\]

As before, count valid fixed-rank anchors and extensions first, then bound their
number by unrestricted positive sums. Invalid Gaussian-counted anchors are not
assumed to determine a span. All configurations have a witness by (1); multiple
witnesses only enlarge the upper bound.

For each stratum the verifier can alternatively use the older one-circuit bound

\[
 {h\choose c}{h-c\choose r-c+1}\epsilon_c\mu^{r-c+1}
                                      q^{(r-1)(h-r-1)}.       \tag{7}
\]

This is valid because the stratum actually has a c-circuit. Sum the selected
bounds over girths 3<=c<=r+1 and ranks 2<=r<=h-2, and add epsilon_h for circuits.
Each selected bound has nonnegative coefficients and mu-degree at most h-4;
the same negative-power argument as Part 276 justifies using the mean floor in
the normalized transfer. Selecting an alternative at that floor fixes a valid
polynomial bound for that stratum; no monotonicity of a pointwise minimum is
needed.

## Fixed positions in uniform rank strata

If c=r+1, every r-element subset of the support is independent. In particular,
every r+1-element subset is a circuit. Fix C to be the first r+1 positions and D
to be the first r positions together with position r+2. They are circuits with
t=1, a=r, union rank r, and the required girth. No union over position choices
is necessary. Apply the same eligible coefficient-pair Gaussian count to this
fixed pair, then complete the other h-r-2 positions as before.

Thus the binomial product in (6) is replaced by 1 in this stratum, and the factor
binomial(h,c) in (7) is also replaced by 1. For (6) this removes the factor
binomial(h,c)(h-c)c. This is not division by an assumed average number of
witnesses: the fixed witness exists for every ordered configuration separately.
The replacement is not made when c<r+1.

## Actual draw-14 result and remaining class

Use q=3329, m=400, N=518, the Part 276 radius and mean floor, and Part 277's
transfer T. Let F_known contain all circuit and rank-two components through size
24 and every other connected component through size eleven. The computation
proves the following full-incidence transfer bounds as the latter size cutoff
increases:

- through size nine: <3.577e-28;
- through size ten: <1.646e-22;
- through size eleven: <6.541e-17.

These include mixtures of admitted components. The first improvement comes from
(1a): the earlier envelope included t=1 extensions even when a t>=2 witness was
always available. Removing those unnecessary witness choices is an upper-bound
improvement, not a cancellation of genuine configurations. Fixed-position
witnesses further reduce the previously dominant uniform rank-three stratum.

For each known component size h<=11, use its full-incidence bound in Part 277's
formula (4) for the density error E_h. This formula depends only on full-incidence
bounds at smaller sizes j<h, all already available here. It requires no global
cap F_h<=mu^h. Use activities F_h+E_h through size eleven, and the existing
circuit/rank-two discrepancy activities above eleven. Their entire transfer,
including all mixtures, remains below 6.541e-17.

The lower-mean substitution is valid for these additional errors as well: a term
in the dependent-set generating function at size j has mu-degree at most j;
multiplication by mu^(h-j-1) leaves degree at most h-1. Independent-product
errors also have degree h-1. Consequently every activated normalized term still
has negative mu-degree. All numerator majorants are nonnegative.

Let R_large be the signed, unnormalized correction to E[K_12(Z;mu)^2] from
supports containing a connected component of size at least twelve, rank at least
three, and nullity at least two. Reference and covered corrections give

\[
 \Pr(b_{14}>0.280)<9.132\,10^{-13}
             +\frac{|R_{\rm large}|}{0.280D_{12}(\mu)^2}.     \tag{8}
\]

This is not a numerical failure bound without the remainder. A sufficient
remaining history requirement is

\[
 \frac{|R_{\rm large}|}{0.280D_{12}(\mu)^2}
 +\Pr(\max_{15\le i\le404}b_i>0.280)\le3.0088\,10^{-12}.     \tag{9}
\]

The constants in (8)--(9) sum to the earlier 3.922e-12 history allowance. The
unresolved component sizes are now 12--24, including all mixtures involving
one of them. Neither (9) nor the full BKZ theorem is proved.

Before Part 282, including size-twelve strata in this two-relation envelope
yielded a central transfer greater than 7.48e-5. The current script incorporates
Part 282; its cumulant-transfer bound is stated in that follow-up. This is an overestimate's value, not a lower bound
for the actual contribution. Its largest size-twelve strata have girth four and
ranks six and five; the uniform rank-three contribution is now much smaller. More relations or sharper Gaussian counting are
needed. The Part 277 alternative full-incidence target remains valid as well.

Run `python3 docs/research/scripts/wall1_general_two_relations.py`. It checks 816
shortest-circuit witness cases over F_3, 101 fixed-position witnesses on uniform
moment-curve supports over F_7, 510 exact circuit-group Holder inequalities,
and 2248 exact rational weighted
three-direction inequalities over F_5 with nontrivial column scalings, then the
actual-parameter interval bounds. The general arguments, including the Pollard
input already stated and sourced in Part 261, are not replaced by these tests.
