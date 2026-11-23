# Occupancy through an entire selected projection flag

This extends the single positive-height description in
[projected occupancy](wall1_projected_occupancy.md) to an arbitrary primitive
projection flag. It retains horizontal branches and mark-group losses. It is a
deterministic identity, not yet an estimate under the selected-history law.
The half-open lift construction also occurs in
[sublattice union](wall1_sublattice_union.md); the additional point here is the
exact cancellation of the multiplicities in the occupancy certificate.

## Finite lifts and their labels

Let L be a full sublattice of Z^n, and let U be a rational r-dimensional subspace.
Set Gamma=L intersect U and Lambda=Z^n intersect U. Choose a Z-basis
w_1,...,w_r of Gamma with Gram--Schmidt vectors v_j and lengths s_j>0.
Write P for orthogonal projection onto U-perp. For R>=0 define the finite set

\[
 C_R=\{z\in\mathbb Z^n:\|Pz\|\le R,
       -\tfrac12\le\langle z,v_j\rangle/s_j^2<\tfrac12\ (1\le j\le r)\}.
                                                               \tag{1}
\]

Each class in Z^n/Gamma has exactly one representative satisfying the interval
constraints. To construct it, process j=r,...,1 and subtract
floor(<z,v_j>/s_j^2+1/2) w_j. This changes the j coordinate by that integer and
does not change any later coordinate. For uniqueness, the largest nonzero index
of a difference sum a_j w_j would give two j coordinates differing by a nonzero
integer within the same half-open unit interval, which is impossible.
All representatives in (1) satisfy

\[
 \|z\|^2\le R^2+\tfrac14\sum_j s_j^2,                         \tag{2}
\]

so the set is finite. Its ambient real cylinder has volume
V_(n-r) R^(n-r) product_j s_j. This volume is not an integer point count.

Let H=Z^n/L and H'=PZ^n/PL. The induced map H onto H' has kernel
(Lambda+L)/L, of order k=[Lambda:Gamma]; in particular h=|H|=k|H'|.
For c in H put n_c=#(C_R intersect c). For c' in H' let n'_c' count the
distinct points p in PZ^n with ||p||<=R and class c' modulo PL. Then

\[
                         n_c=n'_{f(c)}.                         \tag{3}
\]

Indeed, fix p in the latter class. There exists an integral lift z with Pz=p
and label c: begin with any integral lift of p. Its label differs from c by a
kernel element, so adding an element of Lambda corrects the label without
changing p.
Any two lifts with that same projection and raw label differ by
L intersect U=Gamma. The representative construction gives exactly one in C_R.
Conversely every counted representative projects to such a p. Equivalently,
each p has k representatives in C_R, one for each raw label above its projected
label; it does not have k representatives in each raw label.

## Collision identity including group losses

Define N=sum_c n_c, J=sum_c n_c^2, and define N',J' analogously on H'.
Equation (3) gives

\[
 N=kN',\quad J=kJ',\quad
 \frac{\#\{c:n_c=0\}}h=
 \frac{\#\{c':n'_{c'}=0\}}{|H'|},\quad
 \frac{N^2}{hJ}=\frac{(N')^2}{|H'|J'}.                         \tag{4}
\]

There is no k-squared factor in J: each projected class is repeated k times.
For N>0, Cauchy--Schwarz therefore gives the true projected void bound

\[
 b\le1-\frac{N^2}{hJ},\qquad
 J=\sum_{z,z'\in C_R}{\bf1}_{z-z'\in L}.                     \tag{5}
\]

In particular 720 h J<=1000 N^2 suffices for b<=0.280.
Unlike the one-branch inverse, (4)--(5) require neither positive winner heights
nor coprimality. They handle lost labels explicitly.

For the raw graph L(A)={(x,y):x=Ay mod q}, h=q^m and the collision test is exactly
x-x'=A(y-y') mod q. Thus (5) gives one finite integer enumeration for both the
point count and the collisions, with the same raw label space at every flag.

## Applicability to selected shortest vectors

A nonzero shortest vector in a lattice is primitive: a nontrivial integer
multiple would have a shorter divisor. Inductively, if Gamma_j=L intersect U_j,
then PL is isomorphic as a group to L/Gamma_j. A primitive next winner in PL
generates a saturated cyclic subgroup; its full inverse image is
Gamma_j+Z w_(j+1)=L intersect U_(j+1). Hence successively selected shortest
vectors, lifted to L, form the required basis of Gamma. Their Gram--Schmidt
lengths are the selected projected lengths. Appending coordinates between
selections preserves this assertion: an element of the final graph in an
earlier supported span has zero later coordinates, so its graph equation is
the earlier prefix equation. No randomness is used in this argument.

For the incoming state at draw i in the current restart, n=504+i and r=i-1,
so the transverse dimension in (1) is 505. Use the actual smaller radius
defining b_i. For every design the certificate is now

\[
                  720 q^{400} J_i\le1000 N_i^2.                \tag{6}
\]

The remaining history estimate can be bounded by the probability that (6)
fails at some i=14,...,404. This is a sufficient event, not an equivalence.
The selected cylinder C_R depends on A, as does its radius. Therefore one may
not assign a factor q^(-400) to each of its points as if the candidate set were
fixed independently of A. Equations (1)--(6) resolve representative multiplicity
and group-loss bookkeeping, but leave this dependence and the numerical bound open.

## Verification scope

The follow-up [conditional collision law](wall1_flag_collision_law.md) fixes a flag
and derives exact moments under its containment equations. It gives a weighted
union-bound reduction, but does not evaluate that sum for selected histories.

Run `python3 docs/research/scripts/wall1_flag_occupancy.py`. Rational enumeration
checks (1)--(5) for rank-one and rank-two flags in dimensions two and three,
including k>1, skew bases, and half-open boundaries. These checks do not establish
the required high-dimensional probability estimate. The general argument above
is a paper proof and is not yet Lean-formalized.
