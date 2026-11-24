# Exact quotient law with frozen kernel and syndrome image fixed

This identifies the residual random map for actual quotient labels after
rank loss. Fixing both the kernel and its syndrome image preserves a uniform
quotient map subject to explicit linear constraints. It does not preserve
uniformity after imposing the actual shortest-selection inequalities.

## Independent output components

Let A:W->V be uniform linear over F_q, with dim V=m. Write
sigma_A(x,y)=x-Ay on V direct-sum W. Fix subspaces F subset E in that space
and S subset V. Consider the event

    ker(sigma_A restricted to E)=F,  sigma_A(E)=S.       (1)

Choose a deterministic splitting V=S direct-sum Q, and write A=(A_S,T)
and x=(x_S,x_Q). The two components A_S,T are independent uniform maps.
Event (1) factors exactly into

    T y=x_Q for every (x,y) in E,                       (2)
    x_S-A_S y on E has kernel F and image S.            (3)

Condition (2) involves only T and condition (3) only A_S. Whenever (1)
has positive probability, T is therefore uniform among the solutions of
(2), independently of the conditioned A_S. The quotient label of a candidate
(x,y) is x_Q-Ty. After eliminating the input constraints in (2), its residual
map has output dimension m-dim S, not m.

This applies to a fixed rational frozen space U: put Lambda=U intersect Z^n
and use E=Lambda/qLambda and F=Gamma/qLambda, with the arithmetic prefilter
q(U intersect Z^n) subset Gamma. The exact intersection condition from
[flag saturation](wall1_flag_saturation.md) is the kernel condition in (1).
The actual marked quotient is V/S. Thus fixing S resolves the quotient
identification needed in the
[scalar collision certificate](wall1_scalar_collision_certificate.md).

## Exact weight of a fixed image

Put e=dim E, f=dim F, t=dim(input projection of E), a=e-t. Positive
probability requires that F be graphic (its input projection is injective),
dim S=s=e-f<=m, and S contain the output subspace E intersect V. Conversely
these conditions suffice. Under them,

    Pr((1)) = q^(-((m-s)*t+s*f))
                * product_(l=1)^(t-f) (1-q^(-l)).      (4)

To prove this, S containing E intersect V makes (2) consistent, with input
rank t, so its probability is q^(-(m-s)*t). Projection to S direct-sum W
is injective on E: any vector in its kernel would be a pure output vector
of E outside S. Requiring (3) to kill F costs q^(-s*f). In the remaining
S-component, the fixed pure-output subspace has dimension a, and t-f=s-a
independent random images must complete it to S. Their successive full-rank
probabilities multiply to product_(l=1)^(t-f)(1-q^(-l)). This is exactly the
earlier saturation argument in output dimension s.

Every s-dimensional S containing E intersect V has the same weight (4).
There are Gaussian-binomial(m-a,s-a;q) such images. Summing (4) over them
recovers

    Pr(ker(sigma_A|E)=F)
      =q^(-m*f)*product_(j=0)^(t-f-1)(1-q^(a+j-m)),     (5)

the existing fixed-kernel saturation weight. Empty products are one.
Impossible dimension or consistency cases have probability zero; do not
evaluate (4) as a positive weight for such a case.

## What this permits and what remains

Within each fixed (E,F,S) stratum, fixed candidate quotient-label collision
probabilities use the ordinary conditional residual-map rank formulas with
m-s outputs. In particular the nonzero scalar collision probability is
still a difference of a one-system and a two-system probability, now in
the correct quotient. Conditioning on exact saturation changes the outer
weight (4) but does not further tilt this quotient map inside that stratum.

This does not contradict the earlier saturated raw-label collision formulas:
those did not fix S, and raw-label equality is a different event. Nor does it
justify a common uniform-map law after averaging over different S, whose
quotient coordinate maps differ.

The inequalities that make a proposed flag the actual sequence of shortest
winners can couple A_S and T. They have not been removed by the splitting.
For fixed geometry and a fixed candidate set, (2)--(4) supply an exact
disintegration to which those inequalities can be added. Bounding their
aggregate over selected histories at width506 remains open. No new
production failure probability or completed BKZ proof follows.

## Verification

### Actual shortest selection can tilt even one fixed stratum

Take q=3 and a uniform column A in F_3^8. In physical Euclidean coordinates
let L_A={(x,j) in Z^8 direct-sum Z:x=Aj mod3}. Select the shortest nonzero
vector by squared norm followed by signed ambient lexicographic order.
The vector w=-3e_1 is always available and primitive in L_A.

Its proposed frozen space gives E=span(e_1), F=0, S=span(e_1) for every A,
with Gamma=3Z e_1. Thus the stratum in (1) has probability one. The quotient
map is the column T=(A_2,...,A_8), uniform in F_3^7 before selection.
Nevertheless,

    w is selected iff all eight entries of A are nonzero.   (6)

If A has at most seven nonzero entries, the centered height-one vector has
squared norm at most8 and beats w. If all entries are nonzero, the minimum
squared norms at heights +/-1,+/-2,+/-3 are respectively9,12,9. Heights of
larger magnitude exceed9. At height zero the nonzero lattice vectors have
minimum squared norm9. Of all norm-three vectors, -3e_1 has the smallest
possible first coordinate and therefore wins every tie. This proves (6).

Let Sel denote that selection event. Its likelihood within the uniform
quotient law is

    alpha(T)=Pr(Sel | T)=(2/3)*1_{T in {1,2}^7}.

Thus Pr(Sel)=(2/3)^8=256/6561. Conditional on selection, T is uniform on
{1,2}^7, with128 outputs instead of2187. Its total variation distance from
the original uniform quotient law is2059/2187. The maximum density ratio
is2187/128. These are exact finite probabilities, not production estimates.

This example uses an actual primitive shortest winner and a fixed kernel
and image, rather than an arbitrary postselection event. It rules out
extending the uniform quotient law to shortest selection without an extra
argument. For any fixed stratum and quotient statistic G the correct
unnormalized contribution is

    E[1_Sel G(T) | stratum] = E_T[alpha(T)*G(T)].         (7)

If Pr(Sel | stratum)>0, divide (7) by that probability for the selected
conditional mean. Dropping alpha or replacing it by its average generally
changes the result. In this example G=1_{T in {1,2}^7} has selected mean1,
whereas its unselected mean is128/2187. Independence would underestimate
the joint contribution by the factor2187/128.

The checker `scripts/wall1_fixed_quotient_selection.py` exhausts all6561
columns with a complete shortest-vector search through the radius supplied
by w. Exactly256 select w, and each of128 selected quotient outputs occurs
twice. The characterization and probabilities received independent review.
This small-modulus, width9 example does not refute the width506 target;
it specifies which selection likelihood remains to be controlled there.

### Short-candidate collision counts need not improve after selection

The same example also tests the direction of selection bias for the
collision certificate itself. In retained coordinates (x_2,...,x_8,j),
the lattice is M_T={(x,j):x=Tj mod3}, inside K=Z^8, with quotient F_3^7.
Put b=(1,1,1,0,0,0,0), d=(0,0,0,1,1,1,1), and choose two fixed points

    z1=(b,0),  z2=(d,-1).

Their squared norms are3 and5, and quotient labels are b and d+T. On
selected histories the retained minimum squared is8: centered height1
has norm squared8, height2 has11, and horizontal or larger-height vectors
have squared norm at least9. Thus R^2=5, one signed height, and c^2=7 obey
R^2+1<c^2<s_old^2. The witnesses lie in a nontrivial next-step range.

After discarding zero labels, the unweighted counts are exactly

    N=2-1_{T=-d},
    J=N+2*1_{T=b-d},
    C_sc=N+2*1_{T in {b-d,-b-d}}.

The two collision values of T are fully nonzero; the zero-label value is
not. Therefore the uniform and selected means respectively are

    E J=2+1/2187,       E[J | Sel]=129/64,
    E C_sc=2+3/2187,    E[C_sc | Sel]=65/32.

Both increase. Equivalently Cov(alpha(T),J(T)) and
Cov(alpha(T),C_sc(T)) are strictly positive under the unselected uniform
quotient law. There is no universal negative-covariance shortcut for these
fixed short-candidate counts.

The count N also changes, so the separate increases alone do not establish
what happens to a ratio. The checker evaluates the complete certificate
as well. At q3 the sign quotient is trivial and r=0, giving

    B(T)=2*N(T)^2/(2186*C_sc(T)).

For these two candidates B is exactly their signed-height witness coverage
among nonzero marks. Its unselected mean is1457/796797 and its selected
mean is127/69952, which is strictly smaller. These are averages of the
per-state ratios, not ratios of average counts. The actual full-ball coverage
can be larger; this does not assert an increase in actual failure probability
or refute the production target. Independent review and complete finite
enumeration verify the corrected candidate geometry and all counts.

### Fixed-stratum enumeration

Run `python3 docs/research/scripts/wall1_fixed_quotient_law.py`. It enumerates
all212 subspaces E of F_3^4 and all81 maps A:F_3^2->F_3^2, grouping them
by their actual F and S. It checks support equality and constant multiplicity
of the quotient map, including zero-dimensional quotients. The general
factorization proof received independent mathematical review.

All2709 nonempty (E,F,S) strata pass the conditional-uniformity and exact
weight checks. For1629 fixed (E,F) cases the possible images are exactly
the admissible S, have equal weights, and sum to (5). The checker also
includes an explicit difference that is nonzero as a raw syndrome but
vanishes in the quotient. The factorization and mass formula both passed
independent mathematical review; the complete checker was rerun successfully.
