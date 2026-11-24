# A chronological shortest-select/project/append check

This connects the [selected multiple-height Gram evaluator](wall1_selected_height_gram.md)
to actual shortest-vector selection and projected geometry in finite
width-three and width-four experiments. It is not a production width506
bound. The first example reveals the old matrix from its winner. The
width-four extension below retains a nontrivial distribution of old matrices
after selection and verifies its exact gated moments.

## Experiment and exact first selection

Take q=7, uniform a=(a1,a2) in F_q², and

    L_a={(x,y,z) in Z³: (x,y)=a*z modulo q}.

Select its shortest nonzero vector v, orienting the first nonzero coordinate
positively and breaking ties lexicographically. Searching all integer vectors
of squared norm at most q² is complete because q*e1 belongs to L_a. Every
selected v in the fixture has norm²<q² and is primitive in Z³, checked exactly.
The corresponding primitivity argument is also elementary: if v=d*w, d>1,
then d<q, so lambda(w)=0 modulo q, contradicting minimality.

Project orthogonally to v-perp, obtaining K=P_v Z³ and M=P_v L_a. Because
v is primitive in Z³ and belongs to L_a, the projection kernel on Z³ is Zv
and all of it is in L_a. Thus K/M is still F_q². In particular the projected
label lambda(P_v x)=lambda(x) is well-defined; no raw-syndrome/quotient-label
substitution is being made after a rank drop.

Append a new unit coordinate using an independent uniform U in F_q²:

    L'_(a,U)={(P_v x,j): lambda(x)=jU}.

Conditioning on the full old state and its selected winner leaves U uniform,
since it was sampled independently. This is an explicit feature of this
finite experiment, not an assertion about reusing an already exposed column.
The appended lattice has dimension three again.

## Complete projected enumeration

Write n=||v||². Each projected point has a unique integer representative x
satisfying

    -n <= 2<x,v> < n.

Subtracting an integer multiple of v puts a representative in this half-open
strip. Primitivity makes two integer representatives with identical projection
differ by an integer multiple of v, proving uniqueness. In this strip,

    ||P_v x||²=||x||²-<x,v>²/n,
    ||P_v x||²<=R² implies ||x||²<=R²+n/4.

Consequently a finite integer ball search followed by these exact rational
inequalities lists every projected point once. Its canonical representatives
need not be symmetric as raw integer vectors, but their projected points are
symmetric and their labels transform correctly under negation.

Use fixed r²=11/2. The old-minimum gate excludes every nonzero projected point
of norm²<=r² with zero label. On it, every short appended vector has height
±1 or ±2, and the horizontal radii are sqrt(r²-1) and sqrt(r²-4). The complete
projected candidate families at those radii therefore characterize the next
strict-long event exactly. The zero fresh mark has its unit vector. The
checker independently searches signed heights -2 through 2 and the larger
projected ball to verify this equivalence, using rational squared lengths.

This fixed radius is not a claim about the production determinant-dependent
radius update.

## Selected moments and complete finite sum

On each proposed winner stratum, impose lambda(v)=0 and exclude every
canonically preceding raw competitor. Add the complete projected old-minimum
gate. Feed these exact positive equations and signed exclusion states to the
multiple-height Gram evaluator. Geometry and candidate data are fixed within
each v stratum. No factorization of the selected likelihood is used.

Separately, enumerate every a, select its actual v, and enumerate every U.
Compare the gated mass, both first moments, every Gram entry, and the optimized
affine square with the rank-equation calculation. All comparisons use exact
rational arithmetic and the joint denominator q^4. Sum the stratum bounds
without normalizing away their masses. Outside the old gate the short horizontal
vector already rules out a strict-long winner, so those histories contribute
zero to this particular tail.

For q=7 there are 49 different first-winner strata for 49 old matrices, all of
which pass this old-minimum gate. All 2401 old/fresh pairs are checked. The
exact next strict-long probability is 568/2401. The selected two-height
optimized upper bound is 24181299040/76256621959; the corresponding height-one
upper bound is 3935436/10326701. Every stratum improves when the second height
is allowed. The upper bound is still not the exact probability.

The 49 singleton strata are a substantial limitation. A selected vector with
nonzero z modulo q determines a=(x/z,y/z); all winners here have that property.
Thus this fixture has chronological selection and nontrivial projected
geometry, but no residual uncertainty in a after selection. Production
selected-collision estimates must handle many remaining matrix degrees of
freedom, hundreds of projections, and the actual radius law. None of those
requirements is supplied by this finite check.

## Reproduction

Run `python3 docs/research/scripts/wall1_chronological_height_gram.py`.
The script uses the existing exact mixed-gate incidence and affine-square
optimizers. It checks shortest-vector search completeness, primitivity,
projected representative enumeration, both height families, and direct
map/mark expectations. These are executable finite checks, not a Lean
formalization or completion of the BKZ proof.

Independent review reran the checker and verified the chronological equations,
projection kernel, strip completeness, fresh-column law and joint normalization.
Both enumeration routes share the projected-ball routine; its completeness
rests on the strip argument, not an independently implemented lattice enumerator.


## Residual old-matrix uncertainty after chronological selection

The `--residual` mode uses q=5 and a uniform 2-by-2 matrix A, with

    L_A={(y,z) in Z² x Z²: y=A z modulo 5}.

There are 625 equally likely old matrices. Select the exact shortest
canonically oriented/tie-broken v, then project onto v-perp and append an
independent uniform mark U in F_5². The initial and appended lattices both
have dimension four; the retained projected lattice has dimension three.
The test radius is fixed at r²=9/2, so heights ±1 and ±2 still exhaust
possible short nonhorizontal vectors. The two horizontal squared radii are
7/2 and 1/2. The same rational strip proof works in Z^4.

Within each winner stratum, initialize the rank model with the containment
lambda(v)=0. Its returned probability includes this containment mass once.
Exclude every canonical predecessor and then every nonzero projected point
of norm²<=9/2 with zero label. Additional redundant v equations reduce to
zero in this model and do not multiply the containment mass again.
Families remain fixed on the v stratum, while labels vary across its old
matrices. In particular, neither the conditional law nor the candidate
multiplicities are replaced by values at a representative matrix.

The first selection gives 46 winner strata with sizes ranging from 6 to 25.
One nonzero input-vector containment equation alone leaves 25 old matrices;
strictly smaller winner strata therefore retain genuine extra selection
conditions. After the projected old-minimum gate, all 46 strata still
contain multiple old matrices: 24 have size 6, eight have size 8, twelve
have size 10, and two have size 16. These sizes sum to 360 surviving old
histories. Thus the singleton limitation of the width-three example is
removed in this finite extension.

The checker evaluates all 25 fresh marks for each of those 360 histories,
for 9000 direct projected-graph checks. The rank-based joint mass, first
moments, full Gram matrix, and optimized affine-square expectation agree
with direct enumeration on every stratum. The normalization is 5^6=15625,
including all 625 old matrices and all 25 fresh marks; it is not the number
of surviving pairs. The other 265 histories have a short horizontal
projected vector and therefore zero contribution to the next strict-long
event at this radius.

The exact next strict-long probability is 176/15625. Summing the selected
two-height optimized certificates gives 1902132907/32901859375. The
height-one certificate is 5807299424/96436484375; allowing the second height
strictly improves 20 strata. All these are unconditional joint sums under
the specified uniform initial-matrix experiment. They do not presume that
the selected strata are equally likely.

Run `python3 docs/research/scripts/wall1_chronological_height_gram.py --residual`.
The default width-three run was rerun after generalizing the code and its
values are unchanged. This extension verifies a nontrivial selected old-map
mixture, rather than just a fixed matrix after selection. It still includes
only one shortest selection and one fresh append, a fixed radius, tiny
modulus and dimensions, and finite enumeration. It does not bound the
hundreds of steps or high-dimensional selected moments required for the
BKZ goal.

Independent review checked containment normalization, the residual selection
law and projected enumeration, and separately enumerated the 625 old maps
to verify all surviving stratum sizes. The parent run completed the 9000
fresh-mark cases and all exact moment comparisons successfully.

## Determinant-dependent radius in the residual experiment

The `--production-radius` mode replaces the fixed test radius in the
width-four residual experiment by the same dimension-dependent formula used
in the production long-winner criterion. This name denotes the radius rule,
not a production-sized computation.

For a primitive first winner v with n=||v||², projection gives
D=det(P_v L_A)=q²/sqrt(n). The next unit-height append preserves this
determinant. In appended dimension d=4, let

    V_4=pi²/2, g=(D/V_4)^(1/4), r=1.1g,
    r²=(121/100)*(D/V_4)^(1/2).

The checker recomputes r² for every winner stratum. Sixty-digit outward
interval arithmetic certifies strict rational lower and upper endpoints.
A floating midpoint merely proposes these endpoints; the strict interval
comparisons certify them independently. For j=0,1,2, the complete projected
point sets at squared radii lower-j² and upper-j² are compared exactly.
Their equality guarantees that the intervening true irrational radius has
exactly the same old-minimum gate and candidate families. Thus the rational
upper endpoint used by direct enumeration does not add boundary witnesses.

All 46 winner strata have squared radius strictly between
3642570737/2000000000 and 13617284283/5000000000. In particular, 1<r²<4:
the unit witness at zero mark is valid, while height two cannot contribute.
The absence of multiple-height improvement in this mode is a geometric
restriction of this tiny experiment, not a claim about the width506 regime.

Exactly 600 of the 625 old matrices pass the projected old-minimum gate,
spread across all 46 nonsingleton strata. The 15000 surviving old/fresh
pairs are enumerated, and the selected rank-based moments and optimized
square agree with direct evaluation. The remaining 25 old histories have
a short horizontal witness and zero contribution to the next strict-long
event. With denominator 5^6 retaining all old histories and fresh marks,

    Pr(next shortest length >1.1g) = 10432/15625.

In this finite experiment the optimized affine-square upper certificate
also equals 10432/15625. This equality is checked against the exact event,
not inferred from general moment optimality. It does not imply equality
or concentration in higher dimension.

Run `python3 docs/research/scripts/wall1_chronological_height_gram.py --production-radius`.
Independent review verified the determinant identity, interval endpoints,
set-equality argument, and dimension convention. The parent run completed
all exact moment/event comparisons. This connects chronological selection,
residual old-matrix uncertainty and the determinant-based radius in one finite
step. Repeated selections and the width506 quantitative bounds remain open.

The [repeated marked-transition checker](wall1_repeated_marked_transition.md)
tracks exact rational basis metrics and quotient rank changes across several
fresh-column transitions. It verifies mechanics, not the unresolved tail bound.
