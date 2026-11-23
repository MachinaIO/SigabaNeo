# A uniform ball-constrained affine-slice completion bound

Let q be odd and let U be any affine d-dimensional subspace of F_q^k.
For a residue vector y let [y] be its coordinatewise centered integer lift.
Then, for every R>=0,

    #{y in U : ||[y]||<=R}
      <= min(q^d, V_d*(R+sqrt(d)/2)^d) =: M_d(R,q).

For d=0 use M_0=1. This is uniform over U, including adaptively chosen
subspaces once they are fixed. It makes no random-orientation assumption.

## Proof

The direction space of U admits a set of d coordinate pivots on which
projection is injective. The same projection is injective on its affine
translate U. Centering commutes with coordinate projection and deleting
coordinates cannot increase the Euclidean norm. Thus the points in question
inject into integer points of the d-dimensional radius-R ball (also inside
the centered residue cube). There are at most q^d such residue vectors.

Place a closed unit cube centered at each of these integer points. Their
interiors are disjoint, and each cube is contained in the radius
R+sqrt(d)/2 ball by the triangle inequality. Comparing volumes proves the
second bound. Boundary overlaps have zero volume. This argument does not
replace modular independence by real independence.

## Use in the current fixed raw-ball cover

Every candidate input has a centered lift with norm at most the full raw
ball radius R: center its integer representative coordinatewise, then delete
its output coordinates. For augmented input rank r, the compatible affine
slice has dimension r-1. Once an independent basis and its images are fixed,
each additional dependent input therefore has at most M_(r-1) choices.
Its incidence probability is at most one conditional on those data, just as
in the existing q^(r-1) completion argument. Applying this successively to
k redundant positions gives M_(r-1)^k, rather than q^((r-1)k).

This replacement applies only to free *input completion* factors. It does
not replace q powers counting coefficient charts, modular layers, or
probability normalizers. It is also distinct from a bound on the occupancy
of a selected projected cylinder; no such bridge is claimed here.

## Concrete size and limitation

At draw14, R is about2933.437 and q=3329. The volume bound first improves
q^d at d=10. The log10 ratio per completed point is approximately
-0.14046 at d10, -0.53060 at d12, -1.50258 at d16, and -2.68039 at d20.
For d<=9 the implemented minimum keeps the old q^d bound.

Thus this elementary uniform geometry can tighten high-rank completions,
but it does not give the hundreds of orders needed by the largest current
high-order envelopes. Stronger estimates must retain additional simultaneous
ball constraints or exploit average geometry of the basis; replacing a
selected span by a random independent span is not justified.

The executable checker verifies coordinate injection and the exact centered
pivot-ball count for every affine plane over F3 and F5 in three coordinates,
for six squared radii. Its diagnostic evaluates the volume formula with the
existing outward interval geometry constants. These finite tests accompany
the general proof above; they are not a Lean formalization or a complete
BKZ probability certificate.
