# The eight-position plane of Gram determinant twenty

This treats the norm-four/norm-six anchor left in Part 313's determinant
20 stratum. It is a paper-level refinement of the component cover, not a
proof of the remaining component budget or the adaptive BKZ history law.

## Integer projection bound

Coordinate signs and permutations put the two short rows in the form

    a=(1,1,1,1,0,0,0,0), b=(1,1,0,0,1,1,1,1).

Their Gram matrix is [[4,2],[2,6]]. The plane is primitive: an exclusive
coordinate of each row recovers its coefficient integrally. For an integer
vector v, write S0=v0+v1, S1=v2+v3, S2=v4+v5+v6+v7. Its squared orthogonal
projection off this plane is exactly

    D(v) = ((v0-v1)^2+(v2-v3)^2)/2
           + sum_(4<=i<j<8) (vi-vj)^2/4
           + (2S0-2S1-S2)^2/20.

If the last group is nonconstant, its within-group variance is at least
3/4. If both pairs are nonconstant, their variance is at least one. If
exactly one pair is nonconstant and the last group is constant, an even
nonzero pair difference contributes at least two. An odd difference
contributes at least 1/2, while 2S0-2S1-S2 is two modulo four and contributes
at least 1/5. Finally, if all groups are constant, that numerator is a
multiple of four, and a positive D is at least 4/5. Consequently

    D(v)>0 implies D(v)>=7/10.

Equality is attained, for example, by v=(1,0,0,0,0,0,0,0).
The zero case has group constants p,q,r with p=q+r, precisely the integer
span of a,b. These arguments apply to every integer v; enumeration on
{-1,0,1}^8 is a regression check of the formula and its sharp constant.

## Short-pair counting

Fix the support of the norm-four row. There are three balanced sign lines.
Enumerate balanced norm-six lines, nonzero on the other four positions,
with inner product of absolute value two. There are 96 pairs of lines.
Each plane has exactly two such norm-six lines: for dot product two,
they are b and b-a, up to sign. Indeed the squared length of ma+nb is

    4(m+n/2)^2+5n^2.

Thus the only norm-four line is a, and the only norm-six lines have
n=+/-1 and m=0 or -n. Primitivity ensures these are all integer vectors
in the plane. There are 48 planes for each four-support, hence
choose(8,4)*48=3360 anchors on eight labeled positions. Canonical modular
enumeration verifies multiplicity two at q=7,17,3329; retaining all 96
pairs instead gives the valid but weaker count 6720.

## Third relation and Gaussian envelope

Fix an independent six-position basis X of the anchor. A crossing
fundamental relation has t new positions and a nonzero old part supported
in X. This old part cannot belong to the old relation plane, by independence
of X. The fixed-plane short-code argument therefore gives third squared
Gram--Schmidt height at least t+7/10. As in the other short-anchor covers,
this applies to t=1 for a dependent extension and to t>=2 for a crossing.

Use cutoff L=27: 20 L^4 < 3329^2. The determinant argument excludes four
independent short lifts and the primitive old plane extends to a basis
of the saturated three-dimensional short lattice. Reduction has full
rank because its covolume is less than q. The short Gaussian product is

    theta(4 alpha) theta(5 alpha) theta((t+7/10) alpha).

Retain the long tail exp(-L^2 alpha/2) theta(alpha/2)^3 and the complete
positive periodic expansion. For the two-row anchor alone, use cutoff40
and the two theta factors. The implementation uses H=8+t, code dimension
three (two at t=0), input rank H minus code dimension, and
beta=rank*N/(2H R^2). It normalizes the full Gaussian ball envelope by
q^(rank*m), including exp(H beta R^2).

The component cover is the existing short-anchor construction with
anchor size eight and rank six. It retains dependent extensions,
crossings with every permitted t, quotient loops and parallel classes,
and the marked-pair alternative. Crossing completions divide by e+1
only where the coloop-free rank-e quotient supplies that many bases.
No such divisor is used for the canonical marked-pair cover.

For girth-four supports, split into those with two norm-four relations,
those with an eligible determinant-twenty anchor, and those with neither.
The first family retains the existing triangular/orthogonal/shared covers;
the second uses this envelope. Only in the last family may the determinant
20 summand be removed from Part 313's two-relation estimate. Other strata
retain their old upper bounds. Overlap between families is harmless since
all charges are positive. This split does not discard an exceptional case.

## Outcome and remaining target

The cumulant transfer through fifteen is bounded by 1.654e-12; the main
probe asserts this cap. Together with the existing reference and error
bound 9.131e-13, a sufficient remaining condition is

    sum_(h=16)^24 L_h^* U_h + Pr(max_(i=15)^404 b_i>.280) <= 1.3548e-12.

The allocation sums to 3.9219e-12, strictly below 3.922e-12. The condition
is still unproved. Here h indexes component size and i indexes later
selected draws; the b_i are the smaller-radius void quantities, not
direct conditional exit probabilities.

The refined size-sixteen decomposition is dominated by (rank,girth)=(6,4),
whose weighted log10 is about 3.53935, followed by (8,4) at 2.19061 and
(5,4) at 0.93470. Thus the determinant-twenty refinement removes the
previous dominant rank-eight contribution but leaves a large low-rank
extension bound. These are positive upper envelopes, not lower bounds
on actual failure probabilities. Improving this low-rank counting and
establishing the adaptive selected-history law remain necessary.

## Part 316: splitting a further norm-four line

The determinant-twenty plane also admits Part 315's exceptional-line
split. In its original balanced coordinates take

    a=(1,1,-1,-1,0,0,0,0), b=(1,1,0,0,1,-1,-1,-1).

The triangle (0,a,b) has circumcenter (3/10)a+(2/5)b, whose squared
distance from each vertex is 9/5. Triangulating the fundamental
parallelogram along a-b and using the barycentric squared-distance
identity proves squared covering radius at most 9/5. This is an
all-real-points argument; no sampling of the parallelogram is used.

Subtract a nearest old-plane lattice point from any integer vector
outside that plane. If its squared orthogonal height were less than
21/5, the resulting integer vector would have squared norm less than
six. The affine condition and q^2>6H make its integer coordinate sum
zero. Its norm is therefore even; girth four excludes norm two, and
being outside the plane excludes zero. It must be a new balanced
norm-four line. Thus absence of such a line gives third squared height
at least 21/5, combined with the old t+7/10 bound by taking their maximum.

For a fixed old basis and t new positions, at most 3*choose(8,4-t)
balanced norm-four lines can occur outside the old plane: all new
coordinates must be nonzero, and each line determines at most one
third code and normalized fundamental relation. Apply the sum of the
exceptional and nonexceptional bounds to dependent extensions,
crossings and marked pairs, retaining the previous bound as an
alternative. All Gaussian tails, modular terms and completion factors
are unchanged. The anchor-only and unmarked parallel bounds are also
unchanged. The restriction is never imposed on an unpartitioned family.

The exact regression now checks 13199 zero-sum integer vectors across
the orthogonal, shared and determinant-twenty planes, plus twelve
exceptional-line counts. It verifies nearest-corner reduction, the
covering-radius bound and the norm-two-or-four alternative. The proof
above and Part 315's code-counting argument cover arbitrary vectors.
