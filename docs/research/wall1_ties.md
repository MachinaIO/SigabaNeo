# Exact ties in a plain planted quotient

For odd prime q, a horizontal prefix leaving a two-dimensional terminal block cannot have a tie **at the minimum** involving the plant at any irrational squared embedding height. The prefix may be selected adaptively. At unit height, a plain odd-prime example with a three-dimensional terminal block has an uncaptured plant tied at the minimum of a fully reduced basis. In that example an off-line equality survives every change of embedding height.

## A parity exclusion in terminal dimension two

Use the [plain model](usvp_planted.md), with horizontal dimension N=m+n, horizontal lattice H, plant (x,1), and squared embedding height r>0. Fix any horizontal rational prefix plane W of dimension N−1. Its horizontal normal has a primitive integral representative c. In the unit direction c/‖c‖, horizontal projection of H is Dℤ/‖c‖, where D is the positive generator of c·H. Since qℤ^N is contained in H and c is primitive, D divides q. Put a=c·x and C=c·c. In orthonormal terminal coordinates the quotient points are precisely

    ((ja+kD)/√C, j√r),    j,k integral.

The plant has (j,k)=(1,0). A tie with it requires

    (ja+kD)² − a² = (1−j²)Cr.

For irrational r this forces j=±1. After negation take j=1. An off-line tie then requires kD=−2a with k nonzero. As D is odd, D divides a. At this same level the quotient therefore contains (0,√r), strictly shorter than the plant because a is nonzero. This proves the exclusion. In fact the same-level argument holds at every height. Coprimality matters here because it rules out a marked point halfway between the two closest translates.

Consequently for an atomless independent draw of r the joint probability of a horizontal terminal prefix of codimension two and a marked tie at the minimum is exactly zero, for every input law and every prefix selector. No union bound or stability assumption is required. Strictly shorter competitors still count as failures, and this conclusion concerns the metric used for the draw. It gives no transfer of success to r=1.

## A reduced odd-prime example at unit height

Take m=1, n=2, q=5, A=(1,0), error 1 and secret (0,0). Write coordinates in the order (error, first secret, second secret, height). Membership is X+Y−T=0 modulo 5. Take the ordered rows

    w=(0,0,1,0),   v=(0,1,0,1),   h=(1,−1,0,0),   l=(2,2,0,−1).

The plant is u=(1,0,0,1)=v+h. These rows form a basis: after removing the free coordinate, v,h generate the integral kernel of X+Y−T and l has functional value 5. They are size-reduced: w is orthogonal to the other rows, the coefficient of h along v is −1/2, and the coefficients of l along v and h*=h+v/2 are 1/2 and 1/3 respectively.

They are even HKZ-reduced. The unit row w is shortest by integrality. In its complement a nonzero unit vector violates the check, so v of squared length 2 is shortest. After projecting out v, h* has squared length 3/2. Any point involving a nonzero coefficient of l has component of magnitude at least 5/√3 normal to the kernel plane, which survives both projections. Hence h* is shortest in its projected suffix. The last suffix has rank one. This proves full BKZ-3 reducedness, since each restricted block contains its starting projected row and lies inside the corresponding suffix.

No row is ±u. In the terminal block after w, u and v lie on different shortest lines, both primitive by their height coordinate. This failure occurs with probability at least 1/25 for a fully reduced basis selector that chooses the displayed basis on this input and any HKZ basis elsewhere, under uniform A and the fixed planting above. This is an existence statement about selectors. The plant here is short but does not generate the unique ambient shortest line.

Holding the prefix fixed, u and v both have squared length 1+r for every r. To check minimality for 0<r≤1, observe that nonzero horizontal points have squared length at least 2, height ±1 requires a nonzero horizontal part, and at |T|≥2 either the horizontal part is nonzero or 5 divides T. In the latter case the squared length is at least 25r, which is at least 1+r for r≥1/24. More precisely the two lines are shortest exactly on [1/24,1], as (0,0,0,5) and h attain the two competing bounds. Thus even on an open one-sided neighborhood of unit height, changing height alone cannot break this terminal tie with this prefix. Capture and the remaining reduced rows can change under perturbation.

## Outstanding probability

The [fixed-prefix height formula](wall1_embedding_factor.md) makes each comparison affine after clearing its common denominator. For irrational squared height every equality therefore has both integer coefficients zero, simultaneously for all integral prefixes. The example realizes this persistent equality in a plain quotient with a reduced prefix. The rank-one horizontal parity argument excludes persistent *minimal* ties in its stated dimension only. Neither result bounds the selection mass of persistent tied minima for wide blocks with an ambient-unique plant, or of isolated ties at the registered unit height. The success probability and any improved block size for the registered slide output remain open.
