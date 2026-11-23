# Three-row codes over orthogonal and shared-point planes

This extends Part 293's fixed-plane argument to the other two short-anchor
types. It sharpens the two-new-position crossing witness; larger crossings
and the complete residual budget remain separate obligations.

## Orthogonal six-point plane

After coordinate signs and permutations, take

    a=(1,1,-1,-1,0,0), b=(1,-1,0,0,1,-1).

Both squared lengths are four and their inner product is zero. For an
integer old vector v, with x=<a,v>, y=<b,v>, its squared projection onto
the orthogonal complement is

    D(v) = (4||v||^2-x^2-y^2)/4.

The numerator is a nonnegative integer and cannot be one modulo four,
since a sum of two squares is never three modulo four. Therefore positive
D(v) is at least 1/2. The plane is saturated: exclusive unit coordinates
recover integral coefficients for any integer vector in it.

## Shared seven-point plane

Coordinate sign changes give

    a=(1,1,1,1,0,0,0), b=(1,0,0,0,1,1,1).

Their Gram matrix is [[4,1],[1,4]], with determinant 15. For v=(v0,...,v6),
write S1=v1+v2+v3 and S2=v4+v5+v6. Direct orthogonal decomposition gives

    D(v) = (1/3) sum_(i<j in each triple) (vi-vj)^2
           + (3v0-S1-S2)^2/15.

If a triple is nonconstant, its squared differences sum to at least two,
so D(v)>=2/3. If both are constant, the second numerator is divisible by
nine. Thus D(v)>0 implies D(v)>=3/5. The zero case consists exactly of
integer combinations of a,b, also proving saturation. No affine sum
condition is used in either projection bound, so sign changes are harmless.

## The third height and complete Gaussian bound

A crossing relation with two new positions produces a three-dimensional
code whose independent third direction is nonzero in both new positions.
It has no weight-two word. With a short cutoff L, adjoining two independent
short representatives to a,b would produce a nonzero four-minor divisible
by q. Its volume is at most sqrt(det Gram(a,b))*L^2, less than q at
L=28 (orthogonal) and L=29 (shared), for q=3329. All short representatives
therefore span at most three real dimensions.

As in Part 293, saturation has index less than q and reduces into the
three-row code. Its rank-three covolume is less than q, so its reduction
has rank three. The primitive old plane extends to an integer lattice
basis. The third basis vector reduces independently of the old plane.
Its old projection is nonzero: otherwise subtract an integer old-plane
vector to obtain a forbidden weight-two codeword. Including the two
new coordinates gives third squared height >=5/2 or >=13/5, respectively.

The short Gaussian factors are therefore

    theta(4 alpha)^2 theta((5/2) alpha),
    theta(4 alpha) theta((15/4) alpha) theta((13/5) alpha).

Add exp(-L^2 alpha/2) theta(alpha/2)^3 for all long representatives,
and retain the full positive periodic expansion. In H=8 or 9 positions,
put r=H-3 and beta=r*N/(2*H*R^2). Multiply the one-coordinate Gaussian
bound to the Nth power by exp(H*beta*R^2)/q^(r*m). These normalized
joint bounds replace A*K_2 only when smaller in Part 297's cover.

Validation: 15,625 exact orthogonal and 78,125 exact shared-plane projection
and saturation checks, integer cutoff inequalities, and the full cumulant
regressions. These support the paper derivation; this is not a Lean proof
or a proof of the still-open residual and selected-history estimates.

The full size-fifteen residual weighted log10 decreases from 6.35668 to
1.94693, a factor of about 25,700. Orthogonal refinement alone leaves the
displayed value unchanged; the shared-plane refinement removes the
dominant two-new-position shared-anchor contribution. The remaining
full envelope is close to the no-double-short diagnostic and is dominated
by rank-seven girth-five. It still exceeds the residual target by many
orders of magnitude. Larger sizes and selected histories are unresolved.
