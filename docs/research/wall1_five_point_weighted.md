# Weighted Gaussian count for the five-point short code

The six eligible codes from Part 307 have two balanced norm-four generators
sharing three positions, with inner-product magnitude one. Magnitude three
would yield a weight-two difference and is excluded by girth three. By
coordinate signs, permutations, and a generator sign, each is isometric to

    x0+x1-x2-x3 = 0 (mod q),
    x0-x1+x2-x4 = 0 (mod q).

Coordinate sign changes preserve the centered balls. No affine-normal
invariance is required once we bound the lifted ball count.

## Exact layers and square completion

For one scalar coordinate, put x=x0, z=x2, d=x1-x2, and introduce the
integer layers u,v so that x3=x+d-qu and x4=x-d-qv. This parametrizes all
integer tuples satisfying both congruences, with no layer omitted.

Give x0 weight a, x1,x2 weight b, and x3,x4 weight c. Put A=a+2c and
B=b/2+2c. The quadratic exponent completes exactly to

    2b(z+d/2)^2 + A(x-cq(u+v)/A)^2 + B(d-cq(u-v)/B)^2
      + q^2 [c(u^2+v^2)-c^2(u+v)^2/A-c^2(u-v)^2/B].

The layer term equals

    (q^2/2) [ca/(a+2c) (u+v)^2 + cb/(b+4c) (u-v)^2]

and is at least q^2*lambda*(u^2+v^2), where lambda is the smaller of the
two positive coefficients. Sum successively over z, x, d using the
unshifted-theta upper bound for each shifted Gaussian sum. Sum all u,v
using the layer bound. The one-coordinate kernel is at most

    theta(2b) theta(A) theta(B) theta(q^2 lambda)^2.

## Concrete weights and ball bound

For dimension N and squared ball radius R^2, choose

    a=N/(20R^2), b=11N/(40R^2), c=9N/(20R^2).

All are positive; lambda=ca/(a+2c) is the smaller coefficient. For five
vectors each in the radius-R ball, the weighted quadratic sum is at most
(a+2b+2c)R^2. Thus the full modular ball count is bounded by

    exp((a+2b+2c)R^2)
      [theta(2b) theta(A) theta(B) theta(q^2 lambda)^2]^N.

The count retains all nonzero modular layers. The point weights differ
because the central point participates in a midpoint relation, while the
other four points carry the stronger constraints. This avoids imposing
the same Gaussian penalty on every point. It changes only the two-short-line
five-point contribution; all other coefficient classes remain included.

Validation: 3,125 exact rational square-completion/layer inequalities,
eight full-modular small-ball counts (including small moduli), and exact
classification of all 105 norm-four pairs at q=3329. The actual-parameter
evaluation uses outward intervals. This is a paper derivation and verified
calculation, not a Lean proof or completion of the full BKZ statement.

The full size-fifteen residual weighted log10 decreases from -7.04224 to
-10.00541, about 9.88e-11. Girth-three rank-seven is now below 10^(-24.50);
girth-four rank-seven and rank-eight dominate instead. Size fifteen alone
still exceeds the entire remaining budget by about forty times, and
larger sizes and selected histories have not been closed.
