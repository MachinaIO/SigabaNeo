# Rank-five triangles: a three-dimensional short-code bound

This paper calculation closes the last size-fourteen class left by Part 292.
The complete admitted transfer through size fourteen is below 5.396e-13.
Size-15--24 residual components and later selected histories remain open.
This is not a complete draw-14 probability bound or a BKZ proof.

## The fixed plane and its projected integer minimum

After permutations and sign changes, the two old relation rows are
```
a=(1,1,-1,-1,0,0,0,0), b=(0,0,1,1,-1,-1,0,0).
```
Their integer plane P is saturated, has squared covolume 12, and has squared
Gram--Schmidt lengths 4 and 3. Indeed integer vectors in P have constant
coordinates on the three old pairs, with pair constants summing to zero;
they are integer combinations of a,b.

For an integer six-vector v, its squared distance to the old plane is
```
D(v) = (1/2) sum_(i=0)^2 (v_(2i)-v_(2i+1))^2 + (sum_i v_i)^2/6.
```
If D(v)>0, then D(v)>=2/3. When the differences all vanish, the nonzero total
sum is even and has absolute value at least two. Otherwise, the sum of the
differences has the parity of the total. An odd total contributes at least
1/2+1/6; an even total with nonzero differences contributes at least one.
No affine coordinate-sum assumption is used. This is necessary because the
sign change for oriented-difference anchors need not preserve the all-ones
affine normal.

## Short representatives of the three-row code

Part 291 gives a third relation using two new positions and a=2,3,4 old basis
positions. Both new coefficients are nonzero. Its three-row code C over
F_3329 has dimension three and no weight-two words, since the input positions
are distinct; the residual class in fact has girth four.

Take centered integer representatives and cutoff L=30. Two short vectors
independent modulo P, together with a,b, would have four-volume at most
sqrt(12)L^2<3329. Every nonzero four-minor is divisible by 3329 because the
modular rank is three, a contradiction. Thus all short representatives span
at most three real dimensions.

If that span has dimension three, saturate its integer lattice. The index
over a,b and one short independent vector is at most sqrt(12)L<3329, hence
invertible modulo 3329. The saturation therefore still reduces into C.
Its covolume is less than 3329, forcing its reduction to have rank three:
otherwise every three-minor of a lattice basis would be divisible by 3329.
Since P is saturated, a,b extend to a basis of this lattice.

The third basis vector c reduces independently of P, so both its new
coordinates are nonzero modulo 3329 and hence nonzero integers. Its old
projection cannot lie in P: subtracting an integer combination of a,b would
produce a weight-two word. Its squared perpendicular height is therefore
```
D(c_old)+c_6^2+c_7^2 >= 2/3+1+1 = 8/3.
```
Iterated shifted Gaussian summation bounds the short sum by
theta(4 alpha) theta(3 alpha) theta((8/3)alpha). If the short span is only P,
the same bound remains valid since the third factor is at least one.

For the tail, choose three independent coordinate functionals on C. Dropping
the other factors and extending the centered coordinate sums to Z gives
S_C(alpha/2)<=theta(alpha/2)^3. Consequently
```
S_C(alpha) <= theta(4 alpha) theta(3 alpha) theta((8/3)alpha)
             + exp(-450 alpha) theta(alpha/2)^3.
```
No long representatives are discarded. The reasoning applies to all five
signed triangular patterns after their coordinate isometries.

## Ball count and periodic corrections

Set beta=5N/(16R^2), A=pi^2/beta, alpha=A/q^2 and
delta=2 exp(-A/4)/(1-exp(-2A)). The positive Poisson majorant for the Gaussian
Fourier transform is sqrt(pi/beta)(exp(-alpha u^2)+delta) on centered residues.
Expanding eight factors gives the one-coordinate upper bound
```
V=(pi/beta)^4 [S_bound/q^3 + sum_(j=1)^8 choose(8,j) delta^j].
```
Here S_bound is the preceding short-plus-tail bound. Every nonempty periodic
term is retained; its remaining finite-code average is at most one.
The full ball count is at most exp(8 beta R^2)V^N. Divide by q^(5m) on the
eligible rank-five input stratum before dropping restrictions in this count.

Choose the six-point anchor, its pair/sign pattern, the two new positions,
and a old basis positions. There are at most q^a normalized affine third
relations. The eight-point anchor spans rank five, and each of the remaining
six positions has at most q^4 choices. Thus the residual activity is at most
```
choose(14,6) * 75 * choose(8,2) * sum_(a=2)^4 choose(4,a) q^a
 * exp(8 beta R^2) V^N / q^(5m) * q^24.
```

## Result and remaining target

The weighted charge, including known-component mixtures through L_14, is
below 1.151e-28. Adding it to Part 292 proves an admitted transfer through
**all size-fourteen classes** below 5.396e-13. The main
`wall1_factorial_cumulants.py` probe now uses this refined envelope instead
of its generic two-relation bound at size fourteen. Higher-size bounds are
unchanged.

The sufficient open condition is now
```
sum_(h=15)^24 L_h^* U_h + Pr(max_(15..404) b_i>.280) <= 2.4692e-12.
```
The residual starts at fifteen. Only known coefficients through degree nine
can mix with it below degree 25, so admitting size fourteen does not change
those linear coefficients. The condition is still unproved.

Validation: 15,625 exact rational projection identities, including 15,606
positive-height cases; integer cutoff checks; interval assertions for the
new charge and combined budget; and the main cumulant regressions with the
refined bound. The geometric arguments and numerical bounds are not Lean
formalized.
