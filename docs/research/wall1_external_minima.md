# External support and the second lattice minimum

This refines Part 295's support argument in the existing two-relation
Fourier envelope. It does not close the residual probability target.

Let E = 2 ceil((t+1)/2). Any short integer representative whose reduction
is outside the first circuit line has squared norm at least E: it has
at least t+1 nonzero coordinates, and its coordinate sum is zero, so its
squared norm is even. The existing cutoffs ensure that a sum which is zero
modulo q is zero over the integers.

Use the saturated lattice in the real span of short representatives,
as in Part 283. In rank two its reduction is the full two-dimensional
code. A lattice basis therefore cannot have both reductions on the first
circuit line. For a Gauss-reduced basis u,v, write x=||u||^2,
y=||v||^2, and d=<u,v>. Then x<=y and |d|<=x/2. At least one of u,v
is outside that line, hence y>=E. The perpendicular height satisfies

    y-d^2/x >= y-x/4 >= 3y/4 >= 3E/4.

In the class with no norm-four representative, x>=6 and y>=6. Its short
Gaussian sum is consequently bounded by

    theta(6 alpha) theta((3/4) max(6,E) alpha).

If t>=4 and a norm-four representative exists, it must lie on the first
circuit line. Take it as the shortest reduced basis vector, so x=4.
The other vector is outside the line and y>=E. In the exactly-one-short-line
class y>=6 as well. Its height is at least max(5,E-1), giving

    theta(4 alpha) theta(max(5,E-1) alpha).

For a short span of dimension zero or one, the same bounds remain valid:
the actual Gaussian sum needs at most the first theta factor, and the
second factor is at least one. Saturation and all cutoff, long-vector,
and periodic errors are those of Part 283 and remain in the implementation.

## Interval evaluation

The size-fifteen full residual envelope has weighted log10 approximately
7.62645 (previously 7.65399). The diagnostic excluding double-short anchors
has weighted log10 approximately 4.82972 (previously 6.45290). In that
diagnostic, rank-eight girth-three is no longer among the five largest
strata; rank-seven girth-four now dominates. The diagnostic excludes an
event class and is not a bound for the full residual.

These are improvements to upper envelopes, not measurements or lower
bounds on the actual error. The required residual target remains unproved.
The support and reduced-Gram checks are exact finite regressions; this
argument has not been formalized in Lean.
