# Four-circuit projections: parity and overlap

For c=4 and t>=4, the only possible norm-four direction is the first
circuit C. Choose its balanced integer representative with entries +/-1.
Let v be the second vector of the reduced saturated short-plane basis.
Write z_i=C_i v_i on the four old positions. Its squared perpendicular
height is

    sum_new v_j^2 + V(z),
    V(z) = sum_i z_i^2 - (sum_i z_i)^2/4.

The old projection cannot be zero: then all z_i equal an integer d,
and v-dC would reduce to an independent code direction with all old
positions zero, excluded by Part 295. For nonconstant integer z,
V(z)>=3/4. Each new position is nonzero, so the height is at least t+3/4.

Suppose further that t is even and the second circuit overlaps C in
three positions. The height is then at least t+2. Indeed, if it were
less than t+2, every new entry would be +/-1; a magnitude at least two
would already increase their squared norm from t to at least t+3.
Their sum is even, and the full affine integer row sums to zero. Thus
sum_i C_i z_i is even.

If V(z)<2, the range of z is at most one: a minimum and maximum at
distance d alone force variance at least d^2/2. Up to an integer
translation, z is therefore a nonconstant binary pattern. Since C is
balanced, its signed sum has the parity of the number of ones. Even
parity forces two zeros and two ones. Neither value occurs exactly once.
But writing v modulo q as a nonzero multiple of D plus a multiple of C
requires exactly one old ratio z_i to equal that latter multiple,
because D misses precisely one old position. This is a contradiction.

The short-plane basis can be taken within the existing cutoff 40;
coordinate sums vanish over the integers as before. Replace the second
theta height in the one-short-direction term by the maximum of its old
bound, t+3/4, and (for even t with overlap three) t+2. All tail and
periodic terms remain. A rank-one short span is still bounded by the
same product since the extra theta factor is at least one.

The finite regression enumerates 6,561 integer old-coordinate tuples.
The argument above supplies the unbounded integer statement; the check
does not substitute for that argument or for Lean formalization.

## Separate first-ball alternative

There are three balanced first-circuit lines. Preserve their full modular
pair-energy count H_2 and apply Part 291's new-group bound J_t uniformly
in the old-dependent target. The coefficient-averaged joint count is at
most (3/q^2) H_2 J_t: the second row has at most q^(t+a-2) choices,
whereas the normalization uses q^(t+a). The implementation also takes
the minimum with this bound. It helps some odd t terms, but did not
improve the displayed full residual before the projection refinement.
This alternative includes all nonzero modular layers.

## Outcome

The full size-fifteen residual weighted log10 decreases from approximately
6.37057 to 6.35668. The diagnostic excluding double-short anchors decreases
from 4.82972 to 1.94692; rank-seven girth-five now dominates that diagnostic.
The difference matters: excluding anchor families is not a bound on the
whole event, and the full envelope still misses the required budget by
many orders of magnitude. Complete admission remains through fourteen.
The later selected-history and full BKZ statements remain open.
