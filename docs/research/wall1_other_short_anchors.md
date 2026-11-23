# Third circuits for the other short anchors

Extend Part 291's covering argument to the two remaining eligible
double-short anchor types: six-point orthogonal pairs (rank four), and
seven-point pairs sharing one position (rank five).

For six positions there are 45 unordered pairs of four-supports covering
all positions. Each admits four pairs of projective balanced sign rows
with zero inner product, giving at most 180 witnesses. For seven positions
there are 7*10 support pairs and nine balanced sign choices per pair,
giving 630 witnesses. Exact enumeration checks both counts. Duplicate
codes are allowed because these are upper bounds on witness counts.

Write (s,k,P)=(6,4,180) or (7,5,630). Let A be the full modular anchor
ball count divided by q^(km). Use the direct orthogonal count plus its
nonzero modular layers, or the shared-point direct count plus its
nonzero modular layers, respectively. These are the existing bounds
from Parts 287 and 288.

If the full support has rank k, bound its completions by

    choose(h,s) P A q^((k-1)(h-s)).

If its rank r exceeds k, fix a basis of the anchor and extend it to a
basis of the connected support. A crossing fundamental circuit exists
by the same complementary-span argument as Part 291. It introduces
t new positions, with 2<=t<=r-k+1, and meets a old basis positions,
where 1<=a<=k and t+a>=4. The anchor and this circuit have rank k+t-1
and nullity three. Put e=r-k-t+1. Their contribution is at most

    choose(h,s) P choose(h-s,t) choose(h-s-t,e)
    * [sum_a choose(k,a) q^(t+a-2)] A K_t mu^e
    * q^((r-1)(h-r-3)).

Here K_t is Part 291's full modular new-group bound divided by
q^(m(t-1)); its proof also applies at t=2. We omit any division for
multiple basis witnesses. If r=h-2, the proper anchor already has the
whole support's nullity two, so all outside positions would be coloops;
connectedness excludes this case.

Every eligible two-short-direction anchor in the girth-four classifier
is triangular, orthogonal, or shared-point. Thus the no-double-short
envelope plus the triangular envelope plus the two new envelopes covers
the entire stratum. The implementation takes the minimum with the
previous full-stratum envelopes; it never uses the excluded-family
diagnostic alone as a full bound.

The new candidate's size-fifteen weighted log10 is about 6.37057,
compared with 7.62645 before this refinement. At size twenty-four it is
about 263.383, compared with 265.609. These remain far above the required
residual budget. All-size-fourteen admission is unchanged, and neither
selected-history control nor the full BKZ proof is complete. This is a
paper argument with exact and interval checks, not a Lean proof.
