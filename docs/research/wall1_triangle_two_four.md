# Two-new-position norm-four extensions of the triangular anchor

For each of the five balanced affine triangular patterns a,b on six old
positions, enumerate norm-four rows v on two old and two new positions.
There are choose(6,2)*3=45 witnesses per pattern. With d=<a,b>=+/-2,
x=<a,v> and y=<b,v>, the rank-three Gram determinant is

    D=48-4*x^2+2*d*x*y-4*y^2.

The five exact histograms in `scripts/wall1_triangle_two_four.py` have
componentwise upper bounds {32:6,36:24,44:18,48:6}. Their sum exceeds45
because maxima are taken independently across patterns; this is a safe
union bound, not a claim that any one pattern has54 witnesses.

The old anchor has a unit two-by-two minor; adjoining either unit new entry
gives a unit three-by-three minor. Hence these rows generate the saturated
integer plane, and Gram--Schmidt squared lengths4,3,D/12 are valid.
For each determinant evaluate the complete existing code kernel, including
the cutoff-30 tail and periodic terms. Compare the sum with the earlier
45-times-unrestricted kernel and keep the smaller upper bound.

The family without new norm-four rows and its coefficient count are
unchanged. The shared `weighted_code_bound` call connects this refinement
to both ordinary crossings and marked parallel-class completions. No
completion counts are reduced or discarded. In particular, improving a
raw crossing alone would not establish an improvement in the selected
minimum; the full larger-component calculation is rerun.

This is a finite family refinement, not a complete size17 estimate or an
adaptive BKZ proof. The new classification is not Lean formalized.

## Four equal pair sums for determinant32

For each of the27 determinant32 witnesses across the five affine patterns,
normalize each nonzero column of the three-row relation matrix up to sign.
There are exactly four projective column directions, each occurring twice,
and every three distinct directions have determinant+/-1. These properties
are checked by integer arithmetic in the same classification script.

The unique dependence among the four directions consequently has four
coefficients in {+1,-1}. Sign changes on individual point variables preserve
the centrally symmetric ball. After these sign changes, the relation equations
say that the four pair sums are equal. No division by a nonunit or relaxation
of the modular equations is needed. Over the integers the zero-layer count
is therefore sum_s r(s)^4, where r(s) counts pairs of ball points with sum s.

The existing shifted-ball and layer-cake bound for k pairs gives, for even N,

    sum_s r(s)^4 <= 2^(N+5) pi^(5N/2) (2N)!
                      / ((N/2)!^4 (5N/2)!)
                      * (R^2+5N/16)^(5N/2).

Indeed use r(s)<=2 V_N (R^2+N/4-||s||^2/4)_+^(N/2), raise to the fourth
power, and apply the same shifted-ball layer-cake integral as for three
pairs. Thus this is the k=4 specialization of the already implemented
`equal_pair_sum_ball_bound`, not an empirical fit. Nonzero modular layers
are added using `equal_pair_sum_alias_bound` with k=4, including its tail.
Divide by q^(5m) for the rank-five activity, and take the minimum with the
previous complete Gaussian kernel. Both ordinary and marked completions
inherit this change through their shared kernel call.
