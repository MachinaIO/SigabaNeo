# Exact five-point codes with two norm-four directions

The c=3,t=2,a=2 anchor has H=5 positions. Its two-norm-four contribution
previously used (3 choose(5,4))^2=225 as a coefficient-pair count. An exact
finite classification reduces this to six at q=3329.

Every integer norm-four affine row is balanced +/-1 on four positions;
the other squared-norm-four possibility has support one and cannot be
affine. There are five choices of support and three projective balanced
sign patterns, giving 15 lines and 105 unordered pairs. Any eligible
code containing two independent such lines is spanned by one of these
pairs, so enumerating all pairs is exhaustive.

For generators a,b with coordinates in {0,+1,-1}, coordinates of a+lambda*b
can vanish only at lambda=0,+1,-1, or at the separately represented
infinity direction b. All other directions have the full union support.
Consequently the four critical directions suffice to determine the
minimum weight and all proper circuit supports. Fix first support
{0,1,2} and second support {0,1,3,4}, using position symmetry. Keep codes
with minimum weight at least three and both prescribed supports.

Exact modular row reduction deduplicates the pairs into six eligible
two-dimensional codes at q=3329. The regression also checks q=7 and 17.
Each prescribed proper support determines at most one projective row
inside a full-support two-dimensional code: vanishing at any omitted
position is one nonzero linear equation. Thus each code contributes at
most one normalized prescribed coefficient pair. Six is therefore the
appropriate coefficient-count bound; neither the first-circuit choices
nor the second-circuit choices supply an additional factor here.

The existing short-plane, long-vector and periodic bounds remain unchanged.
Only this coefficient count is replaced. The related norm-six split for
girth three is documented in `wall1_three_six_split.md`; it produced only
a tiny improvement, motivating this exact norm-four classification.

This is an exhaustive finite calculation over the actual field with a
coverage argument, not sampling or a Lean proof. The remaining residual,
selected-history and complete BKZ statements are still open.

The full size-fifteen residual weighted log10 becomes -5.17651 (about
6.66e-6), versus -5.00138 before these refinements. Full cumulant
regressions preserve all admitted bounds through fourteen. The gain is
insufficient for the required residual budget; girth-four terms dominate.
