# Girth seven on thirteen positions: no independent norm-eight pair

This lemma applies to the existing c=7, t=6 coefficient-code branch for
every proper nonempty prescribed overlap (1,...,6). It improves the full
local kernel, with no excluded event or additional anchor addback.

## Support obstruction

Let C be the seven old coordinates and J the six new coordinates. The
rank-two modular relation code contains a line supported exactly on C,
and its new restrictions have dimension one. Hence every row outside the
C direction is nonzero on all six new coordinates.

A balanced squared-norm-eight integer row has support two, five, or eight.
Girth seven eliminates the first two shapes; the remaining shape is eight
unit entries with four plus and four minus signs. It cannot lie inside C,
which has only seven coordinates. Therefore every norm-eight row has all
six new unit entries and exactly two old unit entries.

Suppose two such rows are independent. Their new restrictions are
proportional modulo q. Since each new entry is +/-1 and q=3329, the scalar
is +/-1, and the restrictions agree with that sign over the integers.
Their signed difference is a nonzero integer row supported on at most four
old coordinates. Every entry has absolute value at most two, so reduction
modulo q preserves nonzeroness and support. This produces a nonzero code
row of support at most four, contradicting girth seven.

Thus two independent norm-eight rows are impossible. The proof does not
depend on which proper overlap was prescribed.

The script generates all `binomial(7,2)*binomial(8,4)/2=735` balanced
crossing lines. Grouping their new restrictions up to sign gives 11760
pairs, each checked to have the stated nonzero old difference. The support
contradiction also holds in the finite checks at q=7 and q=17. This finite
verification supplements the complete support argument above.

## Complete GS cases, including short-span ranks zero and one

Girth seven and balance imply the first positive squared norm is at least
eight. For a Gauss-reduced basis of the rank-two integer plane:

* If the first squared norm is eight, the second cannot be eight. Its squared
  norm is at least ten, so its squared GS projection is at least
  `10-8/4=8`. The GS lower bounds are (8,8).
* Otherwise the first squared norm is at least ten. Gauss reduction gives
  the second squared GS length at least three quarters of the first, hence
  at least 15/2. The bounds are (10,15/2).

The evenness used here follows from balance: the sum of squared integer
coordinates has the same parity as their sum. Cutoff-short modular affine
rows are balanced over the integers because their absolute sum is less
than q.

No rank-two basis is presumed when the cutoff-short real span has lower
rank. For rank zero its theta sum is one, bounded by either product. For
rank one a shortest primitive generator has squared norm eight or at least
ten; its theta factor is bounded by the first factor of the corresponding
product, and the added second factor is at least one. Thus both lower-rank
possibilities are included without inventing a second short vector.

For rank two, take the saturated integer lattice in the real span. It
reduces into the coefficient code: two independent short rows have a
nonzero 2x2 minor bounded in absolute value by `14^2<q`, so their index in
the saturation is not divisible by q. Consequently the saturated lattice
has the same modular span. Its vectors satisfy the same support and girth
restrictions. No unit minor is claimed for an arbitrary pair here; the
bounds apply to a reduced basis of the full saturated lattice. The usual
`14^3<q` lifting bounds the real rank of all cutoff-short rows by two.

## Unchanged full tails

Let beta=11N/(26R^2), a0=pi^2/beta, alpha=a0/q^2. The Holder power for this
branch is `min(13/2,7)=13/2`, not seven. Keep

    delta = 2 exp(-a0/4)/(1-exp(-2a0)),
    T = exp(-98 alpha) theta((13/4) alpha)^2,
    E = sum_{j=1}^13 binomial(13,j) delta^j,
    K(u,v) = (pi/beta)^(13/2)
             * ((theta(u alpha) theta(v alpha)+T)/q^2 + E).

The complete improvement is

    min(previous selected kernel, K(8,8)^N + K(10,15/2)^N).

It includes all cutoff tails, periodic terms, and the zero vector. The
original Markov factor, coefficient counts, completion counts, and
normalizations remain unchanged. The script checks `14^3<3329` and
`13*14^2<3329^2` and directly retains the production tail and periodic
objects in its independent calculation.

## Production insertion and verified effect

The existing branch guarded by

    (c == 8 and union <= 11) or (c == 7 and union <= 12)

already computes the desired two-case kernel with height eight when c=7
and union=13. Extending only its c=7 upper endpoint from 12 to 13 therefore
implements this lemma. Its c=8 cases and the special c=7/H11 counting branch
remain unchanged. Alternatively use a separate c=7,union=13 branch with
the displayed complete sum. This worker has not edited production; the parent subsequently extended the guard.

The standalone script extracts the actual selected kernel, including its
existing overlap-sensitive alternatives. Measured log10(new/old) values for
overlaps 1,...,6 are approximately

    -15.05221032, -6.04882480, -1.80370701,
     -1.80370701, -6.04882480, -15.05221032.

Recomputing the selected rank-11/girth-seven sums, including the unchanged
other t families and the one-relation alternative, gives the same gain at
component sizes 18 and 19:

    log10(new selected sum / old selected sum) = -15.05181826025....

These are improvements to upper envelopes, not measured probabilities or a
certificate of the full high-order budget.

Run `python3 docs/research/scripts/wall1_seven_thirteen_no_eight_pair.py`.
Pre-integration log: `/tmp/wall1_seven_thirteen_no_eight_pair.log`.
All exact support checks and complete interval comparisons pass. Parent
integration, independent review, and whole-frontier regression remain
separate from this bounded result.

## Integration-aware regression

The original measured log remains unchanged. After the parent extended the
c=7 guard, the standalone diagnostic reconstructs the previous selected
H13 kernel as `chosen_gaussian**N`, which includes the original
overlap-sensitive alternatives. It computes the new two-case kernel with
independently reconstructed cutoff and periodic corrections and checks both
corrections and the final production selected kernel within relative
tolerance 1e-60. It reconstructs the old rank-11 sums by undoing only the
changed t=6 factors in the current production terms; thus it does not apply
the improvement twice. The one-relation alternative is retained in both
old and new selected sums.

Post-integration log:
`/tmp/wall1_seven_thirteen_no_eight_pair_integrated.log`.
