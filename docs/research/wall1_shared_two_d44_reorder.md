# Rank-six/girth-four diagnostic and a conditional D44 exclusion

The size-17 rank-six/girth-four bound is dominated by an addback, not by its
remaining two-relation kernel. The selected-cover log at
`/tmp/wall1_h5_d23_weighted_components.log` has:

| Selected-cover component | Weighted log10 bound |
|---|---:|
| remaining | -28.7792459243212 |
| triangle | -14.4581151828554 |
| other-two-four | -9.93220230703961 |
| D20-eight | -10.9829902734304 |
| D24-eight | -33.7746152703970 |
| D23-seven | -37.8807951408734 |

A fresh diagnostic (`/tmp/rank6_other_diagnostic.py`, log of the same stem)
resolves other-two-four into its actual anchor contributions:

| Anchor / extension | Weighted log10 |
|---|---:|
| six-position orthogonal / large crossing | -35.9239483228974 |
| six-position orthogonal / small crossing | -35.9107566928548 |
| seven-position shared / small crossing | -9.93220230703961 |

The last term has t=2. Its coefficient sum splits into rare norm-four
extensions, log10=-130.456679717571, and the regular no-new-four family,
log10=-159.753117197171. The rare family itself has determinants/counts
44:20, 50:14, 54:13, 56:8, 60:8; its D44 term has log10=-130.456679717571,
whereas D50 has log10=-144.990567404506. These are unweighted joint bounds,
not probabilities.

## Exact containment lemma

Every D44 row in the shared-seven-point/two-new-point norm-four extension
family contains a six-position triangular anchor.

Proof: use the existing saturated shared anchor rows

    a=(1,1,-1,-1,0,0,0,0,0),
    b=(1,0,0,0,1,-1,-1,0,0).

They have squared norms four and scalar product one. Let c be a balanced
norm-four row nonzero on both new positions 7,8. It has exactly two nonzero
old coordinates, so x=<a,c> and y=<b,c> lie in [-2,2]. The Gram determinant
condition is

    44 = 60-4x^2+2xy-4y^2,
    2x^2-xy+2y^2=8.

If both |x| and |y| are at most one, the left side is at most five. Thus one
of |x|,|y| equals two. Select that old row u. Since u has only old coordinates
and c has exactly two old coordinates, their support intersection has size
two. The scalar product +/-2 forces their signs to agree up to a common sign
on both shared positions. Hence u-sign(<u,c>)*c is another balanced norm-four
row, supported on their four exclusive positions. The union has six positions
and the three lines form precisely a triangular four/four anchor.

The pair u,c has a unit minor obtained from one coordinate exclusive to each
row. Its integer plane is saturated. The full rank-three extension also has
a unit minor in every one of the twenty configurations, verified exactly by
the script. This lemma is unchanged over q=3329: all displayed minors and
coordinates are far smaller than q, and the unit minor preserves rank.
It is a containment of complete coefficient codes, not just of short dual
vectors or of their leading Gaussian terms.

## Valid conditional integration and addback

The complete global cover already includes a bound T for every support with
an eligible triangular anchor, and O bounds the other-two-four category.
Use the set cover

    target subset (triangular event) union
                  (other-two-four event AND no triangular anchor) union ... .

In the second event no D44 two-point extension code can occur, by the lemma.
Consequently, in `weighted_joint(size=7,t=2)`, for this CONDITIONAL other
family, replace the rare sum by

    sum_{D in {50,54,56,60}} count[D]*code_ball_bound(D).

Retain the coefficient-weighted no-new-four term, and take the minimum with
the original unsplit bound as before. Keep every tail and periodic term in
each retained code bound unchanged. Deleting the entire D44 code term is
valid because its entire event is absent in this conditional family.

The required addback is T: the existing triangular cover, including its
own remaining-family term plus any D44 refinement/addback used inside it.
It must not be omitted. An unconditional `other_envelopes` caller cannot
use this deletion by itself; an explicit no-triangle condition or a separate
restricted function should preserve that API distinction. The other
extension branches can retain their old overestimates. No new probability
or measure estimate is assumed in this set-theoretic refinement.

## A tested but ineffective alternative

Permuting the D44 generator basis to put the dot-product-two pair first
changes squared GS lengths from (4,15/4,44/15) to (4,3,11/3). The script
retains exactly the existing cutoff-29 tail and periodic terms. It verifies
an improvement, but the log10 ratio of the complete rare sum is only
-5.87511671183e-24. This is quantitatively ineffective and should not be
presented as a meaningful residual reduction. The containment lemma above
is the useful result.

## Verification

`python docs/research/scripts/wall1_shared_two_d44_reorder.py` exhaustively
checks all eligible norm-four extensions, the twenty D44 configurations,
triangular support intersections, balanced third lines and unit minors.
It also evaluates every determinant contribution and the full-tail GS
alternative using interval arithmetic. Output is saved at
`/tmp/wall1_shared_two_d44_reorder.log`.

No production evaluator was edited here. The global numerical improvement
must be measured after integrating the conditional cover; the local deletion
alone is not an unconditional replacement for other-two-four.
