# Retaining a dependent extension of a short anchor

For an anchor of size s and rank d=s-2, the previous rank-d cover allowed
every outside point any of q^(d-1) affine-span positions. Retain the
relation of one outside point instead. Choose the least outside label;
there is no factor for choosing it among h-s positions.

Fix an independent anchor basis X. The chosen point lies in its span,
so it has a unique normalized fundamental relation with new coefficient
one and a old nonzero coefficients supported in X. Girth four implies
a>=3. The affine sum condition leaves at most q^(a-1) coefficient choices,
and the old support has choose(d,a) possibilities.

This adds one relation and one point without increasing rank. Part 305's
short-code argument applies with t=1: the independent third direction
has nonzero new coordinate, and its old part cannot lie in the old
relation plane because it is supported on an independent basis. The
third squared heights are 1+2/3, 1+1/2, and 1+3/5 for the triangular,
orthogonal, and shared-point types, respectively. All cutoffs, long tails,
and periodic expansions remain. Let T1 be the corresponding normalized
full-modular count on s+1 positions, with rank d.

The replacement rank-d cover is

    choose(h,s) P [sum_(a=3)^d choose(d,a) q^(a-1)]
      T1 q^((d-1)(h-s-1)).

Use its minimum with the old cover. Every allowed rank-d support has the
chosen fundamental relation; no exceptional family has been discarded.

## Basis multiplicity for higher-rank other anchors

For the other-anchor crossing covers, also restore the same factor used
for triangular anchors. Contracting a fixed anchor and crossing leaves
rank e and no coloops. Indeed for an outside element x,

    rank((M/A) without x) = rank(M without x)-rank(A)
                        = rank(M)-rank(A).

A rank-e coloop-free matroid has at least e+1 bases: from any basis, for
each of its e elements there is a basis exchange replacing that element,
and these e bases are distinct from each other and the original basis.
This remains true at e=0. Divide the crossing completion cover by e+1.
The fixed crossing stays a valid witness for every basis extending its
fixed independent part. Marked parallel covers use canonical representatives
and are not divided again. Exact checks verify 21,090 contractions and
their basis counts; this correction alone barely changes size fifteen.

The additional arguments are paper proofs connected to outward-interval
envelopes. They do not establish the remaining high-degree components,
selected-history estimates, or full BKZ theorem, and are not Lean formalized.

## Outcome and diagnostic

The full size-fifteen bound stays about 4.99e-12: the proposed dependent-point
cover is not smaller in the dominant case. The new family/rank diagnostic
identifies the rank-five seven-point shared-anchor same-rank term at
log10 -11.57593 (about 2.65e-12), followed by its rank-six small-crossing
term at log10 -13.01452 (about 9.67e-14). All other listed other-anchor
families are much smaller. Thus the same-rank shared-anchor term really
is an obstruction, but this uniform three-row Gaussian refinement does
not resolve it. The earlier possibility that a different rank branch
dominated is ruled out by the explicit decomposition.

These are individual positive upper envelopes, not lower bounds on actual
error probabilities. The no-double-short remainder is also still about
2.05e-12. Larger component sizes and selected histories remain open.
