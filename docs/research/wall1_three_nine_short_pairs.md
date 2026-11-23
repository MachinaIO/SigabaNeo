# H9, girth three: a counted (6,8) cover

This note sharpens the existing no-four branch for c=3, six new positions,
and either proper overlap. The rank-nine applications at component sizes
17 and 18 use this same local kernel. The parent subsequently integrated
the uniform determinant-39 version; this worker edits only this note and its
standalone diagnostic.

## Exact geometry

Let the two-dimensional relation code on nine positions have girth at least
three. It contains a first line supported on C={0,1,2} and a crossing line
supported on all six new positions and a proper nonempty subset of C.
Work in the existing balanced integer short-plane lifting, at q=3329,
and assume this branch has no norm-four line.

Every row outside the C line has all six new entries nonzero. It must also
have a nonzero old entry: otherwise adding a multiple of the full-support
C line gives either zero or all three old entries, contradicting the
prescribed proper crossing support. A balanced norm-six row therefore lies
on C and has shape (2,-1,-1), up to sign and permutation: three lines.
Two independent norm-six lines cannot occur.

A balanced norm-eight row outside C has eight unit entries, four positive
and four negative, on six new and two old positions. The other norm-eight
shapes have support at most five. There are

    binomial(3,2)*binomial(8,4)/2 = 105

outside lines. Thus a code with a norm-six line and an independent
norm-eight line has at most 315 possible pair witnesses. Each pair fixes
one modular plane and at most one coefficient chart for a fixed prescribed
crossing support. We retain witness multiplicity as a safe overcount.

For such a pair a,b, |<a,b>|<=3, so its Gram determinant is
48-<a,b>^2>=39. A unit old coordinate of a and a new unit coordinate of b
give a unit minor; a,b therefore generate the saturated integer lattice
in their real plane. They are Gauss reduced since 2|<a,b>|<=6. Exact
squared GS lengths are (6,(48-<a,b>^2)/6). Exhaustive counts are

    determinant: 39, 44, 47, 48
    witnesses:  120, 45, 90, 60.

If a norm-six line exists but no independent norm-eight line exists, the
second norm is at least ten. Gauss reduction then gives GS lower bounds
(6,10-6/4)=(6,17/2).

## Complete no-six complement

In the absence of norm six, any norm-eight line must be outside C: the
balanced support-three norm-eight possibilities have support two, contrary
to girth three. Two outside norm-eight rows in the same code have
proportional new restrictions. Since those entries are units and q=3329,
a sign change makes the new restrictions identical over the integers.
Their nonzero difference is balanced, supported on at most three old
positions, with entries of absolute value at most two. If it has support
two, it violates girth three; if it has support three, it is (2,-1,-1)
up to sign and permutation and has norm six. Both are excluded.

Thus independent norm-eight rows cannot coexist in this branch. Exactly
one norm-eight line gives squared GS bounds (8,10-8/4)=(8,8); absence of
norm eight gives (10,15/2). These cases exhaust the no-six branch. Rank-zero
or rank-one cutoff-short spans remain covered since each additional theta
factor in these bounds is at least one.

## Complete kernels, including tails

Use the existing beta=7N/(18R^2), a0=pi^2/beta, alpha=a0/q^2, and

    delta = 2 exp(-a0/4)/(1-exp(-2a0)),
    E = sum_(j=1)^9 binomial(9,j) delta^j,
    K_L(x,y) = (pi/beta)^(9/2) *
       ((theta(x alpha)theta(y alpha)
          +exp(-L^2 alpha/2)theta(3 alpha/2)^2)/q^2 + E).

The existing lifting checks 14^3<q, 9*14^2<q^2 and 6*36^4<q^2 hold.
The norm-six branch retains its full cutoff-36 tail and the no-six branch
its cutoff-14 tail. All periodic errors and Gaussian Markov factors are
unchanged.

For overlap o=1 or 2, Q=q^(5+o) is the coefficient count, and
S=3q^(4+o) is the existing norm-six chart upper count. Valid replacements are

    one-six <= sum_D count[D]/Q * K_36(6,D/6)^N
                 + S/Q * K_36(6,17/2)^N,
    no-six  <= K_14(8,8)^N + K_14(10,15/2)^N.

Minimize each new complete branch with its previous bound, then minimize
their sum with the previous complete no-four bound and the actually selected
anchor. In this family both one-four and two-four counts vanish: norm four
cannot lie on C or cover all six new positions. No excluded-family addback
is introduced by this local refinement.

## Reproduction and scope

Run `python3 docs/research/scripts/wall1_three_nine_short_pairs.py`.
The checker verifies all 315 pairs, saturation minors, determinants, and
195 outside pairs with proportional new restrictions. The latter split as
105 support-two/norm-two, 30 support-two/norm-eight, and 60 support-three/
norm-six differences.

The numerical diagnostic retains the full kernels and compares against the
actually selected local anchors. It evaluates the existing restricted
residual with exclusions for D20-six, D20-five, two-four-five, and D23-six,
matching the current girth-three frontier's final cover. Its rank-nine
aggregate comparison is for that residual; the unchanged addbacks must
still be included by the production envelope before a global claim.
This is a finite-witness paper proof and interval diagnostic, not a new
selected-history bound or completed BKZ proof.

With the current parameters, log10(new/actually selected local anchor) is
-19.38314162857879 for overlap one and -22.90545499236419 for overlap two.
For both h=17 and h=18, log10(new/old selected rank-nine restricted residual)
is -1.91359332274764. The next controlling residual family is t=2, overlap=2
(H5), whose old share has log10 -1.91360235111820. These are upper-envelope
ratios, not failure probabilities. The full interval output is retained in
`/tmp/wall1_three_nine_short_pairs_restricted.log`.

For production integration, within the c=3, union=9 branch, refine
`no_six_power` by the sum with GS (8,8) and (10,15/2), using `no_tail`.
After forming `one_six_term`, refine it by the four determinant-count terms
above and the S/Q complement with GS (6,17/2), all using `six_tail`.
The existing `two_six_term` is zero here. Existing outer minima then retain
all alternative complete covers. The parent must independently validate
this insertion and rerun full envelopes and addbacks.


## Integrated regression

The production insertion uses the simpler `315/Q * K_36(6,39/6)^N`
for the rare family, instead of the four determinant strata. The diagnostic
now verifies agreement of this standalone uniform kernel with the actual
production anchor to relative tolerance 1e-60. It reconstructs the previous
evaluator in a private AST copy by removing exactly the two c=3,H9
refinement branches. No module globals, source files, or global tracing
hooks are changed. Both previous and current restricted residual sums are
checked against their corresponding evaluator outputs.

Integrated log10 local improvement is -18.96401232091706 for overlap one
and -22.48632595174177 for overlap two. The determinant-stratified option
would further improve those local terms by about 0.41913 decimal orders;
it is not the currently integrated formula. The integrated h17 and h18
rank-nine restricted residual log10 ratio is -1.91359332274764, the same
to the displayed precision as the optional stratified version. Regression
output is `/tmp/wall1_three_nine_short_pairs_integrated.log`.
