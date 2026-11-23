# H9, girth five: complete counted short-pair covers

This standalone refinement applies to c=5, t=4, old set C={0,...,4}, new
set J={5,...,8}, and overlap o=1,...,4. The coefficient plane has a direction
supported exactly on C and a second direction supported on {0,...,o-1} union J.
All rows are affine-balanced. The numerical certificate uses q=3329, N=518.
It does not assert the adaptive BKZ selection law.

## Actual controlling branch

Production's selected kernel equals the one-six plus no-six split here;
two-six is zero (the existing girth-five two-norm-six classification requires
union eight). At overlap four, one-six is 10.916916 orders below selected,
so no-six is the current limiting family. Refining only one-six would have
negligible effect.

## Complete finite chart covers

A short row in the coefficient plane either vanishes throughout J or is
nonzero throughout J. Balanced norm-six rows surviving girth five are unit
rows on six positions. They therefore use J and two old positions, giving
100 lines. Balanced norm-eight rows have support two, five, or eight; girth
excludes support two. There are 295 lines whose new restriction is zero or
full: 20 old-only support-five lines, 100 crossing support-five lines, and
175 crossing unit-eight lines. The script enumerates all integer balanced
rows of the two exact norms and verifies these counts.

For every mixed six/eight pair and every unordered eight/eight pair:

1. Require full union and proportional restrictions to J. The latter is
   tested by all integer minors on J; for entries at most two, these tests
   agree with modular vanishing at q=3329.
2. Cancel coordinate 5, require the resulting row to have full support C,
   and normalize its coordinate 0 to one, producing f.
3. Choose a pair row with nonzero coordinate 5, subtract its coordinate-0
   multiple of f, then normalize coordinate 5 to one, producing v.
4. Check girth using every cancellation ratio -v_i/f_i on C. All other
   directions have full union, and f itself has support five.
5. For each overlap retain the chart exactly when one cancellation direction
   has the prescribed support {0,...,o-1} union J. Store the canonical pair
   (f,v) in a set, removing duplicate witnesses.

The resulting distinct chart upper counts are:

| overlap | six/eight | eight/eight |
|---|---:|---:|
| 1 | 0 | 400 |
| 2 | 200 | 126 |
| 3 | 60 | 258 |
| 4 | 560 | 2212 |

The script verifies equality at q=7,17,3329; only the last is needed by the
numerical certificate. These are upper covers: extra charts with norm-six
rows may remain in the eight/eight count. This is safe because that count is
applied only to the actual no-six subfamily, where its uniform kernel is
valid. No exact Gram determinant or unit-minor assumption is made for these
counted pairs. Their rank-two modular span fixes at most one normalized
prescribed-support coefficient chart: a proper nonempty zero set determines
a unique cancellation direction. Thus distinct chart counts, rather than
witness multiplicities, are valid coefficient upper bounds.

## Complement, saturation, and full tails

The one-six rare class retains the existing complete GS(6,13/2) kernel.
After removing all independent norm-eight pairs, the second reduced squared
norm is at least ten, giving GS(6,17/2). Two independent norm-six rows were
already excluded. In no-six, the counted pair class retains GS(8,6). In its
complement, first squared norm eight implies second at least ten, giving
GS(8,8); first at least ten gives GS(10,15/2). Rank-zero and rank-one short
spans are covered by additional theta factors at least one.

The reduced-basis reasoning uses the saturation of the lifted short span.
With cutoff36 and a norm-six row, sqrt(6)*36^2<q lifts all short triples;
cutoff14 uses 14^3<q. A nonzero short-pair minor has magnitude below q, so
the saturation index is not divisible by q and its modular reduction remains
the same coefficient plane. Balance and girth therefore apply to the reduced
basis of this saturation. This is not an assertion that every enumerated
pair generates the saturation.

Set beta=7N/(18R^2), alpha=pi^2/(beta*q^2), and Holder power 9/2. Define

    delta = 2 exp(-pi^2/(4 beta))/(1-exp(-2 pi^2/beta)),
    E = sum_{j=1}^9 binomial(9,j) delta^j,
    T36 = exp(-648 alpha) theta(9 alpha/4)^2,
    T14 = exp(-98 alpha) theta(9 alpha/4)^2,
    K(u,v;T) = (pi/beta)^(9/2)
                * ((theta(u alpha) theta(v alpha)+T)/q^2 + E).

For Q=q^(5+o), C6=min(Q,840*q^3), and chart counts A_o,B_o above, use

    one = min(C6,A_o)/Q * K(6,13/2;T36)^N
            + C6/Q * K(6,17/2;T36)^N,
    none = min(Q,B_o)/Q * K(8,6;T14)^N
            + K(8,8;T14)^N + K(10,15/2;T14)^N.

Minimize each against its existing complete term, then their sum against
actual selected. Retain the outer Markov and coefficient normalizers.

## Diagnostic

Run `python3 docs/research/scripts/wall1_five_nine_refinement.py`.
Log: `/tmp/wall1_five_nine_refinement.log`.
The script only instruments an in-memory AST copy of production to capture
size18 rank9 c5 raw charges. It checks that their sum equals the selected
stratum and replaces only t4 terms by their actual-selected ratios.

Selected kernel improvements for overlaps 1,...,4 are approximately
18.69220, 15.06254, 19.10767, 21.65995 decimal orders. After improvement the
one-six term controls overlaps two through four. The independently captured
size18 rank9 c5 residual decreases by 5.14453 decimal orders; this is an
aggregate stratum comparison, not a claim of equal full-size18 improvement.
Production source is unchanged by this script.

After the parent integrated the branch, the diagnostic was made integration
aware. It captures the unchanged generic Gaussian candidate, reconstructs
old one-six/no-six kernels independently, and minimizes their old sum against
that candidate to recover the previous selected kernel. It verifies the
integrated one-six, no-six, and selected kernels to relative tolerance 1e-60
for every overlap. Current raw charges are divided by the selected improvement
ratios to reconstruct the previous aggregate; unchanged t3/t5 terms are retained.
The pre-integration log above is preserved. The integration-aware run is
`/tmp/wall1_five_nine_refinement_integrated.log`. Production edits are owned
by the parent; this diagnostic only modifies its in-memory copy.
