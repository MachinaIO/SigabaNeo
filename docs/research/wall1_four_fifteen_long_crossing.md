# H15, girth four: long crossings and complete no-four minimum cases

This research targets the size24 rank13/girth4 branch c=4,t=11,
particularly overlap3. The parent has now integrated both the counted
one-four split and the stronger complete four-case no-four split for all
three overlaps. The worker edits only this standalone checker and note. The whole coefficient
family remains covered; no new excluded-event addback is required.

Let C be the first four positions and the new positions be4,...,14. An
outside-C code direction is nonzero on all eleven new positions. Its old
part is also nonzero: a new-only direction together with C would allow old
support only zero or four, contrary to the prescribed proper nonempty overlap.
Thus an outside integer row has at least twelve nonzero coordinates.
All short rows are balanced and have even squared norms, using the existing
lifting and saturation conditions.

## One-four family

There are three balanced norm-four lines a on C. An outside norm-twelve row
must have twelve unit entries: all eleven new coordinates and one old
coordinate, with six plus and six minus signs. There are
4*choose(12,6)/2=1848 unoriented lines b. Hence at most5544 pair witnesses
cover every code with a norm-four line and an independent norm-twelve row.

The scalar product <a,b> is +/-1. The Gram determinant is47 and squared GS
lengths are(4,47/4). A coordinate on C where b=0 and a is a unit, paired
with a new unit coordinate of b, gives a unit minor. This proves saturation
of the integer plane and modular independence, so there is no sublattice
index loss in the theta product. Every pair determines one modular plane
and at most one normalized chart per prescribed second support.

In the complementary one-four family, the reduced second squared norm is
at least fourteen. Its squared GS projection is at least14-4/4=13.
The existing chart bound is one_count=3*q^(9+o), Q=q^(11+o) for overlap o.
Therefore a valid complete one-four upper bound is

    min(one_count,5544)/Q*K4(4,47/4)^N
      + one_count/Q*K4(4,13)^N.

K4 keeps the full original cutoff40 tail and periodic correction. The uniform
5544 bound is sufficient, although exact chart counts are1386,0,1386 for
overlap1,2,3 at q=7,17,3329. The zero overlap2 count is not needed by the
uniform formula.

## No-four family: all minimum cases

No norm-six or norm-eight row is possible: their support shapes either
violate girth4, exceed the four old coordinates, or cannot cover the eleven
new coordinates and a nonempty old part. Thus the first squared minimum is
at least ten. Every norm-ten row lies in the C direction, so two independent
norm-ten rows are impossible. A coarse complete bound is GS(10,9), using
second squared minimum at least twelve and Gauss reduction.

The following complete split is stronger.

1. First squared minimum ten. The old row has shape(2,-2,1,-1), supported
   on C. If the second squared norm is twelve, it is the outside unit-twelve
   row above. Its dot product with the first row has magnitude at most two,
   giving GS height at least12-4/10=58/5. If the second squared norm is at
   least fourteen, reduction gives height at least14-10/4=23/2. Therefore
   GS(10,23/2) covers this entire case.
2. First squared minimum twelve. Two outside unit-twelve rows cannot be
   independent in the code: their new restrictions must agree up to sign,
   so their nonzero difference has old support at most two, violating girth4.
   If both minima are twelve, one row lies on C, necessarily with shape
   (3,-1,-1,-1), and the other is outside. Their scalar product has magnitude
   at most three, so the second GS height is at least12-9/12=45/4.
   An outside norm-fourteen row must be unit-fourteen on eleven new and
   three old coordinates: the only nonunit shape with support eleven is
   new-only and impossible; all other shapes have support at most eight.
   There is no full-support norm-fourteen row on C. An outside norm-twelve
   and outside norm-fourteen pair is impossible: after matching the new
   signs, disjoint old supports give a norm-four difference, while intersecting
   old supports give a nonzero difference supported on at most three positions.
   Thus a (12,14) pair has its norm-twelve row on C, and dot product magnitude
   at most3+1+1=5. Its height is at least14-25/12=143/12, greater than45/4.
   If the second norm is at least sixteen, reduction gives height at least13.
   Consequently GS(12,45/4) covers the entire first-twelve case.
3. First squared minimum fourteen. Both norm-fourteen rows would be outside
   unit-fourteen rows. Matching their new signs leaves an old-supported
   difference. Equal old supports give weight at most three; distinct old
   triples leave two exclusive unit entries and at most two doubled entries,
   so its squared norm is at most ten. Either way this contradicts first
   minimum fourteen. Therefore the second squared norm is at least sixteen,
   giving GS bounds(14,25/2).
4. First squared minimum at least sixteen. Gauss reduction gives GS lower
   bounds(16,12).

All inside/outside row claims follow by partitioning their small squared
norms into integer squares and applying the support restrictions. Short
rows in the same C modular direction are really proportional because their
2-by-2 integer minors are smaller than q. The complement uses a reduced
basis of the saturated short real plane, not an arbitrary nonsaturated pair.
If that plane has rank zero or one, padding the theta product with a factor
at least one preserves the upper bound.

Consequently the no-four power can be minimized with

    K0(10,23/2)^N + K0(12,45/4)^N
        + K0(14,25/2)^N + K0(16,12)^N.

K0 keeps the existing cutoff14 tail. The simple alternative K0(10,9)^N
is also valid and evaluated for comparison. These are complete minimum-case
covers; no rare-family coefficient denominator is applied to their sum.

## Tails and production comparison

Here beta=13N/(30R^2), alpha=pi^2/(beta*q^2), and

    K(x,y;T)=(pi/beta)^(15/2)*
               ((theta(x*alpha)*theta(y*alpha)+T)/q^2+E),
    T4=exp(-800*alpha)*theta(4*alpha/2)^2,
    T0=exp(-98*alpha)*theta(4*alpha/2)^2.

E is the original complete periodic-plane correction. No long-vector,
modular-alias, or zero-vector contribution is dropped. Minimize the proposed
one-four and no-four bounds separately with the existing values, add them,
and minimize against the actual selected Gaussian/kernel power. Full-support
two-four planes cannot occur on fifteen positions.

`wall1_four_fifteen_long_crossing.py` enumerates all5544 short pairs, verifies
unit minors and prescribed charts, and checks that all proportional-new
outside/outside pairs violate girth. It then reads the actual c4,t11 locals
before the production anchor is stored and compares against the selected
kernel, not merely against an unused split term.

Run `python docs/research/scripts/wall1_four_fifteen_long_crossing.py`.
The initial three-case numerical log is preserved at
`/tmp/wall1_four_fifteen_long_crossing.log`. The stronger four-case run is
`/tmp/wall1_four_fifteen_four_case.log`. Its finite checker additionally
enumerates6864 outside norm-fourteen lines,22176 forbidden outside12/14
pairs, and32472 forbidden outside14/14 pairs. These exhaustive pair checks
complement the shape-and-support arguments above.
All numerical effects are upper-bound improvements, not actual failure
probabilities or a completed BKZ proof.

For the actual overlap-three selected kernel, the four-case diagnostic gives
log10(new/selected)=-17.939027047066. The one-four power improves by
11.371520706310 orders, while the no-four power improves by73.488712495418
orders. The old split was not the selected bound: old no-four/selected had
log10=+11.768612229139 and old one-four/selected had log10=-6.567506340756.
This is why the selected-kernel comparison is necessary. After refinement,
the counted norm-twelve term is27.629542868686 orders below its one-four
higher complement, which is the next local bottleneck. The full size24
residual still requires recomputation with all other ranks and overlaps.


## Integration-aware AST check

The current script compiles an in-memory copy of `draw14_bounds` in a private
globals dictionary. AST-inserted capture calls run only immediately before
the new rare-one branch, before the new no-four branch, and before storing
an anchor. The script neither edits production source nor enables global
Python tracing. Each inserted call only copies selected local references;
it leaves every original expression and control-flow branch intact.

From the pre-branch locals it reconstructs the prior one-four minimum,
including the unchanged later rare/direct-ball alternatives, and then the
prior selected bound. Independently rebuilt one-four, no-four and selected
powers are required to overlap the corresponding production intervals at
all three overlaps. Comparison uses that prior selected denominator rather
than the already improved current kernel. Signature and original module
namespace isolation are also checked.

The initial standalone logs are preserved. The integration-aware log is
`/tmp/wall1_four_fifteen_integrated.log`.
