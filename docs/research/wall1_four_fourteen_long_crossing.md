# H14, girth four: long-crossing bounds for the leading size-24 branch

This refinement targets c=4,t=10,overlap=3, the actual leading
size-24 rank12/girth4 two-relation term in the Part396 diagnostic. The parent
has integrated the no-four GS(10,9) bound for overlaps1,2,3 and the counted
one-four norm-twelve split for overlap3 only. The original standalone
research did not edit production; the integration is now independently
checked by the companion diagnostic.
The verified local improvement relative to the actual selected production
kernel is log10(new/selected)=-27.94404221699495..., with every original
tail and periodic term retained. This is not a claim about the recomputed
full size-24 sum: other overlap/rank terms can become dominant.

## Geometry of the crossing direction

Let C={0,1,2,3}, let the ten new coordinates be 4,...,13, and let the second
prescribed support be {0,1,2,4,...,13}. In the two-dimensional modular relation
code, every direction outside the C direction has all ten new coordinates
nonzero. It must also have a nonzero old coordinate. Indeed if its entire
old part were zero, adding a nonzero C row would give all four old positions,
whereas the prescribed second support has exactly three.

Thus an outside short integer row has support at least eleven. Balanced
integer squared norms are even, so its squared norm is at least twelve.
The existing cutoff lifting and saturation arguments apply: in particular
the short real plane has dimension at most two and its saturated integer
lattice reduces into the relation code. Short independent integer rows
cannot lie in the same C direction: their integer 2-by-2 minors have
absolute value less than q, so modular proportionality forces all those
minors to vanish over the integers.

## No-four family: GS lower bounds (10,9)

A balanced norm-six row has shape (2,-1,-1), with support three, or six unit
entries. Girth four excludes the former, and the latter fits neither C nor
a crossing direction with at least eleven coordinates. A norm-eight row has
support two, five, or eight; support two violates girth, while five and eight
again fit neither allowed location. Hence in the no-norm-four family the
first squared minimum is at least ten.

Every norm-ten row must lie in the C direction since it has support at most
ten. Two independent such rows are impossible by the preceding modular-to-
real observation. The second squared minimum is therefore at least twelve.
A Gauss-reduced basis satisfies g2^2 >= (3/4)*lambda2^2 >=9. The first GS
squared length is at least ten, yielding the complete kernel K(10,9).
If the short real span has rank zero or one, the extra theta factor is at
least one, and the same bound remains valid.

## One-four family: rare norm-twelve crossing versus its complement

There cannot be two independent norm-four rows: each is supported on C,
while the whole relation plane has support fourteen. The unique norm-four
line is a balanced unit-four row a on C; there are three choices up to sign.
Let b be an independent balanced norm-twelve row. It must have ten nonzero
new entries and at least one old entry. The only norm-twelve shape with
support at least eleven is twelve unit entries. Therefore b is supported
on all ten new positions plus two old positions, with six plus and six
minus signs.

There are choose(4,2)*choose(12,6)/2=2772 such unoriented b lines. Together
with the three possible a lines this gives at most 8316 pair witnesses.
For each fixed prescribed support a pair fixes one code and at most one
normalized coefficient chart. This is an upper count, not an assertion of
8316 different eligible charts.

For overlap three, the two nonzero old ratios b_i/a_i must be different.
The other two ratios are zero, and cancelling their common zero value would
leave only two old positions; cancelling one of two equal nonzero ratios
would also leave two. Thus the two nonzero ratios are +1 and -1. Since a_i
is a unit, their contributions to <a,b> sum to zero. Consequently the Gram
determinant is 4*12=48 and the exact squared GS lengths are (4,12).

An old coordinate where b vanishes and a is a unit, together with any new
unit coordinate of b, gives a unit minor. Therefore a,b generate their full
saturated integer plane, not merely a sublattice of it. They are orthogonal
and reduced. The enumeration checks this unit-minor property for every pair.
It finds exactly 2016 charts for the prescribed overlap-three support at
q=7,17,3329, all with determinant48; the weaker 8316 bound is sufficient.

In the complementary one-four family there is no independent norm-twelve
row. The reduced second squared norm is at least fourteen, so reduction
against the squared-norm-four first row gives squared GS height at least
14-4/4=13. This yields K(4,13) for the entire complementary family.
No family is deleted, hence no extra excluded-event addback is needed.

## Complete formula and retained tails

Let beta=12N/(28R^2), alpha=pi^2/(beta*q^2), and let E be the unchanged full
periodic-plane correction. Define

    T4 = exp(-800*alpha)*theta(4*alpha/2)^2,
    T0 = exp(-98*alpha)*theta(4*alpha/2)^2,
    K(x,y;T) = (pi/beta)^7 *
                ((theta(x*alpha)*theta(y*alpha)+T)/q^2 + E).

These are exactly the existing one-four cutoff40 and no-four cutoff14 tails.
The corresponding lifting inequalities are retained; no contribution from
long vectors, modular aliases, or the zero vector is discarded.

For overlap three, Q=q^(4+10+3-4)=q^13. The existing one-four chart count is
3*q^11, since a norm-four direction must be on C. A complete bound is

    min(3*q^11,8316)/Q * K(4,12;T4)^N
      + 3/q^2 * K(4,13;T4)^N
      + K(10,9;T0)^N.

For safe integration, first minimize the first two terms against the old
one-four term and the last term against the old no-four term, then minimize
their sum against the actual selected kernel. Retain all exterior Markov,
normalization, coefficient-chart and completion factors unchanged.

## Numerical evidence

The original pre-integration run of `wall1_four_fourteen_long_crossing.py`
extracted the actual c4,t10,overlap3 locals immediately before the production
anchor was stored. Its preserved log computes:

- old one-four log10: 15363.8819699785022;
- old no-four log10: 15383.6433123083358;
- actual selected kernel log10: 15382.8226267805674;
- new/old one-four log10 ratio: -9.00338541492977;
- new/old no-four log10 ratio: -50.3139256777139;
- new/actual-selected log10 ratio: -27.9440422169950.

The actual selected old kernel was smaller than the old split, which is why
comparing only against an unused no-four bound would overstate the gain.
The new rare norm-twelve contribution is 26.2993 orders below its one-four
complement. The next obstruction inside this refined branch is therefore
the norm-four line with an unclassified crossing of squared norm at least
fourteen, rather than the counted norm-twelve planes.

The original measured log is preserved at
`/tmp/wall1_four_fourteen_long_crossing.log`. It must not be presented as a
comparison against the already improved production kernel.

Run `python docs/research/scripts/wall1_four_fourteen_long_crossing.py` for
the integration check. The current diagnostic captures locals immediately
before each new production branch, reconstructs the old one-four minimum
including the existing rare and direct-ball alternatives, and reconstructs
the old selected bound from that split and the original Gaussian bound. It
then independently rebuilds both new kernels and checks interval agreement
with production one-four, no-four and selected powers for all three overlaps.
The integrated-run log is
`/tmp/wall1_four_fourteen_long_crossing_integrated.log`.
This is a local bound improvement, not a completed high-order residual proof
or a BKZ certificate.
