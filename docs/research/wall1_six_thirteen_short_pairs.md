# H13, girth six: counted (6,8) planes and the no-six complement

Let C be the six old coordinates and J the seven new coordinates in the
existing rank-two coefficient-code branch c=6,t=7. Its first direction is
supported exactly on C and its second direction has all of J and a proper
nonempty old overlap o=1,...,5. The code has girth at least six. This note
refines its one-six and no-six parts, retaining their different full tails.

## One-six family and saturation

A balanced norm-six row has support three or six. Girth six forces the unit
six shape. An outside direction has all seven new coordinates nonzero, so
a norm-six line must be supported on C. There are ten such balanced lines.
Two independent norm-six rows are impossible: their modular reductions are
in the same C direction, and their small integer minors force real
proportionality. Thus the existing two-six term is zero at H13.

A balanced norm-eight row has support two, five, or eight. Girth six excludes
the first two shapes; the unit eight shape cannot lie inside C. Consequently
an outside norm-eight line consists of the seven new unit entries and one
old unit entry. There are `6*binomial(8,4)/2=210` such lines.

For a C-supported unit-six row a and an outside unit-eight row b, exactly
one old coordinate contributes to their inner product. Hence |<a,b>|=1 and

    det Gram(a,b)=6*8-1=47.

Any old coordinate where b vanishes and any new unit coordinate give a unit
minor. Therefore a,b generate the saturated integer lattice in their rational
plane. Their exact squared GS lengths are (6,47/6); they are Gauss reduced.
The 10*210=2100 pairs form a witness upper cover of this exceptional family.
Each pair fixes at most one normalized coefficient chart for the prescribed
supports. Duplicate witnesses cause only overcounting.

The exact script checks all 2100 unit minors and Gram47 pairs. Normalized
chart counts at q=7,17,3329 are `{1:350,2:0,3:0,4:0,5:350}`. The uniform
2100 upper count is sufficient and is what the bound uses.

In the remaining one-six family no independent norm-eight row exists.
A Gauss-reduced second vector then has squared norm at least ten, by affine
parity. Subtracting its component along the squared-norm-six first vector
leaves squared GS length at least `10-6/4=17/2`. This gives (6,17/2) for the
whole complement, including a short span of rank one by adding a theta
factor at least one.

## No-six family

In this family the first squared norm is at least eight. Every norm-eight
row is the outside unit-eight shape described above. For two independent
such rows the new unit restrictions would agree up to a sign. Their signed
difference is a nonzero old-supported row on at most two positions, violating
girth six. Integer entries have magnitude at most two, so nonzeroness and
support are preserved modulo q. The script checks all 525 such pairs, also
at q=7 and q=17.

Balanced norm-ten rows have support four, seven, or ten. Support four is
excluded by girth. Support seven cannot lie inside C. If such a row were
outside, all seven new coordinates would be its entire support. This is
impossible: a new-only direction together with the C direction would make
every old restriction either zero or full C, whereas the prescribed crossing
has a proper nonempty old overlap. Thus every norm-ten row in the no-six
family is a unit-ten row on all seven new and three old coordinates. There
are `binomial(6,3)*binomial(10,5)/2=2520` such lines. The script also enumerates
all 105 balanced new-only norm-ten lines, which the overlap argument excludes.

For an independent norm-eight/norm-ten pair, the new unit restrictions agree
up to sign. Their signed difference is nonzero on at most four old positions,
contradicting girth six. For two independent norm-ten rows, the difference
has at most six old positions. If it has fewer, girth excludes it. If it has
six, the two old supports of size three are disjoint, so the difference is
balanced unit-six, contradicting the no-six assumption. Entries of these
differences are at most two in absolute value, so reduction modulo q preserves
support and nonzeroness. Exact enumeration finds 12600 forbidden mixed pairs
and 65940 norm-ten pairs: 62580 excluded by girth and 3360 by norm six.

Thus none of the reduced minima (8,8), (8,10), (10,10) can occur. If the
first squared norm is eight, the second is at least twelve and its squared
GS projection is at least `12-8/4=10`. If the first is ten, the second is at
least twelve and its projection is at least `12-10/4=19/2`. Otherwise the
first is at least twelve and Gauss reduction gives second GS at least nine.
The complete no-six cover is therefore (8,10), (10,19/2), (12,9).
Short spans of rank zero or one are included by theta factors at least one:
zero contributes one, while a single generator contributes at most its
corresponding first theta factor.

For the generic rank-two cases use the saturated integer plane. Two
independent cutoff-short rows have a nonzero minor smaller than q, so their
index in that lattice is not divisible by q and its reduction is the same
coefficient plane. Thus the same girth, balance, and support restrictions
apply to a reduced basis of the saturation. The rare family has the stronger
explicit unit-minor certificate. No saturation of an arbitrary chosen
complement pair is asserted.

## Coefficient normalizers and different cutoffs

For overlap o the existing coefficient denominator and one-six count are

    Q=q^(6+7+o-4)=q^(9+o),
    C6=min(Q,10*q^(7+o-2))=10*q^(5+o)  at q=3329.

Thus C6/Q=10/q^4. The rare pair factor is min(C6,2100)/Q, not an unnormalized
2100 and not an extra product with C6/Q. The complement retains C6/Q.
These are the original coefficient counts; no sampling assumption is added.

Use beta=11N/(26R^2), a0=pi^2/beta, alpha=a0/q^2 and Holder power six. Put

    delta=2 exp(-a0/4)/(1-exp(-2a0)),
    E=sum_{j=1}^13 binomial(13,j) delta^j,
    T36=exp(-648 alpha) theta(3 alpha)^2,
    T14=exp(-98 alpha) theta(3 alpha)^2,
    K(u,v;T)=(pi/beta)^(13/2)
             * ((theta(u alpha) theta(v alpha)+T)/q^2 + E).

The one-six family keeps cutoff36. Its known norm-six row allows lifting
all other short rows since `6*36^4<q^2`; equivalently the relevant triple
minor bound is sqrt(6)*36^2<q. The no-six family keeps cutoff14 and uses
`14^3<q`. Both include the complete periodic correction. The unchanged
exterior Markov and q normalization factors must also be retained.

The complete replacements are

    B_one = min(C6,2100)/Q * K(6,47/6;T36)^N
            + C6/Q * K(6,17/2;T36)^N,
    B_none = K(8,10;T14)^N + K(10,19/2;T14)^N + K(12,9;T14)^N.

Minimize each against its previous respective term, then minimize their sum
against the actual previous selected kernel. The two-six term is zero.
Both exceptional and complementary families are included, so no new global
anchor addback is required.

## Production insertion

After the existing `one_term` is formed, and before assembling `split`, use
a separate `c == 6 and union == 13` branch:

```python
from wall1_six_thirteen_short_pairs import SIX_EIGHT_WITNESSES
one_term = min((one_term,
    I(min(one_count, SIX_EIGHT_WITNESSES))/coefficient_count
      *six_plane(6, I(47)/6, long_tail)**n
    + I(one_count)/coefficient_count
      *six_plane(6, I(17)/2, long_tail)**n), key=lambda x: x.b)
tail8 = iv.exp(-98*alpha)*half_sum
none_term = min((none_term,
    six_plane(8, 10, tail8)**n
    +six_plane(10, I(19)/2, tail8)**n
    +six_plane(12, 9, tail8)**n), key=lambda x: x.b)
```

The parent has integrated this branch. This worker edits only its standalone
script and note, never the shared evaluator.

## Verification and actual-selected gain

The pre-integration diagnostic used the returned
`six_circuit_split_parts[7,overlap]`, avoiding whole-execution tracing. It
first matched reconstructed old one-six/no-six terms against production to
relative tolerance 1e-60, then measured the complete improvement.

At the initial, weaker stage, using (8,8)+(10,15/2), the one-six term
improved about 30.17494 orders and the no-six term about
29.94332 orders. The actual old selected kernel was often much smaller than
that old split, so the correct selected improvements for overlaps 1,...,5
are only

    16.03645, 9.07656, 6.84912, 9.07656, 16.03645 orders.

In particular the requested overlap-five branch improves by about 16.04
orders, not thirty. The new no-six term exceeds the new one-six term by
about 6.24014 orders. These are local upper-envelope comparisons; they do
not certify an equal gain in the full h18/h19/h24 sums.

After integration, the diagnostic captures the unchanged generic Gaussian
candidate using one dictionary assignment inserted into an AST copy of
`draw14_bounds` in memory. This does not edit production or install a global
trace. It reconstructs the old selected kernel as the minimum of that
candidate and the old complete split, verifies production one-six, no-six,
and final selected kernels against the independent formulas to relative
1e-60, and reports both the original-baseline and previous-stage gains. The original
logs are preserved. With the stronger cover, no-six improves 52.93592 orders
against the original baseline, or 22.99260 orders against the weak stage.
Actual selected improvements against the original baseline, for overlaps
1,...,5, are

    22.27659, 15.31670, 13.08926, 15.31670, 22.27659 orders.

Against the preceding weak stage, every overlap improves approximately
6.24014 orders. The one-six term now exceeds no-six by 16.75246 orders, so
one-six is the local limiting family. All five production one-six/no-six/
selected comparisons match to relative 1e-60 with the stronger cover. These
remain local comparisons, not full-frontier gains.

Run `python3 docs/research/scripts/wall1_six_thirteen_short_pairs.py`.
Pre-integration log: `/tmp/wall1_six_thirteen_short_pairs.log`.
Integration-aware log: `/tmp/wall1_six_thirteen_short_pairs_integrated.log`.
Strong integration-aware log:
`/tmp/wall1_six_thirteen_short_pairs_strong_integrated.log`.
Full-frontier regression and the remaining BKZ proof are separate obligations.
