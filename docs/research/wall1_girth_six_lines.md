# Short-line splitting at girth six

Extend Part 300's norm-six split to first circuits of size six. A norm-six
affine row must again be balanced +/-1 on six positions. Unlike the
five-circuit case, the first circuit itself has ten possible short lines.
With H=6+t, K=10 choose(H,6), and Q=q^(t+a+2), the one-line coefficient
count is bounded by

    min(Q, 10*q^(t+a-2) + 1_(t<=5)*K*q^4).

The first term retains first-circuit short rows; the second counts an
independent short row and vanishes when external support forces weight
at least seven. The earlier code must not simply reuse the girth-five
count, which omits that first term.

Two independent norm-six lines give at most K^2 normalized coefficient
pairs. Their support union is H. Girth six excludes H<=7: one of the
two cancelling mixed directions has weight at most four. H>12 is
impossible; H=12 consists of disjoint supports, whose only six-support
directions are the two generators. Every mixed direction then contains
all first-circuit positions, so no prescribed second circuit can have
a proper nonempty old overlap. Only H=8,9,10,11 remain.

The two balanced rows have lengths squared six. In H=8 their overlap
has four positions. Girth six forces two equal-sign and two opposite-sign
ratios there, since cancelling three positions would give weight five.
Their inner product is therefore zero. For H=10 and H=11, the overlaps
have two and one positions, giving inner-product magnitudes at most two
and exactly one. Consequently their squared Gram--Schmidt heights are
at least 6, 16/3, and 35/6, respectively. For H=9 use the general 9/2.

These rows generate their saturated real-plane lattice: exclusive
coordinates give a two-by-two minor of magnitude one. Thus the displayed
Gram--Schmidt bounds can be used directly in the two-short-line theta
product. The exactly-one and no-short factors remain (6,13/2) and (8,6).
All coefficient caps, cutoff-36 or cutoff-14 long tails, and periodic
terms are retained. Take the minimum with all previous full bounds.

Exact classification checks cover 948 girth-six pair cases across the
two regression fields, including the orthogonality and overlap assertions.
The supporting proof is above and applies at q=3329. The full BKZ and
selected-history proof obligations remain open; no Lean proof is claimed.

The size-fifteen full residual weighted log10 decreases from -3.67322
to -4.86704 (about 1.36e-5). Girth-six terms leave the five largest
no-double-short strata; girths four and three now dominate that remainder.
The entire residual budget is still unmet by millions of times even
before accounting for the larger sizes and later selected histories.
