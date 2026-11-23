# Four-circuit planes on thirteen positions

The rank11/girth4 stratum after Part374 is led by t9/overlap3, with thirteen
positions. A row outside the first circuit C must cover all nine new
positions, and new parts of any two such rows are proportional.

A balanced norm-ten row covering these nine positions must be unit on ten
positions, since all other balanced norm-ten shapes have support at most
seven. It therefore uses exactly one old position. There are4*126=504
such lines up to sign.

## Family with a norm-four row

The unique norm-four row lies on C, with three possible balanced sign
patterns. Its inner product with any norm-ten extension has absolute
value1, hence Gram determinant39 and second squared GS length39/4.
A unit old/new minor certifies saturation. Count at most3*504=1512 pair
witnesses. There are no independent norm-six/eight rows, because they
cannot cover nine new positions. After charging the norm-ten family,
the second squared norm is at least12. Reducing against the first row
gives |dot|<=2 and second squared GS length at least11. The complete split
is the counted height39/4 kernel plus the existing one-count times the
height11 kernel, with the old cutoff40 tails and periodic corrections.

## Family without a norm-four row

A norm-six or norm-eight row cannot lie on the full four-position circuit:
the possible balanced shapes have support3 or6 for norm6, and2,5 or8 for
norm8. Nor can it cover nine new positions. Thus the first squared minimum
is at least10. If two norm-ten rows were outside C, orient their unit new
parts to agree. Their nonzero difference would lie on C but have support
at most2, a contradiction. Consequently, when both reduced row norms are
10, one row lies on C. Its shape is(2,-2,1,-1); its inner product with the
outside unit row is at most2 in absolute value. The second squared GS
length is then at least48/5. If the first squared norm is10 and the second
is at least12, Gauss reduction instead gives at least19/2. A first squared
norm at least12 uses the general bounds(12,9). Thus the complete cover
uses squared GS cases(10,19/2) and(12,9), retaining cutoff14 tails and all
periodic terms, and is minimized with the preceding complete bound.

The exact script verifies1512 norm-four/ten Gram identities and6048
old-ten/outside-ten inner-product bounds. The support argument supplies
coverage of all other shapes and excludes two outside norm-ten rows.
The implementation updates both families; unrelated coefficient classes
and anchor covers remain. This is not yet Lean formalized and does not
close the full residual budget or the adaptive BKZ distribution bridge.
