# A six-position determinant20 anchor in girth three

Part325 leaves Part322's determinant20 planes as the main girth-three
obstruction. Cover the components containing such a plane separately,
retaining a third relation instead of extending every point freely.

## Geometry and anchor count

In balanced coordinates take

    a=(1,1,-1,-1,0,0), b=(2,0,0,0,-1,-1).

Their Gram matrix is [[4,2],[2,6]] and they span a primitive plane, since
an exclusive unit coordinate in each row recovers the coefficients.
After coordinate signs, use a=(1,1,1,1,0,0), b=(2,0,0,0,1,1). For integer v,
write S=v1+v2+v3 and T=v4+v5. Its squared projection off the plane is

    D(v)=sum_(1<=i<j<4)(vi-vj)^2/3
         +(v4-v5)^2/2+(3v0-S-3T)^2/30.

A nonconstant triple contributes at least2/3 and a nonconstant pair at
least1/2. If both groups are constant, the last numerator is divisible
by nine. Thus D(v)>0 implies D(v)>=3/10. The zero case is exactly the
integer plane, with v0=v1+2v4. The argument does not assume the affine
normal is unchanged by coordinate sign flips.

Enumerating balanced norm-four rows and norm-six rows of support three,
with full union six and dot product of absolute value two, gives180
witness pairs on six labeled positions. These cover all the eligible
determinant20 planes in Part322; each contains the (2,-1,-1) line.
Equivalently choose its three-support, its doubled position, and one of
three balanced norm-four lines on that position plus the other three:
choose(6,3)*3*3=180. Counting witness pairs is safe even without deduplication.

For a crossing supported on an independent old basis, the old part has
nonzero projection, hence the third squared height is at least t+3/10.
Use the old squared heights4 and5, cutoff27 with20*27^4<3329^2, and retain
all long Gaussian tails and periodic terms. The old plane's squared
covering radius is at most9/5. Without an additional balanced norm-four
line, the third height is also at least21/5 by the previous reduction
argument: distinctness still excludes norm two even though girth is three.
Count the exceptional lines by3*choose(6,4-t) and keep both branches.

## Adapting the extension cover to girth three

The anchor has size6 and rank4. For one dependent point the old support
must have at least two entries, not three, so retain
sum_(a=2)^4 choose(4,a) q^(a-1). For a crossing with t new positions use
old support a>=max(1,3-t), with coefficient factor q^(t+a-2). For marked
parallel pairs include a=1 as well, giving sum_(a=1)^4 choose(4,a) q^a.
Omitting these terms would incorrectly assume girth four.

All position choices, free-point factors, completion counts, the
coloop-free quotient basis divisor, and parallel alternatives follow the
existing anchor cover. A proper rank4 anchor already has nullity two;
a connected whole support of nullity two cannot contain it with outside
coloops. The rank h-2 branch is therefore empty, as in the earlier covers.

In the girth-three family split supports into those containing an
eligible six-position determinant20 anchor and those containing none.
Only the latter's c=3,t=3 estimate removes the three determinant20 codes.
Add the new complete anchor cover and take the minimum with the previous
full bound. Girth-four families are not changed.

The exact regression checks15625 projection identities and180 witnesses.
The displayed decomposition proves the projection bound for every integer
vector; the finite check is supplementary. The component bound keeps
all exceptional families. This work is not Lean formalization or a
complete proof of the residual and adaptive selected-history obligations.

## Verified outcome

The exact Part322 plane-key enumeration additionally checks that every
removed determinant20 code contains a balanced norm-six line on the
prescribed three-support. This confirms coverage by the180 witness
anchors, at q=7,17,3329. The complete cumulant probe passes2106 exact
regressions and retains transfer through fifteen below3.419e-13.

Size16's full weighted residual log10 is -9.8426902202, about1.44e-10.
It is now dominated by rank8/girth4 at -9.8477666465. The sufficient
residual allocation for sizes16..24 plus later histories is2.6669e-12,
so even size16 alone is not yet controlled by that allocation. The
through24 envelope remains about1.61e232. No complete draw14 exit,
selected-history or BKZ theorem is established.
