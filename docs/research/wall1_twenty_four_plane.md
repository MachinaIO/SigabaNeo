# Eight-position orthogonal norm-four/norm-six anchors

The leading size16 rank8/girth4 terms after Part326 have c=4,t=4 and
old overlaps2,3. Their surviving determinant24 planes have orthogonal
norm-four and norm-six generators. Cover their extensions separately.

## Projection certificate for every integer vector

After coordinate signs and permutations, use

    a=(1,1,1,1,0,0,0,0), b=(1,-1,0,0,1,1,1,1).

Their Gram matrix is diag(4,6). Exclusive unit coordinates make the
plane primitive. Rounding its two orthogonal coefficients gives squared
in-plane error at most4/4+6/4=5/2.

Suppose an integer vector had positive squared projection D<7/12 off
the plane. Subtract the rounded integer combination of a,b. The resulting
integer vector w has the same projection and

    ||w||^2 <= D+5/2 < 37/12.

Thus ||w||^2<=3. Every such integer vector has entries in {-1,0,1} and
at most three nonzero coordinates. There are exactly577 of them. The
exhaustive rational calculation

    D(w)=||w||^2-<a,w>^2/4-<b,w>^2/6

checks D(w)=0 or D(w)>=7/12 in every case, contradicting the supposition.
This is a finite certificate of the all-integer inequality, not merely
a cube sample used to guess a minimum. Equality occurs at the first
coordinate unit vector. Coordinate isometries preserve this statement.

## Counting and extension

Fix the first four-support. Enumerate its three balanced sign lines
and every balanced norm-six line nonzero on the other four positions,
with inner product zero. There are84 pairs, hence
choose(8,4)*84=5880 anchors on eight labeled positions. Their integer
plane has norm form4m^2+6n^2, so its norm-four and norm-six lines are
unique. No witness multiplicity divisor is needed.

For a crossing using an independent old basis and t new positions,
the third squared height is at least t+7/12. The old squared heights
are4 and6. Use cutoff26;24*26^4<3329^2. Retain the complete long Gaussian
tail and periodic layers. For the anchor alone retain the existing
two-row cutoff40 argument.

The same squared covering-radius bound5/2 gives third height at least
7/2 on codes with no new balanced norm-four line, by the affine reduction
and distinctness argument. Count exceptional lines by3*choose(8,4-t)
and keep both families. This argument is made in the original balanced
coordinates; coordinate sign changes are only used in the projection
certificate and not to change the affine condition.

Use the size8, rank6 anchor extension cover, including dependent points,
all crossing sizes, parallel alternatives and marked pairs. The global
girth-four family is split into earlier anchor families, this new family,
and the family with none. Only the last family's eight-position
two-relation bound removes determinant24 summands. The full sum is
compared with the previous complete bound; no exceptional family or
modular tail is omitted. The new classification does not remove the
six-position determinant24 codes of Part325, which are a different family.

The projection certificate and84-pair enumeration pass exactly. This
computer-assisted geometry and the analytic envelope are not yet Lean
formalized, and do not alone establish the remaining BKZ obligations.

## Girth-filtered dependent point

With a=(1,1,-1,-1,0,0,0,0,0), balanced orthogonal norm-six rows on the
eight old positions have two affine sign types, represented by

    b1=(1,-1,0,0,1,1,-1,-1,0),
    b2=(1,0,1,0,1,-1,-1,-1,0).

The distinction is whether a's entries on the two common positions
have equal or opposite signs. Orthogonality fixes b's relative signs
there, and the remaining balanced entries are fixed up to permutations.
Thus both types cover all anchors without changing the affine normal.

For each type enumerate all168 additional balanced norm-four lines v
nonzero on the ninth position. Writing x=<a,v>, y=<b,v>, their Gram
determinant is D=96-6x^2-4y^2. Test all84 complementary six-column
supports for rank three. All minors have absolute value below seven,
so the test is exact at q=3329; a unit minor establishes a primitive
integer row basis in every case.

The uniform per-stratum upper counts across both types are

    D:      54 56 60 68 72 74 80 86 90 92 96
    count:  12 16  8 16 16 20 14 26 18 20 10.

They deliberately overcount by taking the maximum in each stratum.
All determinant38/42 candidates fail girth four. The surviving third
squared heights D/24 are at least9/4. Replace the one-point exceptional
term by the displayed sum of complete J_D bounds and keep the full
nonexceptional term, long tail and periodic layers. This changes only
the same-rank dependent branch; other extensions remain as before.
The exact regression checks336 lines and all complementary supports.

## Outcome and failed size16 admission

The complete cumulant probe passes2106 exact regressions and now prints
the size16 cutoff explicitly. Transfer through fifteen remains below
3.419e-13. Transfer through sixteen is about3.5070600055e-12, exceeding
the required3.01e-12 cumulant-transfer target. Size16 is therefore not
admitted. The dependent-point refinement above changes this total only
negligibly; it does not remove the current leading component.

The full weighted size16 residual before that negligible refinement
has log10 -11.4996024296 (about3.17e-12), led by rank8/girth4 at
-11.5977845026 and rank6/girth4 at -12.2735305493. It still exceeds the
2.6669e-12 allowance for all sizes16..24 plus later selected histories.
The through24 envelope remains about1.61e232. This is an ineffective
upper bound, not an estimated or lower-bounded failure probability.
The later-history and complete BKZ proof obligations remain open.
