# Norm-six extensions of the triangular anchor

The selected size17 rank8/girth4 cover is dominated by the triangular
six-position anchor. Its t=4 crossing is largest, followed by t=3;
the raw t=2 crossing is replaced by the smaller parallel/marked cover.
Diagnostics: `/tmp/wall1_rank8_cover_current.log` and
`/tmp/wall1_triangle_rank8.log`.

For t=3,4,5 new positions, split third codes into those having a new
norm-four line, those having a norm-six line but no new norm-four line,
and the remaining codes. The first class retains the previous complete
norm-four witness bound. In the second class, the norm-six row must have
six unit entries: a (2,-1,-1) row cannot meet all t new coordinates and
have a nonzero old projection. It therefore has6-t old positions.

Enumerate all five balanced triangular patterns on old supports0123 and
2345 and all norm-six lines nonzero on every new coordinate. Exclude a
candidate when a balanced norm-four line belongs to the same rank-three
plane. New coordinates force the comparison scalar to be +/-1, so
membership reduces to whether the old difference lies in the old plane;
the exact Gram projection tests this. The old difference has squared
norm at most six, and its three-row minors have absolute value below10.
Thus membership over Q agrees with membership modulo3329. The enumeration
uses the original affine sign patterns rather than only an isometric
geometric representative.

For dot=<a,b>=+/-2, x=<a,v>, y=<b,v>, the third Gram determinant is
D=72-4x^2+2*dot*x*y-4y^2. Unit minors verify primitivity. Uniform counts
are componentwise maxima across the five patterns:

    t=3: {56:72,60:36,68:72,72:20}
    t=4: {56:18,60:72,68:60,72:18}
    t=5: {68:60}.

Each counted complete kernel has third squared height D/12. Counting
witnesses can overcount planes, which is safe. For the remaining family,
nearest-plane rounding has squared error at most4/3. With no new rows
of squared norm4 or6, girth four and the affine even-norm condition force
the rounded independent row to have squared norm at least8. Consequently
its projected squared length is at least8-4/3=20/3. Also retain t+2/3.
The lift is valid because q^2>8H. This applies to all integer vectors;
it is not inferred from bounded experimental samples.

Add the norm-four witness kernels, the classified norm-six kernels and
the full coefficient count times the no-four/no-six kernel. Retain every
cutoff30 tail and periodic layer, and take the minimum with both previous
complete bounds. This changes the actual crossing path used by the
larger-component envelope. It is not Lean formalized and does not prove
the complete adaptive BKZ theorem.

The full interval probe passes2106 cumulant regressions. Transfer through
sixteen remains below3.459e-13 (about3.45843778753e-13). Size17's weighted
residual log10 is1.9922807461, now led by rank10/girth4 and rank10/girth6.
The triangular part is at1.0138100612; the targeted rank8/girth4 term is
1.1381831384. Through24 remains about1.05489e232. The2.6629e-12 allowance
and adaptive BKZ bridge remain unproved. Logs: `/tmp/wall1_triangle_six.log`
and `/tmp/wall1_triangle_six_cumulants.log`. These are upper envelopes,
not actual failure-probability estimates.

## Norm-eight refinement

`scripts/wall1_triangle_eight_extensions.py` extends the exhaustive enumeration
to balanced rows of squared norm eight, including coefficient-two shapes.
For t=3,4,5, remove any candidate whose rational plane contains a new row
of norm four or six. To compare a candidate v and a shorter row w, test
`w_i*v_6 == w_6*v_i` on new coordinates, then test the old-plane projection
of `v_6*w-w_6*v`. This integer test also handles nonunit comparison scalars.
Every retained triple is checked to have a unit minor. Componentwise upper
witness counts across all five affine patterns are:

    t=3: {80:18,84:168,92:162,96:18}
    t=4: {80:90,84:144,92:246,96:36}
    t=5: {80:240,84:120,92:240,96:70}.

The keys are Gram determinants, computed as
`96-4*x*x+2*dot*x*y-4*y*y`; heights are determinant/12.
These are witness upper counts, not disjoint plane counts. Removing a
rationally dependent shorter row is safe because its dependence also holds
modulo3329; any additional modular coincidences only overcount the cover.
Girth four excludes shorter rows of support below four. A row confined to
the new coordinates would have zero old projection and is excluded by the
existing crossing hypothesis.

For the remaining family no independent row of squared norm four, six or
eight exists. The same covering-radius argument gives squared length at
least `10-4/3=26/3` after projection, retaining also `t+2/3`. The affine lift
uses `q^2>10H`. Add the three rare-row covers and the full coefficient count
times this remaining kernel. All cutoff-30 tails and periodic layers stay
in every kernel. Take the minimum with the previous complete cover.

### The t=4 norm-four exception is empty

The crossing construction chooses a nonzero old coefficient vector supported
on a fixed independent basis of the rank-four anchor. Thus its old component
is not in the two-dimensional anchor relation space P modulo q. Any new
relation independent of P in the resulting three-dimensional code is a
nonzero scalar multiple of that crossing modulo P, so it too has nonzero
old projection. A norm-four integer row nonzero on four new coordinates
must consist of four unit entries there and zero old entries. This is
impossible for the crossing code. Hence the t=4 norm-four exception count
is zero, rather than the previous conservative count three. This conclusion
uses the independent old basis and nonempty crossing coefficients, not merely
girth four. The production coefficient sum starts at old support size one.
