# Additional norm-four lines over triangular anchors

Part320 leaves a triangular-anchor extension among the leading size16
terms. Extend Part315's exceptional-line split to these anchors, including
the signed oriented-difference patterns as well as equal-pair-sum patterns.

## Geometry without changing the affine normal

Work with the original balanced norm-four integer generators a,b. Flip
one entire row if necessary to make their inner product two. This keeps
both coordinate sums zero. The triangle (0,a,b) is equilateral with
squared side length four; its circumcenter (a+b)/3 has squared distance
4/3 from each vertex. Triangulating a fundamental parallelogram and using
the barycentric squared-distance identity gives squared covering radius
at most4/3 for the old plane lattice. The old plane is primitive.

This argument applies to all five triangular patterns because it only
uses the two balanced rows' Gram matrix. It does not change individual
coordinate signs or replace the affine normal by an unverified one.

For any integer vector outside the old plane in the saturated short
three-dimensional relation lattice, subtract a nearest old-plane lattice
point. If the squared perpendicular height were less than14/3, the
reduced vector would have squared norm less than six. Since q^2>6H,
its affine modular sum condition forces its integer sum to vanish. Its
norm is even and nonzero; distinctness excludes norm two. Thus it is an
additional balanced norm-four line. On codes with no such line the third
squared height is at least14/3. Combine this with the old t+2/3 bound by
taking their maximum. The old theta factors remain theta(4 alpha) and
theta(3 alpha), with the entire long tail and periodic corrections kept.

## Exceptional counting and integration

With t fixed new positions and a fixed independent old basis, every
codeword outside the old plane has all t new entries nonzero. There are
at most3*choose(6,4-t) balanced norm-four lines of this kind for t<=4.
Each determines at most one third code and normalized fundamental
relation; extra witnesses only overcount. For coefficient count Q use

    min(Q*J_old,
        3*choose(6,4-t)*J_unrestricted + Q*J_no4).

Here J_old may include the smaller earlier product bound. The exceptional
branch uses the unrestricted fixed-plane bound. For t>4 the implementation
retains its old cover. No exceptional family is removed without its term.

The weighted bound is used for the rank-four dependent-point branch,
every crossing term, and marked parallel pairs at component sizes14..24.
It also replaces the coefficient-times-joint term in the size14 rank5
baseline, so the admitted lower-size transfer uses the same improvement.
Position counts, quotient-basis divisors, unmarked parallel alternatives,
and all other anchor families remain unchanged.

The exact regression includes both equal-pair and oriented-difference
representatives. Across all six tested old-plane types it passes41066
integer-vector reduction checks and24 rare-line counts. The all-vector
covering proof and the universal balanced-line count above justify the
extension beyond these finite checks. This is not a Lean formalization
or a completed adaptive BKZ proof.

## Verified outcome

The full cumulant probe passes2106 exact regressions. Transfer through
fifteen is about5.2830384913e-13, still below the retained cap5.295e-13.
The sufficient residual allocation remains2.4793e-12 for sizes16..24
plus the later selected-history probability; it is not established.

Size16's full weighted residual log10 is -2.1874969613. Its triangular
part has log10 -3.3751772138 and the rank5/girth4 term is no longer among
the five largest strata. The leading terms are rank8/girth3 at
-2.5148446833 and rank7/girth4 at -2.5855673479. The through24 envelope
remains about1.71e233. Thus the new split improves a genuine obstruction
but does not provide the required overall probability bound.

An initial numerical run encountered an interval-comparison exception
at t=4, where t+2/3 equals14/3 exactly. The implementation now compares
the integer numerators max(3t+2,14), then divides outwardly by three.
Direct checks verify strict improvement at t=1..3, overlap of the equal
bounds at t>=4, and monotonicity of the complete weighted cover. The
reported full runs completed after this repair.
