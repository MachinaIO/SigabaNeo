# Independent-map energy and a nineteen-point mixed-fiber alternative

Two independent affine output maps give an exact colored incidence model
for weighted same-span energy, avoiding the Jensen replacement by one map.
They do not remove the need for union sizes25 and26 at H=13. A different,
direct pinned-completion moment uses only nineteen points, but its output
constraints differ from the existing joint-ball kernels. This note derives
both normalizations and their finite Gaussian kernels. It supplies no new
production estimate and changes no production file.

## Exact independent-map model

Let inputs lie in F_q^n and outputs in F_q^m. Let B_y be the allowed output
fiber at input y. An eligible anchor A has H distinct inputs, augmented
rank r, and a connected augmented matroid. Put

    I_A(F)=product_(y in A) 1{F(y) in B_y},
    w(A)=E_F I_A(F), W_U=sum_(A:span_aff A=U) w(A),
    E=sum_U W_U^2.

All sums retain the actual anchor eligibility; the displayed definitions
count each eligible anchor once. Fixed nonnegative witness weights omega(A),
independent of the output map, are allowed by replacing w(A) with
omega(A)*E_F I_A(F) and N_U(F) with sum_A omega(A)*I_A(F). Pair sums
then retain omega(A)*omega(A'). No Gaussian upper envelope is substituted
for the actual incidence weight in this identity.
For independent uniform affine maps F and G,

    E=E_(F,G) sum_U N_U(F)N_U(G),
    N_U(F)=sum_(A:span_aff A=U) I_A(F).                       (1)

Fix a pair A,A' with the same affine (r-1)-span U. Restrictions F|U and
G|U are independent and uniform among q^(mr) affine maps each. If Y is
the union of their inputs, write I,J for the anchor position sets in Y.
Allowed output lists on I are exactly those satisfying the affine
relations of Y_I, and similarly on J. Each such list extends uniquely to
an affine map on U. Hence the pair weight is exactly

    q^(-2mr) * #{(z_I,z'_J): z_I respects relations of Y_I,
                    z'_J respects relations of Y_J,
                    z_y in B_y (y in I), z'_y in B_y (y in J)}.   (2)

At a shared input the two outputs are independent variables; equality is
not imposed. Equivalently use one map into F_q^(2m), with fiber B_y x B_y
on I intersect J, B_y x F_q^m on I minus J, and F_q^m x B_y on J minus I.
Absent-layer outputs are determined by the corresponding spanning anchor;
marginalizing them introduces no extra q factor. The normalization is
q^(-2mr), not q^(-m*r) and not q^(-2m*|Y|).

For centered raw-ball fibers, the shared-input condition consists of two
inequalities ||y||^2+||z||^2<=R^2 and ||y||^2+||z'||^2<=R^2.
It is not the ordinary ball inequality ||y||^2+||z||^2+||z'||^2<=R^2.
For example y=0,z=z'=2,R^2=4 satisfies both original conditions but fails
the latter. This prevents reuse of a single ordinary doubled-output ball.

## A precise factorized Gaussian bound for a fixed union chart

For an ell-position relation code K of dimension ell-r, define the finite
Gaussian sum

    S_K(beta;d)=sum_(x in F_q^ell, K*x=0)
                    exp(-beta*sum_j d_j*[x_j]^2),

where [x_j] is the centered representative. For an anchor set I of size H,
K_I consists of the rows of K supported on I, restricted to I. Because
that anchor spans the full rank-r union, dim K_I=H-r; likewise for J.
Set d_j=1_I(j)+1_J(j), either one or two. Multiplying the 2H ball
majorants in (2) gives the fixed-chart bound

    exp(2H*beta*R^2)/q^(2mr)
       *S_K(beta;d)^n*S_(K_I)(beta;1)^m*S_(K_J)(beta;1)^m.   (3)

The exponent on the shared input is doubled, while each separate output
has its own single weight. The input and the two output coordinate blocks
factor because their modular relation constraints are separate once the
chart is fixed. Lower-rank or repeated-input solutions can be included in
the Gaussian sums as a nonnegative enlargement of the original domain;
this does not change the fixed q^(-2mr) factor of the valid rank-r terms.
The actual coefficient-chart counts and repeated-description weights must
still multiply (3). In particular one may not replace the three different
Gaussian factors by a single equal-weight kernel raised to n+2m.

Formula (3) avoids Jensen exactly. It does not establish that the
same-span weights are close to uniform. A normalized chi-square bound
would still require the appropriate energy upper bound and a justified
normalization, including a lower bound on actual Z where Z occurs in a
denominator.

## Why energy still needs input unions beyond degree24

If two H=13 anchors overlap in i inputs, their union has ell=26-i positions.
The i=0 and i=1 classes require ell=26 and25. Independent maps change the
output model and normalization, not this input count. Both overlap classes
occur for connected rank-eleven ball anchors: use the explicit H13 anchor
A in `wall1_girth_four_completion_obstruction.md`. The reflected anchor
-A has exactly one input in common with A; the translated anchor A+3e1
has none. All these points lie in the radius2933 ball at q=3329, and all
three anchors span the same coordinate ten-plane. Reflection and
translation preserve the connected balanced relation code and girth four.
The zero affine output map meets every fiber, so each pair has strictly
positive independent-map incidence weight.

These examples establish the obligation for the general eligible family;
they have not been audited against every current excluded-anchor residual.
Dropping these classes in a restricted family requires a separate exclusion
proof. Even when an exact coefficient-chart treatment avoids explicitly
naming a degree26 moment, the rank-r input constraints and multiplicity for
those 26-position configurations remain to be bounded.

## Direct pinned completion: nineteen positions instead

Let C(U) count inputs in the centered radius-R input ball intersected with
U. For anchors with nonzero incidence weight, all H anchor inputs belong
to this ball. For k additional ordered distinct inputs, define

    T_k=sum_A w(A)*(C(U(A))-H)_k.                            (4)

This is the exact weighted distinct completion count before imposing any
additional girth or output-incidence constraints on the k new positions.
It upper-bounds the corresponding production completions. Expanding (4)
requires only H+k input positions: anchors obey the joint input/output ball
constraint, while new positions obey only the input ball constraint and
membership in U(A). For a fixed extended input tuple of augmented rank r,
only the anchor output values are restricted, so the exact map
normalization remains q^(-mr).

For a fixed relation code K on H+k positions, dim K=H+k-r and its
anchor-supported subcode K_A has dimension H-r. With a common beta,
Gaussian majorization yields the complete fixed-chart bound

    exp((H+k)*beta*R^2)/q^(mr)
          *S_K(beta;1)^n*S_(K_A)(beta;1)^m.                  (5)

More generally the anchor and new input blocks may use different positive
beta values, with the anchor output block using the anchor beta. This does
not introduce output constraints at the new positions. All dependent-input
coefficient charts must still be counted, or summed with their exact
weights; there is no factor q^(-mk) for these dependent completions.

For the leading H=13,r=11,k=6 case, (5) is a nineteen-input model with
input relation dimension8 and anchor-output relation dimension2. Thus
this direct route genuinely avoids degree25/26 energy moments. However,
the ordinary nineteen-point joint-ball kernel imposes output ball
constraints on all nineteen positions. It is a smaller event and cannot
upper-bound (4). The new task is a mixed-fiber Gaussian/chart estimate with
these asymmetric relation dimensions. Applying the old q^10-style uniform
completion bound to its input block simply recovers the existing weak
bound; no useful numerical improvement has yet been proved.

## Exact finite verification

The checker uses centered balls over F5, two input coordinates, scalar
output, H=3, and all thirty affine input lines. Every restriction map is
explicitly counted, and the q^3 ambient affine maps are checked to have
q equal preimages over each of the q^2 restriction maps. With each unordered
anchor counted once, independent colored energy is 338/125 whereas the
same-map energy is 298/25. The exact values differ, confirming that the
independent model avoids the Jensen loss rather than identifying the maps.

Sixty exact checks verify the pinned mixed-fiber identities for k=1,2 and
their Gaussian majorants with beta=log2. The mixed moments are 104/25,
while the ordinary joint-ball completion moments are 8/5: substituting the
latter would undercount. The script also checks the H13 union25/26 ball
fixtures. These tests validate finite identities, not the high-dimensional
Gaussian estimate or the selected-history bridge.

Run `python3 docs/research/scripts/wall1_independent_map_energy.py`.
Log: `/tmp/wall1_independent_map_energy.log`.
