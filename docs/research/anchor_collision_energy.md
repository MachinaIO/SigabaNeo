# Same-span anchor energy and connected union incidences

This gives an aggregate bound on the weighted span-collision energy from
[Weighted completion](wall1_weighted_completion.md). It reduces that energy to
higher connected full-incidence counts, without assuming independence of a span
and its selecting anchors. The reduction is valid for actual incidence weights.
It also exposes a quantitative loss and a higher-order obligation that prevent
it from closing the current completion bound as it stands.

## 1. Actual incidence weights and a common-map second moment

Fix the candidate fibers B_y and a uniform affine map F:F_q^n -> F_q^m.
An eligible anchor A is an ordered list of H distinct inputs, with augmented
rank r, and connected augmented-input matroid. Put

    I_A(F) = product_(y in A) 1{F(y) in B_y},
    w(A) = E_F I_A(F),
    U(A) = affine span of A,   dim U(A)=r-1.

For each affine (r-1)-plane U, let

    N_U(F) = sum_(eligible A: U(A)=U) I_A(F),
    W_U = E_F N_U(F),
    E = sum_U W_U^2,       D = sum_U E_F[N_U(F)^2].               (1)

The symbol E on the left denotes energy, not an expectation operator. Then

    E <= D,       D-E = sum_U Var_F(N_U(F)).                     (2)

This is Jensen applied separately to each U. Equivalently, E uses two
independent maps F,G and counts N_U(F)N_U(G), whereas D uses the same map twice.
No conditioning on a selected anchor or independent-plane approximation occurs.
In particular, varying anchors are averaged before applying (2), avoiding the
fixed-full-anchor singleton degeneracy.

The variance loss in (2) can be large. Knowing only E_F N_U does not bound its
variance sharply, so replacing two independent maps by one is an upper-bound
step, not an equality. Nonnegative deterministic witness weights can be inserted
inside N_U without changing (2); the counting comparison below must then retain
their products.

## 2. Why a pointwise gluing argument is invalid

It is generally false that w(A)w(A') <= P(A union A'), even when both anchors are
connected and span the same affine space. For q=5, use scalar input and output,
with fibers

    B_0=B_1=B_2={0,1}, B_3={0}, B_4={1}.

Take A=(0,1,2,3), A'=(0,1,2,4). Both have rank r=2, H=r+2=4, and connected
input matroids. The first event requires the constant-zero map and the second
the constant-one map. A nonconstant affine map has three distinct values on
0,1,2, so cannot meet those three two-element fibers. Thus

    P(A)=P(A')=1/25,  P(A union A')=0.

This is a counterexample for general fibers, not a counterexample for centered
ball fibers. It shows that rank and shared-span conditions alone do not justify
pairwise gluing. The aggregate square (2) nevertheless remains valid, because
it includes all pairs from the same anchor family, including its diagonal.
A proposed ball-specific pairwise inequality would require a separate proof.

## 3. Connected unions and the exact overlap coefficients

Two connected anchor matroids of positive rank with the same full span have a
connected union. To prove this, each anchor must lie within one connected
component of the union. If their components differed, those component spans
would have zero intersection in a represented matroid. But both anchor spans
are the same nonzero r-dimensional augmented-input space. Therefore they lie
in the same component, and together exhaust the union. Its augmented rank is r.

Let F_(ell,r) be the existing ordered full-incidence count restricted to
connected ell-input supports of rank r. Assume each eligible ordered anchor
list appears at most once. Expanding D in (1) and sorting by the number i of
shared inputs gives

    D <= sum_(i=0)^H choose(H,i)^2 i! F_(2H-i,r).                (3)

Here F_(ell,r)=0 when no such support exists. To justify the coefficient, list
A first in its given order and then the H-i inputs of A' not in A in their
given order. This is an ordered union list of length 2H-i. Choose the i shared
positions in A' and inject them into A's H ordered positions: the number is
choose(H,i)*(H)_i=choose(H,i)^2 i!. The prescribed interleaving reconstructs
A' uniquely. Every eligible pair contributes the exact joint probability of
its union, because I_A I_A'=I_(A union A'). Dropping eligibility of the two
reconstructed subanchors only enlarges the sum. Connectivity and rank are
retained by the preceding argument.

For rank-two line anchors consisting of every ordered H-subset of the occupied
line, (3) is equality. It is then the falling-factorial identity

    (C)_H^2 = sum_i choose(H,i)^2 i! (C)_(2H-i)

averaged over the map and summed over lines. For a restricted circuit shape,
(3) generally has slack.

If a support has multiple coefficient-chart or anchor-witness descriptions,
one must either use a canonical description, sum their actual weights in N_U,
or supply a uniform multiplicity bound K. In the last case the right side of
(3) is multiplied by K^2. The formula with coefficient one does not silently
apply to arbitrary duplicated chart descriptions.

## 4. The resulting sufficient collision estimate

Let L be the number of affine (r-1)-planes in the chosen common reference family
and Z=sum_U W_U. All actual anchors must belong to that family. For the
unrestricted reference one obtains

    chi = L E/Z^2 - 1
        <= L/Z^2 * sum_i choose(H,i)^2 i! F_(2H-i,r) - 1.        (4)

Use the actual reference moments of f(U)=C(U)^j or another justified completion
statistic in the weighted-completion CS bound. If its mean is mu_f, variance
v_f>0, and the desired weighted average is T>mu_f, a sufficient condition is

    sum_i choose(H,i)^2 i! F_(2H-i,r)
       <= (Z^2/L) * (1+(T-mu_f)^2/v_f).                         (5)

This is a concrete rank-doubling-size reduction. The rank itself remains r;
the union can have up to 2H points and correspondingly higher nullity. It is
not merely the definition of E, since it replaces unknown same-span pairs by
existing single-map connected-incidence quantities with explicit coefficients.
It may still be quantitatively much weaker than directly bounding E.

If applying a normalized form of (4), an upper bound on F alone and an upper
bound on Z are insufficient: the denominator requires a justified lower bound
on the actual Z, or the calculation must instead retain the unnormalized
weighted-completion inequality with consistent bounds. An exact upper-envelope
value must not be substituted for Z in a denominator.

## 5. Gaussian majorants: what can and cannot be substituted

The current Gaussian anchor calculations give upper bounds on actual incidence
sums by relaxing constraints. For the actual w(A) above, rigorous higher
full-incidence envelopes may be inserted into (3) after (3) has been proved.
One must not first replace w(A) by an arbitrary Gaussian upper envelope and
then assert that its squared energy is bounded by the actual F_(ell,r).
Pointwise enlargement changes the energy and its normalization.

More generally, if a nonnegative Gaussian random majorant G_A(F)>=I_A(F) is
explicitly defined, Jensen still gives

    sum_U (E_F sum_(A:U(A)=U) G_A(F))^2
       <= sum_U E_F[(sum_(A:U(A)=U) G_A(F))^2].                 (6)

But the product G_A G_A' is a doubled-weight Gaussian kernel. At shared inputs
its Gaussian exponent is doubled, and any auxiliary output summations and
coefficient restrictions must remain. It is not automatically the existing
unweighted union-incidence kernel. Thus (6) indicates a possible anisotropic
Gaussian calculation, but no useful production upper bound for it is supplied
here. Two independent affine output maps also cannot simply be identified:
incompatible output restrictions have positive independent-map weight, as in
Section 2.

## 6. Quantified obstacle at H=r+2

The dominant full-anchor case H=r+2 requires connected union sizes

    r+2 <= ell <= 2r+4,   union nullity ell-r.                   (7)

The existing degree-24 connected-incidence pipeline contains all these sizes
only when r<=10. For r>=11, the largest required size exceeds 24; a degree-24
moment calculation does not supply those missing envelopes. Even when r<=10,
the upper end of (7) requests higher-nullity counts at the same rank that are
at least as challenging as the existing residual families. Using their current
uniform-completion envelopes merely feeds the original weak completion bounds
back into (5). This is a specific potential circularity, not an impossibility
claim: independently stronger union kernels or direct collision estimates could
break it.

The overlap weights are explicit additional losses. The identical-support term
has coefficient H!, and the disjoint-support term has coefficient one but needs
F_(2H,r). These terms cannot be omitted because the two independent anchors may
share any number of inputs. Only a separate structural exclusion can remove an
overlap class. No selected-history independence follows from this reduction.

## 7. Exact ball-fiber tests

The checker uses scalar output, two-dimensional input, and the actual centered
raw ball in three dimensions. It enumerates every affine map, every affine input
line, and its number C of successful inputs. Every ordered four-tuple of distinct
successful inputs on a line is an eligible rank-two connected anchor. Thus
N_U=(C)_4 and the union formula is exact through size eight.

| q | R^2 | Z | E | D | D/E | exact chi | chi upper from D |
|---|---:|---:|---:|---:|---:|---:|---:|
| 5 | 4 | 48/5 | 1152/25 | 1152 | 25 | 14 | 374 |
| 7 | 9 | 23616/49 | 771840/49 | 3297024/49 | 1431/335 | 84647/30258 | 51175/3362 |

The first example exhibits a factor-25 loss from the common-map second moment,
even with exact union counts. The second loses about 4.27. These are exact finite
ball examples of the reduction's cost, not extrapolations to q=3329. They also
confirm all overlap coefficients by equality with the direct diagonal second
moment. The checker separately verifies the incompatible-pair example and
aggregate Jensen for that same two-anchor family.

Run `python3 docs/research/scripts/anchor_collision_energy.py`.
Log: `/tmp/anchor_collision_energy.log`. All arithmetic is exact rational.
Only this new note and checker were written. No production evaluator, previously
validated weighted-completion files, or Lean theorem was changed. The result
provides a rigorous possible route and a quantified obstruction, not a new
numerical global residual or a completed BKZ proof.
