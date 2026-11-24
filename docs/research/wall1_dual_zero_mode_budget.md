# Completion-dual zero sector: baseline and remaining-frequency budget

At the actual production radius, the completion-dual zero sector has relative
factor F0 with log10 F0=-124.70687452 against the **same relaxed anchor theta
kernel**. This is a lower contribution to the new relaxed Gaussian expression,
not an upper bound on it and not a probability estimate. Bounding the remaining
frequencies is the entire new obligation.

## Exact reference and factorization

Use Eq. (13) of `wall1_mixed_gram_kernel.md`. Write W=[A,V], where A contains
the two nonbasis anchor columns and V the k=6 completion columns. Keep the
basis and extra-anchor temperatures fixed, and give each completion weight
gamma>0. Let T_A denote the anchor-only relaxed kernel (6), with precisely
the same fixed anchor temperatures. For fixed V, let T_V be the corresponding
full relaxed kernel. In the positive joint dual expansion retain all anchor
dual frequencies but set the six completion frequencies b_V to zero.
The surviving row sum is exactly

    z(gamma)^k T_A,  z(gamma)=sqrt(pi)/(q sqrt(gamma)).

In particular this is not merely the single frequency a=b_A=b_V=0. Keeping
all anchor frequencies is necessary to compare with the same anchor kernel.
For n=118 coordinate rows, retaining this sector in every row contributes
z(gamma)^(nk) T_A^n. There are q^(dk)=q^60 affine completion charts, d=r-1=10.
Their zero sectors are identical. Multiplying the six input-ball majorants
gives the exact relative lower contribution

    F0(gamma)=q^(dk) exp(k gamma R^2) z(gamma)^(nk).          (1)

The anchor ball factors and output factors are unchanged and cancel in this
comparison. There are no new output coordinates and no q^(-400k) factor.
This formula retains the same relaxed rank-enlarged domain as Eq. (6);
it is not a lower bound for the original centered, eligible configuration sum.

For each V define L(V)=T_V/[z(gamma)^k T_A]>=1. The whole relaxed completion
factor divided by this relaxed anchor is

    F0(gamma) * T(gamma),
    T(gamma)=q^(-60) sum_(affine V) L(V)^118 >=1.            (2)

All118 rows share the same V. A bound on the mean of L(V) cannot replace
the118th moment. For multiple anchor charts, (2) is averaged with their
nonnegative relaxed-anchor weights; the zero-sector factor is unchanged.
The nonzero-completion-frequency contribution relative to the zero sector
is T-1, not T. Bounds below are stated on the total T for convenience.

## Optimal zero-sector temperature and actual-radius calculation

With fixed n,k,R,

    d/dgamma log F0 = kR^2-nk/(2gamma),
    d^2/dgamma^2 log F0 = nk/(2gamma^2)>0.

Thus (1) has its unique minimum at gamma=n/(2R^2). This optimizes the zero
sector only: the correction T may move the optimum of the complete bound.
The production radius is computed locally as

    R^2=1.21*exp(2*(386log(3329)-log(V506))/506)-2,
    V506=pi^253/253!.

It gives R=2933.43724183307456 and gamma=6.85643572312505e-6. At this gamma,

| quantity | log10 |
|---|---:|
| zero-sector relative contribution F0 | -124.70687451768 |
| current completion cap M10^6 | 210.49605822720 |
| allowed total/zero multiplier to beat that cap | 335.20293274488 |

Here M10=min(q^10,V10*(R+sqrt(10)/2)^10), at the same actual radius.
If the anchor reference is unchanged, it would suffice to prove
T<10^335.20293274488 to improve the current cap. Equivalently the remaining
nonzero contribution must be below F0*(10^335.20293274488-1). No such bound
has been established by this calculation.

## Conditional target budget and anchor-reference mismatch

Suppose, conditionally, that the current leading-envelope term is
A_ref*M10^6 with log10 equal to39.9478, and that replacing its anchor factor
by the relaxed-anchor expression costs a multiplier C_A=A_rel/A_ref.
C_A is not known from the zero-sector calculation; a different theta
relaxation need not equal the previously selected anchor envelope.
The new relaxed bound has the comparison form

    A_ref * C_A * F0 * T.

Therefore the necessary upper-bound obligations are

    log10 C_A + log10 T <335.20293274488        (beat old bound),
    log10 C_A + log10 T <-12-39.9478
                             +log10 M10^6-log10 F0
                           =283.25513274488    (reach1e-12).

With C_A=1 the zero contribution alone would have term log10
-295.25513274488. That number is only the baseline of this conditional
comparison, not an upper estimate for the full term. The39.9478 input is a
rounded target-envelope reference, not a revalidated exact production term;
if its certified value is L, replace39.9478 by L throughout.

For a **uniform** row ratio bound L(V)<=B, the corresponding sufficient
row budgets when C_A=1 are log10 B<2.84070281987 to beat the old cap and
log10 B<2.40046722665 for the target. More generally those numbers describe
T^(1/118), not an independent-row expectation. Anchor-reference loss
log10 C_A must be subtracted before division by118.

## Scope and verification

This leaves substantial numerical room for a nonzero-frequency bound, but
supplies no control of that correction or of C_A. It neither proves a new
completion cap nor rules out the method. Eligibility, coefficient weights,
and restricted-anchor scope must match when establishing C_A and T.

Run `python3 docs/research/scripts/wall1_dual_zero_mode_budget.py`.
Log: `/tmp/wall1_dual_zero_mode_budget.log`. All displayed intervals use
70-digit interval arithmetic and the same locally computed production radius.
No heavy evaluator is imported and no production files are changed.
