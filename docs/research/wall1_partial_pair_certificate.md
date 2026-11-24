# Partial-gate certificates for the selected pair bound

The [selected pair evaluator](wall1_selected_pair_collision.md) assumes a
complete gate excluding zero candidate labels. Processing only some
old-minimum conditions invalidates that assumption. The extension retains
zero-label subtractions and gives moment intervals at every processed prefix.
It specializes Part 469's nonnegative remainder method to the pair bound.

## Exact moments at incomplete gates

Fix the stratum, h>1, candidate family S and positive center mu. Let Q_W(C)
be the unconditional mass with processed gate W and quotient constraints C.
Extra positive full or quotient constraints can be added to evaluate residual
bad-event intersections. With U!=0 understood, the moments are

    M0(W) = (h−1) Q_W(empty)/h,
    M1(W) = sum_x [Q_W(empty)−Q_W({x})]/h,
    M2(W) = sum_{x!=y} [Q_W({x−y})−Q_W({x−y,x})]/h,
    T(W) = M2(W)+(1−2mu)M1(W)+mu²M0(W).

The second anchor subtraction removes the unique shared mark when it is
zero. Neither subtraction can be discarded until its zero-label event is
excluded on the whole gate. The last formula evaluates (Z−mu)² regardless
of the partial-gate mean. Replacing it by M2+M1−mu²M0 would be unsound
unless M1=mu M0 is proved. Its signed expansion still represents a
nonnegative statistic.

## Moment intervals and the void bound

Let E exclude the remaining bad events B_j from W. For each nonnegative
statistic 1,Z,(Z)_2,(Z−mu)², multiplied by 1_{U!=0}, let U be its mass
under W and R the sum of its masses under W intersect B_j. Then

    max(0,U−R) <= E[1_E statistic] <= U.

Overlaps need not vanish. They only weaken the lower bound. Processing
additional exclusions decreases the exact uppers; the maximum of all
previous lower bounds is a nondecreasing lower envelope. After all
exclusions, moment intervals become exact, but a second-moment void
bound need not equal the true void probability.

With uppers U0,U1,U2,UT and mean lower envelope L1,

    P(E,U!=0,Z=0) <= min(U0, U0−L1²/(U2+U1), UT/mu²).

Omit the middle term if its denominator is zero. It follows from
Cauchy–Schwarz applied to the final gate; the last term follows because
(Z−mu)²=mu² at a void. Retain the minimum of these certificates over
processed prefixes. No parity truncation of signed inclusion-exclusion
is used.

## Sharp integer correction and its limited production gain

For each integer k>=1, the polynomial

    P_k(z)=(z−k)(z−k−1)/(k(k+1))

majorizes 1_{z=0} on nonnegative integers: at zero it is one, and its two
consecutive roots leave no integer in the interval where it is negative.
For exact moments this gives

    B_k=M0−2M1/(k+1)+M2/(k(k+1)).

If M1>0, write r=M2/M1 and choose k=max(1,ceil(r)). Indeed
B_k−B_{k+1}=2(M2−k M1)/(k(k+1)(k+2)), proving optimality within this family.
The bound is also sharp given these moments alone. The nonnegative masses

    p_0=B_k,
    p_k=(k M1−M2)/k,
    p_{k+1}=(M2−(k−1)M1)/(k+1)

have total M0 and precisely the supplied first and second factorial moments.
Nonnegativity of p_0 follows from the polynomial bound for any feasible
moment triple; the other two follow from k−1<=r<=k. Thus a distribution
supported on 0,k,k+1 attains the upper bound. If M1=0, the void mass is M0.

At partial gates, use the safe bound

    U0−2L1/(k+1)+U2/(k(k+1)),
    k=max(1,ceil(U2/L1)) when L1>0.

The coefficient signs justify these endpoint choices. This is a certified
upper bound, not a claim of optimality for every interval-constrained problem.
The implementation includes it in the minimum over existing certificates.

For exact moments compare B_k with the continuous Cauchy–Schwarz bound
B_CS=M0−M1²/(M1+M2). Their difference is exactly

    B_CS−B_k=M1 (k−r)(r−k+1)/(k(k+1)(r+1)).

Let nu=M1/M0>1. Nonnegative variance implies r+1>=nu, and k>=r.
Using (k−r)(r−k+1)<=1/4 yields

    0<=B_CS−B_k<=M0/(4 nu(nu−1)).

For the complete old-minimum gate and full candidate family, the Fourier
count gives nu>10^16. With M0<=1, this possible improvement is less than
2.500000000000001e-33. It cannot replace the missing production collision
bound. At incomplete gates the large exact-mean condition may fail, so this
numerical comparison is not asserted for those intermediate intervals.

## Implementation and checks

`nonzero_mark_moments` supports anchor subtractions and extra positive
intersection constraints. The certificate driver uses the preceding q=5
geometric fixture, adding a full bad event overlapping a quotient bad
event. The initial residual bound is therefore strictly loose.

All 16 prefixes agree with complete map/mark enumeration and enclose the
final moments (72/125,54/125,76/625,287/1250). With the integer correction,
the void upper bound decreases from 448/625 to the exact joint candidate
void 128/625. The preceding continuous bound was 5166/21625 at completion.
The initial incomplete gate also verifies M1!=mu M0.

Run `python3 docs/research/scripts/wall1_partial_pair_certificate.py` and
`python3 docs/research/scripts/wall1_selected_pair_collision.py`.
`python3 docs/research/scripts/wall1_integer_pair_bound.py` additionally checks
728 exact finite distributions, the attaining three-point distribution,
and the large-mean correction bound.
These are exact finite certificates, not production bounds. Efficient
control of the weighted residual sum and the selected-history collision
energy at dimension 505 remains unresolved.
