# Use the first-moment seed with linear capped transport

The draw14 seed E[P_14/delta]<=D, delta=.280, D=1.9704509e-12,
initializes Phi_k(P)=min(1,(P/delta)^k) for every k>=1. There is no
initialization penalty for choosing k=1. This observation weakens the
geometric premise of the current two-height certificate; it does not prove
that premise for actual histories.

## Exponent choice for the existing radial certificate

Let0<P<delta and let the two smaller-radius voids satisfy P<=p0<=p1<=1.
The assumption P<=p0 holds when the chosen outgoing radius floor is no
larger than the incoming radius. The capped convolution upper bound is

    U_k=min(1,(p0*p1/delta)*min(1,p0/delta)^(k-1)).

If p0<=delta, its ratio to the incoming potential is exactly

    U_k / Phi_k(P) = p1*(p0/P)^k.

This is nondecreasing in k. If p0>=delta, U_k is independent of k while
Phi_k(P) decreases, so the same conclusion holds. Thus k=1 minimizes the
certified relative drift for this radial relaxation. This is not a general
ordering of actual potential drifts or of additive positive charges. If
p0<P, the comparison need not hold. At P=0 every multiplicative premise
requires a zero upper bound and cannot be checked by dividing by P.

For k=1 a sufficient condition for multiplier C>=1 is simply

    p0*p1 <= C*P.                                       (1)

Indeed E Phi_1(P')<=min(1,p0*p1/delta)<=C*Phi_1(P)
before exit. By contrast the uncapped24th-power condition in the p0<=delta
regime requires (p0/P)^24*p1<=C. The first-moment seed makes that stronger
condition unnecessary for this route.

## A multiplicative stopped bound with the existing numerical budget

Let tau be the first draw with P_i>=delta, for14<=i<=404. Suppose on each
pre-exit full history the actual conditional expectation satisfies

    E[Phi_1(P_(i+1)) | F_i] <= C_i*Phi_1(P_i),

where the C_i>=1 are deterministic. For Z_i=Phi_1(P_min(i,tau)), this
inequality also holds after stopping, since Z_i=1 and C_i>=1. Iteration
therefore proves

    Pr(tau<=404) <= E Z_404 <= D*product_(i=14)^403 C_i.   (2)

The390-transition constant choice C_i=1.0017 gives exactly, by rational
comparison,

    D*(1.0017)^390 < 3.821716e-12 < 3.922e-12.

This replaces a requirement for tiny absolute charges by a sufficient
relative-drift condition. There is no measured or certified production
multiplier here. The two-height implication(1) still needs the smaller-radius
profiles on actual selected histories, or a stopped averaged substitute.
Fresh-mark uniformity, correct radius floors, and separately charged gate
failures remain required. No conditioning on survival is introduced.

Run scripts/wall1_linear_capped_transport.py for exact exponent comparisons
and the390-step rational budget certificate. The general stopping argument
is the paper proof above; the finite checks do not verify its history premise.

## Zero-state boundary is not a generic invariant

The [binary Hamming example](wall1_hamming_zero_void.md) is an actual
systematic q-ary initial state with K=Z^15, determinant16 and the correct
width16 radius law. It has P=0 yet expected next capped potential15/16.
Thus the multiplicative premise cannot follow solely from unit generation,
q-ary structure, determinant normalization and shortest selection. This
does not refute the required production q3329,width506 estimate, but that
estimate must use further ensemble-specific information or exceptional
charges. The sufficient conditional calculation(2) remains valid.
