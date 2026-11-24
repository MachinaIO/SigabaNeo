# Averaged rounding supplies candidate density at every freeze

The worst-case covering displacement in Part 474 is unnecessarily costly
for counting points. Integrating unbiased rounding yields a quadratic radius
correction. At the production parameters it proves candidate density greater
than 751871 at every freeze from 0 through 406. This supplies a concrete
sixth-central-moment route; it does not prove the required moment bound or
its connection to the capped-history failure event.

This is an elementary alternative, not the strongest available density bound.
Parts 215/217 already give a stronger Fourier-minorant count; its
[extension to this radius and all 407 floors](wall1_fourier_density_extension.md)
gives density above 10^16 and reduces the proposed concentration route to a
second-moment obligation. That obligation remains unproved.

## A deterministic lower count from a rounding kernel

Let K=P Z^N have intrinsic rank r, where P is a rational orthogonal projection.
Choose r independent projected coordinate units b_i. Their norms are at most
one and they generate a finite-index sublattice K_0 of K. Write B for this
basis matrix in orthonormal coordinates of the projection range.

For each coset a+K_0 and each x in that range, independently round the
coordinates of B^(-1)(x-a) to adjacent integers with unbiased probabilities.
The rounded point Y lies in a+K_0 and satisfies

    E Y=x,
    E||Y||^2=||x||^2+sum_i Var(round_i)*||b_i||^2
             <=||x||^2+r/4.

Obliqueness introduces no cross terms, since rounding errors are independent
and centered. For a fixed lattice point, its probability as a function of x
is a product of one-dimensional tent functions in basis coordinates. Each
tent has integral one. Thus the integral of this probability over the entire
projection range is det(K_0).

Assume R^2>r/4 and put A^2=R^2-r/4. Markov's inequality gives

    Pr(||Y||<=R) >= (A^2-||x||^2)/R^2     for ||x||<=A.

Integrate over B(A), then bound the integral above by its all-space value.
The radial integral is 2 V_r A^(r+2)/((r+2)R^2). Hence

    det(K_0)*#((a+K_0) intersect B(R))
      >= 2 V_r (R^2-r/4)^((r+2)/2)/((r+2)R^2).

Sum over the [K:K_0]=det(K_0)/det(K) cosets. The index cancels exactly:

    #(K intersect B(R))
      >= 2 V_r (R^2-r/4)^((r+2)/2)
           /((r+2)R^2 det(K)).                           (1)

When R^2<=r/4 use zero. Boundaries cause no issue; the argument counts a
closed ball and integrates nonnegative functions. This is a deterministic
count, not a statement about the distribution of quotient labels. Related
integer-grid tent-kernel rounding appears in
[the earlier long-winner argument](wall1_long_winner_handle.md); here the
finite-index projected cosets and quadratic-slack integration are explicit.
Independent review verified the integration and index normalization.

## Uniform density at the actual determinant floors

Use r=505, q=3329, D=h*det(K), h>1, and the same choices as Part 474:

    g=(D/V_506)^(1/506),    c=1.1g,    R^2=1.21g^2-2.

If L counts all nonzero projected points through R, (1) gives

    L/(h-1) >= F_av(g),
    F_av(g)= (2/507)*(V_505/V_506)
             *(1.21g^2-128.25)^(507/2)
             /((1.21g^2-2)*g^506) -1/3328.              (2)

The factor h/(h-1)>=1 and the origin subtraction justify the final constant.
As before, g lies between the unconditional Hermite/period floor g_f and
g_max=(q^400/V_506)^(1/506). All these intervals have 1.21g^2>128.25.

Unlike Part 474's lower expression, (2) is not monotone over the whole
range. With x=1.21g^2, the logarithmic derivative of its positive term has
numerator

    -x^2+65149x-129789

and positive denominator (x-128.25)(x-2). The quadratic is negative at zero,
positive at 128.25 and negative eventually. It has exactly one root above
128.25. Thus the function increases and then decreases on this domain;
its minimum on every allowed interval is attained at an endpoint.

Outward interval evaluation at both endpoints for all 407 freeze counts
proves a global lower bound exceeding 751871.0429. The smallest endpoint
is g_406; the value at g_max exceeds 8.473e15. The determinant recurrence,
section identity and range of g are the same previously certified inputs
used in [Part 474](wall1_intrinsic_cover_density.md). There is no newly
assumed determinant profile or exceptional event. In particular,

    L > 750000*(h-1)                 for every f=0,...,406. (3)

This improves the candidate-density horizon to the entire stated range.
It does not improve a certified failure-probability horizon by itself.

## A concrete sufficient sixth-moment target

Fix mu=750000. On each old-history event

    G_f={h>1 and lambda_1(M)>=c},

choose exactly L_star=mu*(h-1) distinct nonzero geometric candidates of norm
at most R, using a specified deterministic geometric rule depending only on K,D,h
(for example, a fixed coordinate ordering of the finite candidate set).
It is then fixed on each geometric and quotient-rank stratum used by the
incidence evaluator. Its existence follows from (3). Their labels are all nonzero
on G_f by the old-minimum gate. For the single fresh mark U define

    Z_f=sum_{candidate z} 1_{[z]=U}.

Then E[Z_f | old history, U!=0]=mu exactly. The choice does not use U;
no independence or uniformity of the candidate labels follows. A proof of
the next inequality must concern the chosen rule, not an unspecified subset.
For a quotient of order one the next long-winner event is empty directly.

The event S_(f+1)>=c forces G_f and U!=0. A hit produces a vector with
squared norm at most R^2+1=c^2-1, so this event also forces Z_f=0. Therefore

    Pr(S_(f+1)>=c) <= T_f/mu^6,
    T_f=E[1_{G_f}1_{U!=0}(Z_f-mu)^6].                   (4)

This is an expectation under the actual reached-history and fresh-column
law. It does not divide by the probability of G_f or replace that law by
an unselected matrix law. The moment can be expanded using the old selected
collision incidences of Parts 471–472, now only through order six.

For any 390 consecutive transitions in the certified range, a sufficient
condition is the STILL UNPROVED bound T_f<=2000*mu^3 at every transition.
It would give

    Pr(any such long winner) <= 390*2000/mu^3
      =1.848888...e-12 <1.9515491e-12.                  (5)

An aggregate bound on sum_f T_f suffices as well. This comparison fits the
numerical size of the remaining allowance, but a long-winner event is not
automatically the capped empty-coset exit event used elsewhere. Establishing
the required implication or a replacement complete proof route remains
separate from proving the sixth-moment bound. Equation (5) is conditional,
not a new production probability certificate.

For scale only, independent Bernoulli variables with total mean mu obey

    E(Z-mu)^6 <= mu+25mu^2+15mu^3 <15.0001mu^3.

Expand the sixth power of centered independent summands: only block patterns
6, 4+2, 3+3 and 2+2+2 survive. Each summand's absolute central moment of
order at least two is at most its success probability; bounding the distinct-
index sums gives the displayed coefficients. This reference comparison
explains the constant 2000; it is not an independence assertion for Z_f.
Part 473 shows why old-minimum information alone does not control all
higher moments of arbitrary candidate lists.

## Verification and remaining obligations

`scripts/wall1_averaged_rounding_density.py` verifies 64 exact rational
rounding cases and 192 Markov checks for oblique bases and translated cosets,
including tent-kernel normalization. It certifies the derivative algebra,
all 407 endpoint intervals, the uniform bound above mu, and the exact
390-step conditional budget comparison. The parent reran the checker.
Independent review verified the count proof, endpoint argument, subset
normalization, sixth-moment implication and their stated scope.

The missing production result is now explicit: control the actual selected
sixth central moment for a valid candidate-selection rule, and connect the
resulting next-winner tail to the full required history failure. No such
moment bound, full BKZ proof, or new Lean formalization is claimed here.
