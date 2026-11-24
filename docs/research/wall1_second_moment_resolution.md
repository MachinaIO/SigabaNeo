# Resolution of the scalar-collision second-moment certificate

The selected-incidence evaluator computes the correct moments, but precision
of the evaluator does not imply that the resulting second-moment inequality
is sharp enough. This diagnostic isolates that issue in an independent-label
comparison model. It is not the selected BKZ distribution and establishes no
lower bound on production failure or impossibility of the target theorem.

## Exact benchmark calculation

Let the quotient have h=q^d elements and K=h-1 nonzero labels. Draw L labels
independently and uniformly among those K labels, retaining multiplicities.
The candidate count N is L. Let J count equal ordered labels and C count
ordered pairs on the same nonzero scalar line. Then

    E J = L + L(L-1)/K,
    E C = L + (q-1)L(L-1)/K.

The diagonal contributes L, including only scalar 1 in C. An off-diagonal
pair agrees with probability 1/K and lies on the same scalar line with
probability (q-1)/K. Put D=r(q-1)J+(1-r)C and A=1+r(q-2). The aggregate
ratio-of-moments coverage certificate from Part 465 is exactly

    B = (q-1)L^2 / (K E D)
      = L / (L-1+KA/(q-1)).

This is a lower coverage certificate, not the mean of the pointwise ratio.
Granting r=0 minimizes the resulting miss upper bound. Sign averaging does
not change this case, since total candidate multiplicity on each scalar
line, hence C, is unchanged. With L=K*mu its miss upper bound, including
the always-covered zero mark, is

    U = K/(K+1) * a/(mu+a),     a=1/(q-1)-1/K.              (1)

For large K this tends to 1/(1+(q-1)mu). In contrast the actual full-scalar-
orbit witness miss probability in this independent model is

    K/(K+1) * (1-(q-1)/K)^L.

Thus loss of precision can come from the second-moment inequality itself,
even when all moments are known exactly. Granting the full scalar orbit
also relaxes geometric requirements: production height witnesses still need
their radius and height margins. This model cannot establish those margins.

## Exact numerical diagnostic and implications

The checker `scripts/wall1_second_moment_resolution.py` verifies the formulas
by exhaustive small-field enumeration (36 moment/miss checks). For q=3329,
K=q^388-1 and benchmark mu=58,119, it verifies exactly that (1) lies between
2e-6 and 6e-6; its limiting values are respectively 1/193025 and 1/396033.
The finite-K error from the displayed limit is positive and less than 2/K.
The chosen means are comparison values, not computed later-history means.

Solving (1)<=epsilon gives the exact necessary condition for this particular
certificate to meet that tolerance:

    mu >= (1/(q-1)-1/K) * (K/((K+1)*epsilon)-1).

At epsilon=1.951e-12 the checker proves that this threshold exceeds
150,000,000. The quoted epsilon is a comparison with the rounded remaining
history allowance, not a claim that every transition must independently meet
that absolute tolerance. Independent mathematical review verified the
formulas, zero-mark factor, finite-K qualification and sign-averaging scope.

Consequently exact evaluation or improved residual bounds in Parts 467–469
alone need not produce a sufficiently sharp main-history certificate. This
route can still bound low-mass exceptional strata, or participate in signed
gain/loss transport. A main route must exploit additional information, such
as higher occupancy moments or cancellation in the actual capped drift.
The previously proved draw-14 high-order bound supplies the initial seed;
it cannot be reapplied to a selected later quotient without proving the
appropriate joint law. No production obstruction has been proved here.

## Accuracy cost of partial exclusion

There is a second, separate precision issue in Part 469. For a processed
avoidance event let its exact moments be (a_P,n_P,d_P), with n_P,d_P>0,
and let R_N bound the candidate count lost to unprocessed competitors.
Put eta=min(1,R_N/n_P), so the lower candidate moment is n_P*(1-eta).
Holding the processed upper bounds a_P,d_P fixed, the increase of the
mixed-moment tail certificate is exactly

    ((h-1)/h) * ((q-1)*n_P^2/((h-1)*d_P)) * (2*eta-eta^2).

The processed-event coverage certificate is at most a_P, hence this
increase is at most 2*a_P*eta. Summing over proposed flags therefore
requires control of the weighted residual sum sum_F a_P(F)*eta(F), in
addition to the processed baseline certificate and any other enclosure
errors. Processed events may overlap even when the full selected flags
are disjoint: replacing their total mass by one is invalid in general.
If n_P=0, selected candidate mass is also zero; use the zero-coverage
convention instead of the relative-error expression.

This exact sensitivity calculation identifies the relevant aggregate
residual quantity. It does not bound it geometrically. A positive n_L in
an exhaustive finite example alone does not provide the required precision.

## A valid raw-incidence residual bound at the production modulus

One coarse bound does not require a uniform quotient law after selection.
For a uniform original map A into F_q^m, fix a graphic flag span F of input
rank t. If an unprocessed forbidden vector belongs to F, its membership
is forced and the full selected event is empty; discard that flag. If
span(F,b) is nongraphic, its joint incidence is zero. Every other single
competitor extends the input rank by one, so

    Pr(F subset graph(A), b in graph(A)) = q^(-m*(t+1)).

Dropping saturation, fixed-image and processed avoidance constraints only
increases this mass. If C_F counts the remaining distinct membership events,
then a valid unconditional remainder is

    eta_F <= C_F * 3329^(-400*(t+1)),
    R_N(F) <= L_F * C_F * 3329^(-400*(t+1)),

where L_F is the fixed candidate-list multiplicity. Here eta_F is an event
union bound, not the relative candidate error eta of the preceding section.
The number of raw lifts can replace C_F as an upper bound, even with duplicates.
For a certified integer-lift radius R_j in actual raw prefix dimension D_j,
the elementary theta count gives

    # {z in Z^{D_j}: ||z||^2 <= R_j^2}
      <= inf_{beta>0} exp(beta*R_j^2) * theta(beta)^{D_j},
    theta(beta) = sum_{k in Z} exp(-beta*k^2).

Summing this over the chronological competitor lists bounds C_F. The radius,
prefix dimension and completeness of those lists must be certified for the
specific flag; no dimension indexing convention is inferred here. This
expresses the residual using original-matrix incidences and integer geometry,
but summing it over all proposed flags remains uncontrolled. In particular,
the small factor q^(-400*(t+1)) alone is not a history bound: the number of
flags and their competitor lists must also be paid for.
