# Linear residual transfer and the remaining size-fourteen strata

The positive transfer is truncated at order 24. Consequently two unknown
components of sizes at least 14 never occur in the same retained term.
This removes the need for a separate nonlinear mixed-term estimate for these
unknown components. Their activities themselves, and later selected histories,
still need bounds. Nothing here completes the draw-14 or BKZ proof.

## Exact identity

Let B be the admitted activity envelope from Part 283, with B_2=0. Let U_h
be the actual unadmitted activity, supported on 14<=h<=24. Thus the full
activity is bounded componentwise by B+U. Put

```
E_B(z) = exp(sum_(h=2)^24 B_h z^h/h!),
K(mu) = (12!)^2/(0.280 mu^24),
L_h(mu) = K(mu)/h! * sum_(j=h)^24 w_j^+(mu) [z^(j-h)] E_B(z).
```

Modulo z^25, exp(sum U_h z^h/h!)-1 equals sum U_h z^h/h! exactly: the
square already has degree at least 28. Hence

```
C(B+U)-C(B) = sum_(h=14)^24 L_h(mu) U_h.
```

All known/unknown mixtures occur in L_h. Only B_2,...,B_10 can affect these
coefficients. In particular admitting additional size-fourteen strata does
not change any L_h. This is an identity for the positive majorant transfer,
not an assertion of probabilistic independence.

## Mean-floor evaluation

Choose the same positive polynomial envelopes as in the existing verifier.
Each B_s has mu-degree at most s; the stronger bounds used previously also
suffice. The coefficient [z^k]E_B has degree at most k, and w_j^+ has degree
at most 12-ceil(j/2). A monomial in L_h therefore has degree at most

```
12-ceil(j/2)+(j-h)-24 = floor(j/2)-h-12 <= -h.
```

Its coefficient is nonnegative. Thus evaluating L_h at the proven mean lower
bound gives an upper bound valid throughout the allowed mean interval, while
U_h may be kept as the actual unknown activity. Selecting one of two valid
envelope polynomials at the mean floor does not invalidate that polynomial
elsewhere.

Write L_h^* for this evaluated coefficient and
D_h^*=K(mu_floor) w_h^+(mu_floor)/h!. Interval arithmetic proves, for all
14<=h<=24,

```
0 <= L_h^*-D_h^* < 2e-42 D_h^*.
```

The difference is exactly zero for h>=22 since B_1=B_2=0. The largest relative
correction occurs at h=14, with log10 approximately -41.8247156640.
This numerical ratio concerns the evaluated upper coefficients; no claim
about the ratio at arbitrary mu is needed for the upper bound.

Therefore a sufficient open condition can be written explicitly as

```
sum_(h=14)^24 L_h^* U_h + Pr(max_(15..404) b_i > .280) <= 2.7913e-12.
```

The left side remains unbounded. Small relative mixed coefficients alone do
not imply that the unknown contribution is small.

## Additional admitted size-fourteen strata

The existing two-relation envelopes separate rank r and shortest-circuit
size c. At h=14, the sum over r>=3 outside

```
c=4 and r in {5,6,7,8,9}
```

has weighted transfer less than 6e-18, including all mixtures with the admitted
baseline. Add these strata to B_14, keeping the already admitted circuit and
rank-two bounds. The resulting known transfer still satisfies C(B)<2.175e-13;
the previous rounded budget has enough slack. The coefficients L_h^* are
unchanged. U_14 can now be restricted to exactly those five rank/girth strata.
Sizes 15--24 retain their previous unadmitted rank>=3, nullity>=2 classes.

Among the current h=14 envelopes, the largest is r=7,c=4, with weighted
log10 about 5.95329, followed by r=6,c=4 at 4.01265 and r=8,c=4 at 0.67321.
These are loose upper envelopes, not lower bounds on actual activities.
They identify where better overlap-sensitive counting is needed; they do not
refute the desired probability estimate.

## Verification

`python3 docs/research/scripts/wall1_linear_remainder.py` checks 48 exact
rational identities at several truncation orders, rejects a cutoff allowing
two unknown components, and verifies that high baseline terms cannot affect
the residual coefficients. It then checks the relative coefficient bounds,
the additional size-fourteen charge and the unchanged known-transfer budget
with interval arithmetic. The numerical checks are not Lean formalized.

## Lean certificate (Part 289)

`SigabaNeo/Lib/Lattices/Research/Wall1/LinearRemainder.lean` proves that if a
formal series U has no coefficients below k, then every power U^(r+2) has
no coefficients below 2k. Multiplication by any known formal series preserves
this cutoff. The result applies to arbitrary finite scalar-weighted tails,
and `weighted_exponential_remainder_24` specializes it to the factorial
coefficients of the finite nonconstant exponential sum over the reals.

Concretely, through order 24 the weighted coefficients of
E * sum_(r=1)^(terms+1) U^r/r! equal those of E*U whenever U vanishes below
14. The theorem's right side is the explicit antidiagonal convolution, so
the unknown coefficients appear only linearly. `coeff_mul_prefix_24` also
proves that only coefficients 0,...,10 of E matter. Both are unconditional
algebraic statements subject to the displayed support premise.

The file compiles with `lake env lean`. All eleven theorem axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`
proofs or new axioms. This is a file-level check, not a whole-project build.

Scope: the formal result starts from the **factored finite correction** above.
It does not yet formalize the exponential factorization of B+U, the
factorial-cumulant/probability identity, the reindexing into the L_h formula,
the mean-floor monotonicity argument, or the numerical bounds. Those remain
paper arguments/regressions and must not be inferred from this certificate.
