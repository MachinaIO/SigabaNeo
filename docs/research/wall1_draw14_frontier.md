# Concrete draw-14 frontier for the fixed raw-ball route

This calculation returns to the actual q=3329 parameters. It does not close
draw 14. It bounds the reference contribution and a specified class of dependency
corrections, leaving an explicit remainder. Later projected histories also remain
open, and Part 262's independent-reference obstruction still applies at draw 15.

## Parameters and polynomial degree

Use the fixed raw radius from Part 250 with draw i=14, m=400, N=518 and 118
input coordinates:

\[
 R^2=1.21(q^{386}/V_{506})^{2/506}-2.
\]

The proven integer candidate lower bound gives a mean floor
58.15006220912<mu_*<58.15006220913. Let mu be the true mean of this fixed candidate
set, so mu>=mu_*. With the Charlier square K_t(Z;mu)^2/D_t(mu)^2 and rho=0.280,
the reference upper bound obtained from this floor is

\[
 \frac1{\rho D_{11}(\mu_*)}>4.5177\,10^{-12},\qquad
 \frac1{\rho D_{12}(\mu_*)}<9.131\,10^{-13}.
\]

Thus the floor-based bound at kernel degree 11 exceeds the remaining 3.922e-12
history budget, whereas kernel degree 12 (square degree 24) leaves room for
dependencies. This is not a lower bound on the actual failure probability, or a
claim that every possible degree-22 method fails. An improved count or a different
certificate could change that comparison.

## Corrections covered by existing proofs

Apply Parts 253--256 with the new dimension, radius and orders through 24. The
same one-circuit Gaussian counts give epsilon_h for h=3,...,24. The direct-sum
generating function includes all combinations of the admitted components and
the independent free components; it is not limited to a single activated circuit.
Transfer these central-moment corrections to K_12 using the absolute monomial
coefficients of its exact central expansion, as in Part 257.

Outward interval arithmetic at 80 digits proves:

- The independent Bernoulli correction, after division by rho, is <1.120e-289.
- The correction from direct sums of circuits alone is <4.682e-48.
- Including all rank-two connected components through size 24, and all remaining
  connected components of size at most eight, gives a correction <1.160e-15.

The substitution mu>=mu_* is justified termwise after normalization. Central
coefficient monomials at central degree j have mu-degree at most 24-j. The
circuit/rank-two activities have mu-degree zero; the rank-extension activity of
a connected h-point block has degree at most h-4. Free blocks have size at least
two and contribute one power of mu. Thus every normalized dependency term has
a negative power of mu after using D_12(mu)^2>=mu^24/(12!)^2. The Bernoulli-error
majorant likewise has total mu-degree at most 23 before that denominator.
All coefficients in these majorants are nonnegative. This is why the lower
mean floor is valid here despite the alternating signs in the original polynomial.

## Explicit remaining inequality

Let R_large denote the signed correction to E[K_12(Z;mu)^2] contributed by
supports having a connected component of size at least nine, rank at least three,
and nullity at least two. Components of size up to 24 can occur. The reference
comparison and the covered corrections give the conditional-on-this-remainder bound

\[
 \Pr(b_{14}>0.280)
       <9.143\,10^{-13}+\frac{|R_{\rm large}|}{0.280D_{12}(\mu)^2}.       \tag{1}
\]

In particular the constant 9.143e-13 is not by itself a draw-14 failure bound.
Together with Part 261's earlier accounting, a sufficient remaining obligation is

\[
 \frac{|R_{\rm large}|}{0.280D_{12}(\mu)^2}
       +\Pr\left(\max_{15\le i\le404}b_i>0.280\right)
                                                    \le3.0077\,10^{-12}. \tag{2}
\]

The old unrestricted rank-extension majorant, when enlarged just to include
size-nine components, already exceeds 0.00185 after transfer. This is the value
of an overestimate, not a lower bound on the true correction. It demonstrates
that this particular envelope cannot bound the remainder in (1); a sharper
joint-constraint count or signed cancellation is needed. Draw 13's top-degree
nine-support cancellation cannot simply be reused in a degree-24 polynomial,
where the same support can occur with many more multiplicities.

Run `python3 docs/research/scripts/wall1_draw14_frontier.py`. It recomputes the
actual draw-14 parameters and circuit counts, checks the stated interval bounds,
and prints the deterioration as the admitted higher-rank support size increases.
The underlying component proofs are the paper deductions of Parts 253--257;
this calculation is not an independent audit or Lean proof of those deductions.


## Proper-subset suppression does not resolve the largest components

The rank-deficit argument of Part 260 applies to every proper subset of a
connected support, including sizes 9 through 24 here. Evaluate its equation (1)
for every rank 3 through h-2, retaining rho_max^w with w>=1, and call the resulting
activity E_h. Applying the same positive degree-24 transfer to these activities
alone gives the following interval-verified diagnostic:

- With E_h for 9<=h<=21, the proper-only envelope is <1.548e-31.
- The envelope using E_22 alone exceeds 360.
- The envelope using E_24 alone exceeds 1e74.

These large values are values of upper envelopes, not lower bounds on any true
moment correction or failure probability. Even the retained density factor does
not offset the single-circuit completion count at the largest support sizes.
Consequently this argument cannot localize the entire remaining error solely to
full-incidence terms with a negligible proper-subset charge.

The transfer here includes combinations of proper-subset activities only.
It does not bound mixed products with full-incidence activities: those must be
included in the same component generating function before making a total-error
claim. In particular, the small value through size 21 cannot be added to (1)
as a bound for all terms involving a proper subset.

Run `python3 docs/research/scripts/wall1_draw14_proper_subset.py` to reproduce
these diagnostics. The negative powers of mu after normalization justify using
the same mean floor, as in the preceding calculation. The remaining obligation
(2) is unchanged.

Follow-up: [Part 277](wall1_full_incidence_reduction.md) gives a different,
conditional reduction using smaller full-incidence counts. It includes mixed
error terms and avoids this one-circuit proper-subset envelope; the needed
full-incidence transfer target remains unproved.
