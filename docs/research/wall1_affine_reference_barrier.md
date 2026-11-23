# Fixed-ball independent-reference obstruction at draw 15

This is a limitation of the comparison method, not a lower bound on BKZ failure.
Part 261 closes draw 13. Before increasing polynomial degrees for later draws,
the following bound shows why the same raw candidate set and independent reference
cannot suffice through draw 15, even with a perfect polynomial optimization.

Use the fixed raw radius of Part 250, with q=3329, m=400, N=504+i:

\[
 R_i^2=1.21(q^{400-i}/V_{506})^{2/506}-2.
\]

Let S be the centered integer candidates in that ball. Group them by their input
residue y and let a_y be the number of output residues in that fiber. Set
rho_y=a_y/q^400 and let Z_0 be a sum of independent Bernoulli variables with these
probabilities. This is the reference distribution, not the affine graph law.

Write mu=sum_y rho_y and assume rho_y<=eta<1. Independence and

\[
 \log(1-p)=-\int_0^p\frac{dt}{1-t}\ge-\frac{p}{1-\eta}
 \quad(0\le p\le\eta)
\]

give the rigorous lower bound

\[
 \Pr(Z_0=0)=\prod_y(1-\rho_y)\ge \exp[-\mu/(1-\eta)].       \tag{1}
\]

For any dimension k, the number of integer points in a radius-R ball is at most
2 V_k (R^2+k/4)^(k/2). Indeed, the portion of z+[-1/2,1/2]^k where z dot u<=0
has volume at least 1/2 and lies in the radius-sqrt(R^2+k/4) ball; distinct cubes
have disjoint interiors. The zero center causes no problem. Apply this once to S
and once to an output fiber, enlarging the latter to the radius-R ball in 400 dimensions:

\[
 \mu\le M_i=\frac{2V_N(R_i^2+N/4)^{N/2}}{q^{400}},\qquad
 \rho_y\le\eta_i=\frac{2V_{400}(R_i^2+100)^{200}}{q^{400}}.
\]

At draw 15, outward interval arithmetic at 80 decimal digits proves

\[
 M_{15}<9.287185,\qquad \eta_{15}<1.192\,10^{-300},\qquad
 \exp[-M_{15}/(1-\eta_{15})]>0.000092603.             \tag{2}
\]

For every function g on the nonnegative integers satisfying g(0)>=1 and g(k)>=0
for k>0, (1) implies E g(Z_0)>=Pr(Z_0=0). This includes every squared-polynomial
certificate, of any degree. Thus a comparison of the form

\[
 \Pr(Z=0)\le E g(Z)\le E g(Z_0)+\epsilon,\qquad\epsilon\ge0,
\]

cannot yield an upper bound below 0.000092603 with this reference at draw 15.
The corresponding Markov transfer divided by 0.280 cannot yield a bound below
0.000330725, far above the remaining 3.922e-12 history allowance.

This does not exclude a signed correction reducing the reference expectation,
a direct estimate of the exceptional-matrix event, a larger provable radius,
or projection-aware candidates. It does not show that the affine graph has
independent fibers, or that its void probability has the lower bound (2).
At draw 16 there is the separate deterministic raw-coverage obstruction of Part 250;
the verifier also rechecks that bound. Neither obstruction transfers backwards
through the one-sided domination from the projected observable to the raw void.

## Consequence for the remaining proof

Raising the degree of the Part 257--258 certificate alone is insufficient for
draws 14--404. A projection-aware count must retain both the selected geometry and
the resulting collisions. The exact occupancy identity in
[projected occupancy](wall1_projected_occupancy.md) gives a suitable target:
on each covered branch, prove 720 h J <= 1000 N_points^2 with high probability
under the actual selected-history law. Its failure probability, together with
branches outside that identity's hypotheses, must fit the remaining history budget.
The point count N_points here is not the raw dimension N above.
No distributional estimate for that statistic is proved by this note.

Run `python3 docs/research/scripts/wall1_affine_reference_barrier.py`.
It checks the interval inequalities and 81 exact finite product-law examples.
The general inequalities above are paper proofs, not Lean formalizations.
