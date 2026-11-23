# A sharper compensator bound from the actual finite-group correlation

This is a paper proof and an interval-checked improvement of the sufficient condition
in Part 246. It does not establish the required exceptional-history probability.
The bound uses the two-mark correlation from [Part 230](wall1_inductive_typicality.md),
not merely its range and first moment. It also omits the first seven long-winner
probabilities, which vanish deterministically.

For the original width-506 process, let p_i be the conditional probability of
s_i > 1.10 g_i given the incoming history, as in [Part 243](wall1_fresh_review.md).
Let b_i retain its Part 246 meaning: the fraction of old cosets missed at radius
sqrt((1.10 g_i)^2 S_i^(-2/506) - 2), NOT the long-winner probability p_i.
Define E_rho = {there exists i in 7,...,404 with b_i > rho}. We prove

\[
 \Pr\left(\sum_{i=1}^{405}p_i>48.6\right)
 \le \Pr(E_\rho)+e^{-48.6\lambda}B_q(\rho,\lambda)^{398},       \tag{1}
\]

where q = 3329, 0 < rho <= 1/2, lambda > 0, and

\[
 m_q(\rho)=\frac{\sin(\pi\rho)}{q\sin(\pi/q)},\quad
 d_q(\rho)=\rho^4+m_q(\rho)^2\rho(1-\rho),
\]
\[
 B_q(\rho,\lambda)=1+\lambda\rho^2+
 \frac{e^{\lambda\rho}-1-\lambda\rho}{\rho^2}d_q(\rho).       \tag{2}
\]

Useful interval-verified instances are:

* rho = 0.280 and lambda = 3.004: the exponential term is < 1.174e-12.
  Thus Pr(E_0.280) <= 6.426e-12 suffices for the Part 243 target of 7.6e-12.
* rho = 0.281 and lambda = 2.950: the exponential term is < 2.736e-12.
  Thus Pr(E_0.281) <= 4.864e-12 also suffices.

These are alternative sufficient targets, not measured probabilities. Their exit
windows start at 7, so the draw-2 family in Part 247 is not by itself an obstruction
to either one. Later exits, including those in continuations of that family, are
not excluded. Neither target has been proved.

## 1. A coefficient bound using the exponent of the mark group

Let H be a finite abelian group with qH = 0 for prime q. For A contained in H,
put p = |A|/|H| and a = 1_A. Every nontrivial character chi has order q,
so its q fibers have equal size. If f_j in [0,1] is the fraction of A in fiber j,
then p = (1/q) sum f_j and the normalized Fourier coefficient is
(1/q) sum f_j exp(2 pi i j/q), up to conjugation.

Give the circle normalized measure dtheta/(2 pi). Define f to equal f_j on the
arc of length 2 pi/q centered at 2 pi j/q. Direct integration yields

\[
 \int f(\theta)e^{i\theta}\frac{d\theta}{2\pi}
 =\frac{q\sin(\pi/q)}{\pi}\widehat a(\chi).
\]

For any measurable 0 <= f <= 1 of mean p on the circle, the modulus of this
integral is at most sin(pi p)/pi. Indeed rotate its phase to make it real, and
compare f with the indicator of the centered arc |theta| <= pi p. On this arc,
(f-1)(cos theta-cos(pi p)) <= 0; outside it,
f(cos theta-cos(pi p)) <= 0. Integrating and using equality of the means
proves the claim. Hence

\[
                   |\widehat a(\chi)|\le m_q(p).             \tag{3}
\]

No shape assumption on A or independence between its characters is used.
If H is trivial there are no nontrivial coefficients and the variance below is zero.

## 2. The correlation second moment

Let C(u) = E_v a(v)a(v+u). Then 0 <= C <= p and E C = p^2. Finite Fourier
orthogonality and Parseval give

\[
 \mathbb E C^2=p^4+\sum_{\chi\ne1}|\widehat a(\chi)|^4
 \le p^4+m_q(p)^2p(1-p)=d_q(p).                 \tag{4}
\]

The standard bound E C^2 <= p^3 can be used as well, but is not needed in (2).
For p <= rho <= 1/2, d_q(p) <= d_q(rho): each factor in the two nonnegative
terms is nondecreasing on that interval.

If 0 <= X <= C pointwise, then for lambda > 0,

\[
 e^{\lambda X}\le1+\lambda X+
 \frac{e^{\lambda\rho}-1-\lambda\rho}{\rho^2}X^2.
\]

This follows term by term from the exponential series, since
X^k <= rho^(k-2) X^2 for k >= 2. Taking expectations proves
E exp(lambda X) <= B_q(rho,lambda). This retains a second-moment constraint
that is absent from the chord bound 1 + rho(exp(lambda rho)-1).

## 3. Filtration, stopping, and the first seven draws

Condition on the incoming history at draw i. The set A is the set of old cosets
missed at the smaller radius defining b_i, so its density is p = b_i.
Part 230 equation (2) with offsets 0 and 1 proves the pathwise bound

\[
                      p_{i+1}(u)\le C(u).
\]

The next height-one miss majorizes the true next long-winner probability.
The inclusion holds for the actual chosen shortest vector, including ties.
Conditional on the incoming history, the fresh u is uniform in H. There is no
conditioning on the selected output before applying (4).

Each winner length is at most q, because projected q-periods span the window.
Therefore g_i >= (q^400/V_506)^(1/506) q^(-(i-1)/506). The exact integer
comparison

\[
 11^{506}q^{394}253!113^{253}
   >10^{506}q^{506}355^{253}
\]

and pi < 355/113 imply 1.10 g_7 > q. Hence p_1 through p_7 vanish for every
history, and sum_{i=1}^{405} p_i = sum_{i=7}^{404} p_{i+1} has 398 terms.

Set X_i = p_{i+1} times the indicator that b_j <= rho for every 7 <= j <= i.
This indicator is measurable before the fresh mark at draw i. On a stopped
history X_i = 0; otherwise the preceding conditional exponential bound applies.
Iterating conditional expectations gives
E exp(lambda sum X_i) <= B_q(rho,lambda)^398. On E_rho complement,
sum X_i = sum p_i, so Markov's inequality and a single charge for E_rho prove (1).
One must not condition the whole experiment on the absence of exits; the stopped
variables are what preserve the original fresh-mark law.

## What remains

The Part 243 Bernoulli-compensator argument then gives a small-scale crossing
bound below 1.9642e-11 + 7.6e-12 = 2.7242e-11, IF either stated exit target
holds. This addresses the vertical crossing route only. It does not prove the
other score, horizontal, or prefix-rejection obligations in Part 243 equation (1),
and does not complete the BKZ-506 theorem.

The new condition is less restrictive than Part 246's sufficient exit condition,
but it remains an estimate on the distribution of selected histories. No simulation
or fixed-history coset probe has established it. The finite occupancy lemmas in
`CosetOccupancy.lean` can certify individual histories; this Fourier argument and
its application to the concrete restart are not formalized in Lean.

Run `python3 docs/research/scripts/wall1_correlation_mgf.py`. It checks the period
comparison exactly, checks all reported numerical bounds with 80-digit interval
arithmetic, and exhaustively checks the second-moment inequality for every subset
of F_3^2 and F_7. The finite examples are regression checks, not a proof in general.


## Subsequent initial-history certificate

[Part 250](wall1_affine_void_moments.md) proves on paper, with exact finite and interval
checks, that Pr(max_{7<=i<=12} b_i > 0.280) < 7.150e-14 under the original marginal.
Consequently the first sufficient target above reduces to
Pr(max_{13<=i<=404} b_i > 0.280) <= 6.354e-12. That latter probability remains open;
the moment argument here still uses all 398 stopped variables and charges the
initial exception once.
