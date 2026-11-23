# A degree-ten square certificate for the affine void

The raw twelfth central power is not required for the draw-13 moment route.
This paper result constructs a nonnegative polynomial of degree ten whose
independent reference contribution, after division by rho=0.280, is below
2.274e-12. The independent Bernoulli correction is below 2.575e-293. Previously
bounded dependent components through size eight contribute below 4.859e-22.
Connected components of sizes nine and ten remain uncontrolled at the required
scale. No complete bound for Pr(b_13>0.280) is claimed.

## Pointwise certificate and the Poisson reference

For mu>0, write (x)_l=x(x-1)...(x-l+1), with (x)_0=1, and define

\[
 C_j(x;\mu)=\sum_{l=0}^j {j\choose l}(-\mu)^{j-l}(x)_l,
 \qquad D_t(\mu)=\sum_{j=0}^t\mu^j/j!,
\]
\[
 K_t(x;\mu)=\sum_{j=0}^t(-1)^j C_j(x;\mu)/j!
     =\sum_{l=0}^t\frac{(-1)^lD_{t-l}(\mu)}{l!}(x)_l.
\]

Since K_t(0;mu)=D_t(mu), for every nonnegative integer Z,

\[
       1_{\{Z=0\}}\le K_t(Z;\mu)^2/D_t(\mu)^2.           \tag{1}
\]

For X~Poisson(mu), the exponential generating function of C_j is
(1+s)^X exp(-mu*s). Taking the expectation of the product at s and t gives
exp(mu*s*t), by the Poisson generating function. Equating coefficients proves
E[C_i(X)C_j(X)]=1_{i=j} j! mu^j. Consequently

\[
                    \mathbb E K_t(X;\mu)^2=D_t(\mu).      \tag{2}
\]

This is optimal among degree-t square certificates for this reference law:
expand any degree-t polynomial g in the orthogonal C_j basis and apply
Cauchy--Schwarz to g(0). It gives g(0)^2<=D_t(mu) E[g(X)^2], with equality for
K_t. This optimality concerns the Poisson reference, not the dependent affine law.

## The independent Bernoulli law is accounted for

Let Z_0 be the sum of independent Bernoulli(rho_y) variables from the input fibers,
with mu=sum rho_y and rho_max=max rho_y. For h>=2,

\[
 0\le\mu^h-\mathbb E(Z_0)_h
       \le {h\choose2}\rho_{\max}\mu^{h-1}.               \tag{3}
\]

Expand mu^h over ordered lists of input indices. The factorial moment contains
exactly the distinct lists. A repeated list has an equal pair of positions;
a union bound over pairs gives binomial(h,2)(sum rho_y^2)mu^(h-2), which is
at most the right side. This proof allows nonuniform means and means equal to one.

Set a_l=(-1)^l D_(t-l)(mu)/l!, and expand K_t(x)^2=sum_h f_h (x)_h using

\[
 (x)_a(x)_b=\sum_{v=0}^{\min(a,b)}{a\choose v}{b\choose v}v!(x)_{a+b-v}.
\]

Let F_h be the same coefficient sum with |a_a a_b| in place of a_a a_b.
Then |f_h|<=F_h, and (2)--(3) prove

\[
 |\mathbb E K_t(Z_0)^2-D_t(\mu)|
 \le\rho_{\max}\sum_{h=2}^{2t}F_h{h\choose2}\mu^{h-1}.    \tag{4}
\]

Each F_h is a polynomial in mu with nonnegative coefficients and degree at most
2t-h. Since D_t(mu)^2>=mu^(2t)/(t!)^2, dividing the right side of (4) by D_t^2
leaves a bound that is a sum of negative powers of mu. Thus the existing lower
bound on mu can be used without knowing the exact candidate count.

For the radius-R raw ball at draw 13, each output fiber lies in an m-dimensional
integer ball of radius R. The inward-half-cube argument gives

\[
 \rho_{\max}\le2V_m(R^2+m/4)^{m/2}/q^m.                  \tag{5}
\]

With t=5, q=3329, m=400 and the Part 250 radius and count bounds, outward interval
arithmetic verifies 1/(rho D_5(mu))<2.274e-12 and the normalized (4) bound
<2.575e-293. No approximation of the independent Bernoulli law by a Poisson law
is left uncharged.

## Transferring the dependent-component estimates

Expand exactly in the centered variable z:

\[
              K_5(\mu+z;\mu)^2=\sum_{j=0}^{10}c_j(\mu)z^j.
\]

The verifier constructs these polynomials over the rationals before numerical
evaluation. Each c_j has degree at most 10-j in mu. Define bar-c_j by taking
absolute values of its monomial coefficients. For any class of supports, a
bound B_j on the sum of absolute tuple corrections in the j-th central moment
therefore bounds its polynomial correction by sum_j bar-c_j(mu) B_j.
The corrections at orders zero, one and two are zero: individual means and
pairwise independence match the independent input-fiber model exactly.

Apply the component bounds from Parts 254--256 for j=3,...,10. Their activity
polynomials have nonnegative coefficients and total mu degree strictly less
than j for every term with an activated component. After multiplying by
bar-c_j and using D_5^2>=mu^10/(5!)^2, all powers of mu are negative. The candidate
lower count is again a valid substitution.

Allowing every connected component of size at most eight, as well as every circuit
and rank-two component through size ten, gives normalized correction <4.859e-22.
The same absolute-coefficient transfer through size nine is **not** sufficient:
its displayed majorant exceeds 8.68e-11. The previous size-nine result for a
single twelfth central power cannot be copied to this different polynomial.

Let R_large be the signed polynomial-moment correction from supports containing
a connected component of size nine or ten, rank >=3 and nullity >=2. The exact
remaining obligation is explicit:

\[
 \Pr(b_{13}>0.280)\le
 2.274\cdot10^{-12}+2.575\cdot10^{-293}+4.859\cdot10^{-22}
                  +\frac{|R_{\rm large}|}{0.280D_5(\mu)^2}.       \tag{6}
\]

This route needs no moments above order ten and hence no supports of size eleven
or twelve. It still needs a sharper joint-constraint count for the size-nine and
size-ten components, and it does not resolve draws 14--404 or the selected
projection issue. Equation (6) is conditional on bounding its explicit remainder;
dropping that term would be incorrect.

## Verification

Run `python3 docs/research/scripts/wall1_affine_square_certificate.py`.
It checks the polynomial identities, the Poisson factorial-moment identity,
pointwise nonnegativity and normalization, and the Bernoulli correction using
139 exact rational checks. The centered square is computed symbolically with
rational bivariate coefficients. Outward 80-digit interval arithmetic verifies
the reference, Bernoulli, and transferred component bounds and the limitation of
the size-nine transfer. These are paper proofs with finite regression checks;
this addition is not Lean-formalized and does not simulate the selected process.
