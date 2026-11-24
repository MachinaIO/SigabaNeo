# Factorial cumulants retain cancellation before the square transfer

This paper reduction replaces the absolute central-monomial transfer with an
exact factorial-cumulant expansion. It also bounds the difference between these
cumulants and connected full-incidence counts, including repeated input labels.
Part442 closes the complete size3..24 incidence-transfer target:
C(F)<1.058e-12<3.01e-12. This independently computed nonnegative envelope
implies the temporary caps below; the cumulant error is then bounded without
circularity. The baseline plus transfer plus error is below1.971e-12.
By the pointwise projection domination in
[affine void moments](wall1_affine_void_moments.md), this bounds
Pr_A(b_14>0.280) under the original unconditioned uniform matrix law, including
the actual selected projection. It does not give a bound conditional on a
selected history. The draws15..404 history estimate remains open, and the
complete BKZ theorem is not proved. These numerical deductions are not
Lean-formalized. Earlier checkpoints below are retained as historical results.

## Exact finite-polynomial transfer

For Z=sum_y J_y and mu=E Z, define factorial cumulants by the formal series

\[
 \log\mathbb E(1+z)^Z=\mu z+\sum_{j\ge2}\kappa_j z^j/j!.
\]

Truncate all series at degree 24; no convergence assertion is needed. For any
polynomial f of degree at most 24, falling-factorial coefficient comparison gives

\[
 \mathbb E f(Z)=\sum_{j=0}^{24}w_j[z^j]
       \exp\left(\sum_{h=2}^{24}\kappa_h z^h/h!\right),
 \qquad w_j=\mathbb E_{X\sim\mathrm{Poisson}(\mu)}\Delta^j f(X). \tag{1}
\]

Indeed for f(x)=sum_l f_l (x)_l, the coefficient multiplying the degree-j term of
the second exponential is sum_(l>=j) f_l l! mu^(l-j)/(l-j)!, exactly w_j.

For f=K_t^2, use Delta^a K_t=(-1)^a K_(t-a) and
E[K_u(X)K_v(X)]=D_min(u,v)(mu). The discrete product rule gives

\[
 w_j(\mu)=
 \sum_{\substack{0\le a,b\le t\\\max(a,b)\le j\le a+b}}
 \frac{(-1)^{a+b}j!}{(j-a)!(j-b)!(a+b-j)!}
                         D_{t-\max(a,b)}(\mu).               \tag{2}
\]

The product-rule coefficient follows by expanding
(Delta_1+Delta_2+Delta_1 Delta_2)^j. Thus w_0=D_t, and w_j has degree at most
t-ceil(j/2). Combine rational coefficients in (2) before taking their absolute
values; call that positive polynomial w_j^+. This preserves cancellation lost
by the previous central-monomial majorant.

## Connected supports, including repeated labels

Consider the multivariate polynomial G((z_y))=E product_y(1+z_y J_y).
Restrict to a finite label set T by setting other variables to zero. If T's
augmented-input matroid splits as a direct sum, its evaluation vectors are
independent. Hence G factors and log G is a sum. Every coefficient supported on
more than one component is zero, including coefficients with repeated powers.
After setting every z_y=z, only connected supports and singleton supports
therefore contribute to kappa_j.

For a fixed ordered j-tuple of labels its contribution is

\[
 \sum_{\pi\in\mathcal P([j])}(-1)^{|\pi|-1}(|\pi|-1)!
 \prod_{B\in\pi}
 \left(\mathbf1_{\text{labels distinct within }B}\,P(B)\right). \tag{3}
\]

The distinctness indicator is essential: these are factorial cumulants, not
ordinary joint cumulants with repeated indices. Formula (3) cancels on a
disconnected label support. Its single-block term, after restricting to connected
supports, sums to F_j, the ordered connected full-incidence count of Part 277.
Set F_2=0. Remaining terms have at least two blocks. Repeated-label Bernoulli
terms are included in them, not discarded or charged a second time.

## A smallest-block bound for all remaining terms

Let A_l be the ordered full joint-incidence count on all distinct l-input
supports. Part 277's component decomposition gives

\[
 A_l\le l![z^l]\exp\left(\mu z+\sum_{h=3}^{24}F_hz^h/h!\right)
                            =:\widehat A_l.                 \tag{4}
\]

Fix a partition pi with p>=2 blocks in (3). Choose one of its smallest blocks B,
of size b<=j/2, deterministically. Its input span intersects the span of all
remaining labels nontrivially. If these label sets overlap, this is immediate.
Otherwise a zero intersection would disconnect their union, contrary to the
connected-support restriction. A singleton union also has a nonzero intersection,
since its label repeats across blocks.

Let B have rank t. Choose its t basis positions in at most binomial(b,t) ways.
The nonzero intersection implies that some one of those basis inputs lies in
the span of the other basis inputs and the remaining blocks' inputs. Union over
its at most t positions. Fix those other inputs first. The redundant input then
has at most q^(j-b+t-2) possible affine values, whose density-weighted sum is at
most q^(j-b+t-2) rho_max.

Count compatible full outputs within B. The other t-1 basis positions have
unrestricted weighted count mu^(t-1). Each nonbasis full point has at most
q^(t-1) completions in the rank-t affine full-point span. The factor q^(-mt)
from P(B) is absorbed by the t full basis density weights. Remaining blocks
retain their joint probabilities and are summed using (4). Basis independence
and compatibility are imposed first, before upper-bounding counts by unrestricted
positive sums. Repeated labels across remaining blocks may be allowed.

Consequently the connected-support sum for this partition is at most

\[
 H_{j,b}\prod_{B'\ne B}\widehat A_{|B'|},\qquad
 H_{j,b}=\rho_{\max}\sum_{t=1}^b{b\choose t}t\,
 q^{j-b+t-2+(t-1)(b-t)}\mu^{t-1}.                            \tag{5}
\]

The exponent j-b+t-2 is nonnegative in the stated range. For an integer partition
lambda=(b_1<=...<=b_p) of j, put
N_lambda=j!/(product_i b_i! product_s multiplicity(s)!). Then

\[
 |\kappa_j-F_j|\le R_j:=
 \sum_{\substack{\lambda\vdash j\\p\ge2}}
 N_\lambda(p-1)!H_{j,b_1}\prod_{i=2}^p\widehat A_{b_i}.        \tag{6}
\]

No extra choice of a smallest block is charged: it was selected deterministically
for each fixed partition. The rank sum and marked basis position in (5) are
genuine union bounds. Choosing a smallest block avoids the large completion
exponent of the earlier proper-subset estimate.

## Transfer, mixed errors, and the actual parameters

For nonnegative activities A_h, with A_2 allowed, define

\[
 \mathcal C(A)=\frac{(12!)^2}{0.280\mu^{24}}
 \sum_{j=2}^{24}w_j^+(\mu)[z^j]
 \left(\exp\left(\sum_{h=2}^{24}A_hz^h/h!\right)-1\right).     \tag{7}
\]

Equations (1), (6), positivity of coefficient majorants, and
D_12(mu)^2>=mu^24/(12!)^2 bound the dependency correction by C(F+R).
Every mixture involving a cumulant error is included in C(F+R)-C(F), evaluated
as the positive transfer of

\[
 \exp\left(\sum F_hz^h/h!\right)
 \left(\exp\left(\sum R_hz^h/h!\right)-1\right).              \tag{8}
\]

Temporarily assume F_h<=mu^h for 3<=h<=24. At the actual draw-14 radius, with
q=3329, N=518, m=400, the mean interval
58.15006220912<mu<118.02042612281, and the existing fiber-density bound,
outward interval arithmetic gives

\[
                     \mathcal C(F+R)-\mathcal C(F)<3.475\,10^{-121}. \tag{9}
\]

Positive numerators are evaluated at the mean upper bound and the normalizing
denominator at the mean lower bound. Repeated-label terms and all mixtures are
included, so no separate independent-Bernoulli correction is needed.

The temporary caps follow from the desired target C(F)<=3.01e-12. The existing
circuit bound proves the h=3 cap. For h>=4 let l_h mu^(d_h) be the leading
monomial of w_h^+. The single-factor term in (7) implies

\[
 \frac{F_h}{\mu^h}\le
 \frac{0.280(3.01\,10^{-12})h!}{(12!)^2l_h}
                         119^{24-h-d_h}<1.                  \tag{10}
\]

All 21 inequalities are checked exactly over the rationals; 24-h-d_h>=0.
The implication alone does not prove the target. Part442 separately verifies
the premise by complete incidence envelopes. Combining (9) with the reference
term gives the following implication, whose premise is now verified:

\[
 \mathcal C(F)\le3.01\,10^{-12}\ \Longrightarrow\
 \Pr(b_{14}>0.280)<9.131\,10^{-13}+\mathcal C(F).              \tag{11}
\]

A sufficient remaining history condition is
C(F)+Pr(max_(15..404)b_i>.280)<=3.0088e-12. It implies the premise of (11) and
fits the earlier 3.922e-12 allowance. The later-history term is still not
established here; a sufficient rounded budget for it is1.951e-12.

## Historical numerical reach through Part 343

Apply (7) to Part 280's envelopes, admitting all circuits and rank-two components
at every size and other components up to a cutoff. The new transfer is:

- below 2.195e-45 through size eleven;
- below 4.247e-30 through size twelve;
- below 2.175e-13 through size thirteen, after Part 283's strengthened counts.
- below 5.396e-13 through size fourteen, after Parts 288 and 291--293.
- below 3.419e-13 through size fourteen and 3.419e-13 through size fifteen,
  after Parts 312--324. Part 314 covers the determinant-twenty anchors
  separately and keeps every remaining short-code stratum.
- below 9.583e-13 through size sixteen, after Part 328's separate
  seven-position determinant23 anchor cover.
- below 3.459e-13 through size sixteen, after Part 343's shared-anchor
  two-point Gram strata.

These are envelopes for admitted components, not lower bounds on failures or
full failure upper bounds. At those checkpoints sizes17--24 were uncontrolled. Part 327's
failed size16 cutoff was superseded by Part 328: its full cutoff transfer
was about9.582432310768002e-13 from above, below9.583e-13. Part 343
improved it to about3.45843824783e-13, below3.459e-13. The then
remaining sufficient allowance for sizes17--24 plus later histories is
2.6629e-12 after the admitted size16 cutoff. Indeed,
(0.3459+0.9131+2.6629)e-12=3.9219e-12<3.922e-12. At Part343, both the total C(F) target and
the later selected-history condition were unproved. Part442 closes the former;
the latter remains open.

For these evaluations the lower mean can be used termwise: known full-incidence
bounds have mu-degree at most h-4 (circuits have degree zero), and the degree
bound after (2) leaves negative total powers after normalization. Exact rational
coefficients are constructed first, then geometric quantities are evaluated
with 80-digit outward intervals.

Run python3 docs/research/scripts/wall1_factorial_cumulants.py. It checks 240
exact Poisson-difference/transfer identities and 1866 exact connected-support
cancellation and cumulant-error inequalities on affine designs with nonuniform
fibers, repeated labels, zero/full fibers and independent components. It then
checks the actual-parameter estimates and cap implications. Finite regressions
support the general proofs but do not replace them, certify the unknown
incidence counts, or provide a Lean proof of BKZ.
