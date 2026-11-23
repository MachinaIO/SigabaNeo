# Direct initial-history void bounds from affine graph moments

**Follow-up:** [Part 261](wall1_affine_two_constraints.md) now proves the separate
paper bound P(b_13>0.280)<2.432e-12, using a different degree-ten square certificate
and two-relation counting. The remaining sufficient history target is draws
14--404 with allowance 3.922e-12. The eighth-moment limitation below remains valid
for that older certificate. The new proof is not Lean-formalized or independently audited.

Under the original unconditioned 400-row width-506 restart, the probability that
any of b_7,...,b_12 exceeds 0.280 is less than 7.150e-14. Here b_i is the
smaller-radius void fraction in Part 246, not the long-winner probability.
This bound includes the actual selected projection; it does not assume a law
for that projection. It follows from a raw affine-coset eighth-moment bound.

The numerical bound is a paper proof with exact finite regression and outward
interval checks; it is not independently audited. The affine probability and moment
identities are now formalized in Lean, as detailed below, but the complete numerical
bound is not. The remaining
selected-history probability is still open. In particular the result below is
not a proof of the complete BKZ-506 success theorem.

## 1. Projection domination under the original law

At entry to draw i, let N = 504+i, d = N-400, and let
L(A) = {(x,y) in Z^400 times Z^d : x = Ay mod q}, with q = 3329.
The exposed matrix A is uniform without conditioning on the selected flag.
Let P be the actual orthogonal projector, K = P Z^N, and M = P L(A).
The map Z^N/L(A) onto K/M is surjective, so uniform raw cosets push forward
to uniform projected cosets, even though P depends on A. For every z,

\[
       \operatorname{dist}(Pz,M)\le\operatorname{dist}(z,L(A)).       \tag{1}
\]

Thus at any radius R no larger than the radius defining b_i, that void fraction
is bounded above by the fraction of raw cosets having no representative through R.
No union over frozen subspaces or assumption that P is independent of A is needed.

Every window contains a vertical q-period, so s_j <= q. Consequently

\[
 g_i\ge(q^{400}/V_{506})^{1/506}q^{-(i-1)/506},\qquad S_i\le q.
\]

A valid deterministic raw radius is therefore

\[
 R_i^2=(11/10)^2(q^{400-i}/V_{506})^{2/506}-2.                    \tag{2}
\]

It is positive at all entries used here. If v is independent uniform in F_q^400,
a raw coset is {(x,y):x=Ay+v mod q}. Define the fixed candidate set

\[
 \mathcal S=\{z\in\mathbb Z^N:\|z\|\le R_i,
                    \ |z_j|\le(q-1)/2\ \text{for every }j\}.
\]

Distinct candidates have distinct full residues. Let Z(A,v) count its points in
the raw coset. Some raw cosets can have other, noncentered short representatives;
this only helps coverage. Thus for every rho > 0,

\[
 \Pr_A(b_i>\rho)\le\rho^{-1}\Pr_{A,v}(Z=0).                  \tag{3}
\]

Indeed (1) bounds b_i pointwise by a raw void fraction, which is at most
Pr_v(Z=0 | A). Average over A and apply Markov. This is not an estimate conditional
on a selected history.

## 2. A finite affine-graph moment lemma

For this section let m,d be arbitrary, q prime, N=m+d, and S any finite set of
integer points with distinct residues modulo q. Set C=|S|>0, p=q^(-m), mu=Cp.
For z=(x,y), I_z indicates x=Ay+v. For distinct candidates z_1,...,z_k, write
r for the rank of the columns (y_j,1) over F_q. Then

\[
 \mathbb E\prod_{j=1}^k I_{z_j}=
 \begin{cases}p^r,&\operatorname{rank}(x_j,y_j,1)_{j=1}^k=r,\\
               0,&\text{otherwise.}\end{cases}                 \tag{4}
\]

Each of the m independent affine row functionals is prescribed on an r-dimensional
space. This proves (4), including inconsistent output assignments.

Let C_j count ordered j-tuples of distinct full residues forming an affine circuit:
the augmented columns (z,1) have rank j-1 and every proper subset is independent.
Let T_{k,r} count ordered distinct full k-tuples of augmented rank r. For 2 <= r < k,

\[
 T_{k,r}\le\sum_{j=3}^{r+1}
 {k\choose j}{k-j\choose r-j+1}
 C_j C^{r-j+1}q^{(r-1)(k-r-1)}.                    \tag{5}
\]

Choose one circuit, then extend it to a rank-r spanning set using r-j+1 additional
points. There are k-r-1 remaining points, each in an affine space of dimension r-1,
which has q^(r-1) residues. Uniqueness of the candidate lifts is essential here.
The circuit and extension may not be unique; summing over them is an upper bound.
Circuits have size at least three because full residues are distinct.

Let K_k count ordered distinct k-tuples with dependent augmented *input* columns.
For

\[
 D_k=\sum_{\text{ordered distinct }z_1,\ldots,z_k}
       \left(\mathbb E\prod I_{z_j}-p^k\right),
\]

(4) gives

\[
 |D_k|\le\sum_{r=2}^{k-1}p^r T_{k,r}+p^k K_k.                 \tag{6}
\]

Independent inputs contribute zero. A compatible tuple with rank one would have
identical full residues and is excluded. The second term in (6) is necessary:
inconsistent affine dependencies can affect a centered moment even though their
joint incidence probability is zero.

Compare Z to a sum of C independent Bernoulli(p) variables Z_0. Their raw moments
differ by sum_{k=2}^ell S(ell,k) D_k, where S(ell,k) is a Stirling number of the
second kind; both variables have the same mean mu. Expansion of the eighth central
moment and the triangle inequality therefore give

\[
 \mathbb E(Z-\mu)^8\le \mu+119\mu^2+490\mu^3+105\mu^4
 +\sum_{\ell=2}^8{8\choose\ell}\mu^{8-\ell}
       \sum_{k=2}^\ell S(\ell,k)|D_k|.                       \tag{7}
\]

For the independent central moment only set partitions with no singleton blocks
survive. There are 1,119,490,105 such partitions with 1,2,3,4 blocks. The absolute centered
moment of one Bernoulli variable of any degree at least two is at most p, yielding
the first four terms. This proves (7) without an independence claim for Z.

## 3. Explicit Gaussian bounds for the dependency counts

Write theta(t)=sum_{z in Z} exp(-t z^2). For beta > 0 put T=sqrt(pi/beta) and

\[
 A_j(\beta)=\theta(\beta q^2/j)
              \prod_{h=1}^{j-1}\left(1+T\sqrt{h/(h+1)}\right).  \tag{8}
\]

For any nonzero coefficients lambda_1,...,lambda_j in F_q,

\[
 \sum_{\sum\lambda_h z_h=0\bmod q}e^{-\beta\sum z_h^2}
       \le A_j(\beta).                                     \tag{9}
\]

To prove (9), periodize the one-dimensional Gaussian modulo q. Its finite Fourier
transform is nonnegative by Poisson summation. Multiplication by each nonzero lambda_h
permutes the frequencies. Holder bounds the product sum by the sum of j-th powers
of the same transform, namely the Gaussian sum with all coefficients equal to one.
The layers sum z_h = qt are translates of the root lattice of rank j-1, with
Gram--Schmidt lengths sqrt((h+1)/h); their perpendicular heights are qt/sqrt(j).
Each shifted one-dimensional Gaussian is at most 1+T/length (integrate its level sets).
Summing successive coordinates and then the layers gives (8).

For candidate points in the radius-R ball, each circuit has a relation with all
coefficients nonzero and sum of coefficients zero. After normalizing the last
coefficient there are at most q^(j-2) possibilities. Exponentially majorize the
j ball indicators and apply (9) independently in all N coordinates. Therefore

\[
 C_j\le Q_j:=q^{j-2}e^{j\beta_jR^2}A_j(\beta_j)^N,
 \qquad \beta_j=\frac{(j-1)N}{2jR^2}.                         \tag{10}
\]

**Retaining the affine constraint for triples.** Equation (10) discards the
coefficient-sum-zero condition after counting possible relations. For j=3 that loss
is too large for the eighth moment at draw 12. We instead use the following explicit
finite coefficient certificate.

Normalize every three-point relation as (t,-1-t,1), with t != 0,-1 in F_q. The script
enumerates integer triples nu=(u,v,w) with u+v+w=0, squared norm at most 2q, and all
coordinates nonzero modulo q. It checks a primitive representative for every one
of the q-2=3327 normalized relations: nu is a nonzero scalar multiple of that relation
modulo q, and gcd(u,v,w)=1. Its squared norms range from 6 to 6422. This is an exact
integer enumeration, not a random sample or an unverified existence assumption.

For one recorded normal of length b, its integer kernel has covolume b. It contains
the primitive vector (1,1,1); completing that vector to a kernel basis gives
Gram--Schmidt lengths sqrt(3) and b/sqrt(3). The layers nu dot z = qh have heights
qh/b. Hence its Gaussian congruence sum is at most

\[
 M_b(\beta)=\left(1+\frac{T}{\sqrt3}\right)
             \left(1+\frac{T\sqrt3}{b}\right)
             \theta(\beta q^2/b^2).
\]

Multiplying a coefficient vector by a nonzero residue does not change its modular
kernel. Thus (10) for j=3 can be replaced by the stronger, explicitly finite bound

\[
 Q_3=e^{3\beta_3R^2}\sum_{t\ne0,-1}M_{b_t}(\beta_3)^N.       \tag{10a}
\]

Every normal's primitiveness, zero coefficient sum, and modular label are checked
in the verifier. Grouping equal squared norms is exact. For j>=4 use (10) unchanged.
The interval calculation bounds theta(t) by 1+2 exp(-t)/(1-exp(-3t)), or first uses
Poisson's identity theta(t)=sqrt(pi/t) theta(pi^2/t) when t<pi.

For K_k, there are (q^(k-1)-1)/(q-1) possible projective relations with coefficient
sum zero. Their support can be as small as two. A relation on s >= 2 coordinates
has Gaussian sum at most theta(beta)^(s-2) A_2(beta): bound s-2 Fourier factors by
their maximum theta(beta), and apply Cauchy--Schwarz to the remaining two frequency
permutations. The unused coordinates are free. Since theta(beta) <= 1+T, we obtain

\[
 K_k\le B_k:=\frac{q^{k-1}-1}{q-1}e^{k\beta_0R^2}
     (1+\sqrt{\pi/\beta_0})^{km+(k-2)d}A_2(\beta_0)^d,
 \qquad\beta_0=\frac{N}{2R^2}.                              \tag{11}
\]

Only the d input coordinates carry these relations; all m output coordinates
remain free in (11). Treating K_k as a full-vector dependency count would be wrong.

## 4. A computable lower count and the normalized moment

Put a=sqrt(R^2-(N-2)/4) and L=R+sqrt(N)/2. At the radii used here, a>0 and L>1664.
The two-coordinate rounding bound of [Part 225](wall1_raw_graph_winner_cap.md) gives

\[
 C\ge C_*:=V_Na^N-\frac\pi{\sqrt2}V_{N-1}a^{N-1}
  -2N V_{N-1} L^N(1-(1664/L)^2)^{(N-1)/2}.                   \tag{12}
\]

The subtracted term covers noncentered integer points: their centered unit cubes
lie inside the radius-L ball and in the union of coordinate caps |x_j| >= 1664.
A cap is bounded by its maximal cross-section times an interval of length L.
The first two terms use mean-preserving rounding in N-2 coordinates and the disk
count from the last two; the convex function (sqrt(y_+)-1/sqrt(2))_+^2 justifies
averaging the rounding error. This is a lower bound for the actual finite candidate
set, not its Euclidean volume used as an equality.

Define mu_* = C_* p, gamma_j = Q_j/C_*^(j-1), kappa_k = B_k/C_*^k, and

\[
 a_{k,r,j}={k\choose j}{k-j\choose r-j+1}q^{(r-1)(k-r-1)}.
\]

Combining (5)--(12) and dividing by mu^8 proves

\[
 \Pr(Z=0)\le\mathcal B_8:=\mu_*^{-7}+119\mu_*^{-6}+490\mu_*^{-5}+105\mu_*^{-4}
 +\sum_{\ell=2}^8{8\choose\ell}\sum_{k=2}^\ell S(\ell,k)
 \left[\kappa_k\mu_*^{k-\ell}
  +\sum_{r=2}^{k-1}\sum_{j=3}^{r+1}
      a_{k,r,j}\gamma_j\mu_*^{r-\ell}\right].                \tag{13}
\]

All powers of mu_* in the bracket are nonpositive. Replacing C and mu by their
lower bounds therefore has the correct direction. On Z=0 the normalized eighth
power is one, which is the final Markov step. Equations (3) and (13) bound the
selected-history exit probability by B_8/rho.

## 5. Initial draws and the remaining target

With m=400, N=504+i, R=R_i from (2), rho=0.280, the outward interval calculation gives:

| Draw i | Upper bound for Pr(b_i > 0.280) |
|---:|---:|
| 7 | 1.598e-34 |
| 8 | 1.656e-30 |
| 9 | 1.957e-26 |
| 10 | 2.641e-22 |
| 11 | 4.066e-18 |
| 12 | 7.149e-14 |

The sum of the unrounded enclosures is below 7.150e-14. These are probabilities
under the original matrix distribution, including every choice made by the specified
shortest-vector rule. They concern the void fractions, rather than merely a moment
of the winner length.

Combining this charge with [Part 249](wall1_correlation_mgf.md), it would now suffice
for the vertical compensator route to prove

\[
             \Pr\left(\max_{13\le i\le404}b_i>0.280\right)
                        \le6.354\times10^{-12}.              \tag{14}
\]

Indeed 7.150e-14 + 6.354e-12 + 1.174e-12 < 7.6e-12. Equation (14) remains open.
The other score, horizontal and prefix-rejection obligations are also unchanged.
The raw unprojected radius loses too much at later draws to claim the same bound
throughout the tour; the new certificate does not silently resample the selected
projection or replace it by a Haar law.

## Verification scope

Run `python3 docs/research/scripts/wall1_affine_void_moments.py`. The script uses
80-digit interval arithmetic for (8)--(13), including (10a), and rational arithmetic for regression
of (5)--(7). It enumerates 893 nonempty subsets of three finite fixtures and every
affine graph law for each fixture (9,27,243 laws respectively). The fixtures include
a six-point circuit whose augmented input rank is five. These finite regressions
check the combinatorial formulas but do not replace the general proof above.


## Boundary of this certificate

The same raw-radius method does not certify the rest of the tour. At draw 13,
the leading independent eighth-moment term alone, 105/(rho mu_*^4), already exceeds
1.4e-9 using this lower count. That is a limitation of the displayed majorant,
not a lower bound for the actual exit probability. Raising the moment order also
increases the rank-pattern losses in (5)--(7); it must be checked, not assumed to
improve the estimate. The small raw radius at later entries still discards substantial
projection shortening. Equation (1) is valid, but its converse is not available.


There is also a barrier independent of the chosen moment order. At the deterministic
radius R_16 in (2), N=520. For each integer point z in the ball, the inward half of its
unit cube satisfies ||z+u||² <= R_16²+N/4. These half-cubes have disjoint interiors and
volume 1/2. Hence the fraction of raw cosets that can be covered is at most

\[
 \frac{\#(\mathbb Z^{520}\cap B_{R_{16}})}{q^{400}}
 \le\frac{2V_{520}(R_{16}^2+130)^{260}}{q^{400}}<0.707088.
\]

Every raw graph has exactly q^400 cosets, regardless of its matrix. Thus the raw void
fraction at this radius is greater than 0.292912 for **every** matrix. Merely raising
the moment order, or counting the same raw ball more accurately, cannot prove a
0.280 ceiling for this dominating raw void observable. This is not a lower bound
for b_16: the selected projection can shorten representatives, and the actual radius
can exceed R_16. A different probabilistic scale floor or a projection-aware count
could therefore still help. The interval verifier checks this barrier as well.


## Formalized affine-probability and moment layer

[AffineGraphMoments.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/AffineGraphMoments.lean)
encodes the independent offset as column zero of a uniform finite-field matrix.
`incident_iff` identifies this encoding with x = Ay + v. `system_probability` and
`joint_probability` give the exact probability from input rank and explicit row
feasibility, including incompatible targets. `first_moment` proves the exact mean.
`raw_moment` and `central_moment` give exact finite rank-sum formulas at every order,
including repeated tuple entries and order zero. `void_le_rank_sum` then bounds a
zero hit count using the eighth central moment and any positive center.

File compilation and all nine printed axiom checks pass using only `propext`,
`Classical.choice`, and `Quot.sound`. These theorems apply to a fixed candidate list.
They do not prove the projection domination, circuit-count bounds, Gaussian estimates,
integer-ball bounds, or the final numerical values of this note. In particular, they
do not permit substituting a design-dependent projected candidate list into a
fixed-list probability calculation.
