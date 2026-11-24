# Integer-section volume floors throughout the selected restart

This applies the existing coordinate-minor lemma with stage-dependent rank
thresholds. It extends the exactly cubic exclusion to a quantitative bound
on the determinant of every selected integer section, simultaneously at
freezes21 through406. The joint exception is below3.86e-28. It does not
bound the remaining void probability.

Use the exact width506 forward restart, uniform systematic rank400 graph,
q=3329, N=505+f, frozen space F, primitive section S_F=F intersect Z^N,
p_F=(det S_F)^2, and quotient rank d. Existing identities give

    det K=1/sqrt(p_F), D=q^d/sqrt(p_F).

Let L_f be the unconditional determinant floor from
[cubic-history exclusion](wall1_cubic_history_exclusion.md), using the
already certified Hermite cap56.2142 and the height-q period.
For each f choose the largest integer k<min(f,400) for which

    2 binom(505+f,f) q^(-(400-k)(f-k)) < 10^(-30),

and put s_f=k+1. The same finite Grassmannian count as in that note
shows that, except on an event of probability less than386*10^(-30),
every f-column coordinate restriction has rank at least s_f, for all
386 stages simultaneously. Prefixes and coordinate choices need not be
independent. This is an event in the original input law.

## From coordinate ranks to selected volumes

The [coordinate-minor lemma](wall1_integrality_bound.md) then gives,
for every rational frozen f-space, simultaneously,

    p_F >= 2^max(0,s_f+d-400).

For completeness, take a primitive integer basis matrix X of S_F and
choose f rows I forming an invertible matrix modulo q. If the complementary
row block has rank u, the ranks of sigma X and sigma_I X_I differ by at
most u; hence u>=s_f-(400-d). Every subset of u independent complementary
rows extends to a basis using rows from I. The resulting2^u distinct
integer maximal minors are nonzero modulo q. Cauchy--Binet makes p_F
their squared sum, yielding the inequality. This does not model the
selected space as an independent random subspace.

Combining the volume inequality with D>=exp(L_f) requires

    d log q - (1/2)max(0,s_f+d-400)log2 >= L_f.           (1)

The left side is strictly increasing in d. Let d_f be the smallest
integer not excluded by (1), and h_f=max(0,s_f+d_f-400). Then
d>=d_f and p_F>=2^h_f on the single good event. Selected examples are:

| Freeze f | Coordinate rank s_f | Quotient rank d_f | log2 p_F lower bound h_f |
|---|---:|---:|---:|
|21|21|380|1|
|100|100|307|7|
|200|200|230|30|
|300|300|168|68|
|375|373|130|103|
|395|388|120|108|
|400|391|118|109|
|404|393|116|109|
|406|394|115|109|

Thus, for example, at freeze404 the retained ambient projected grid has
determinant at most2^(-109/2). This is a covolume statement: it does not
by itself bound a norm distance between lattice shapes or imply isotropy,
smoothing, independent labels, or a covering-probability estimate.

## Verification and probability accounting

`scripts/wall1_selected_volume_profile.py` verifies all386 rank-union
comparisons by integer arithmetic and rejects each incompatible rank in
(1) with outward intervals. The positive interval at the first accepted
integer confirms it is not rejected by this scalar condition; it does not
assert that a state attaining all the lower bounds exists.

An independent verifier checked all386 chosen k values and their next
larger alternatives by exact arithmetic, and checked the d-1/d thresholds
with70-digit intervals. All displayed rows agreed. The general rank,
minor-counting, and original-law probability arguments also passed review.

This reuses the published-in-repository Hermite certificate and existing
minor lemma. It is a quantitative extension, not a new proof of either
input. Compared with the older late-stage choice of fixed deficiency17,
the new rank thresholds give stronger late volume floors and cover more
stages, at the price of a larger (still tiny) exceptional probability.
The older10^(-748) exception remains useful when multiplying by enormous
uncapped counts; it must not be replaced indiscriminately by3.86e-28.

For any bounded failure indicator, its contribution on the new exceptional
event is at most3.86e-28. The same holds for a single potential in[0,1].
This bound is joint across stages, so a first-exception event need only be
charged once. A sum of uncapped moment counts has no such automatic
bound. Conditioning the entire run on the good event may change fresh-mark
laws; a continuation proof must retain original-law stopped weights or
otherwise justify its conditional laws. The nonexceptional selected-history
moment estimate required by the BKZ proof is still missing.

## What the same rank information buys in a Gaussian count

The information used above is stronger than a covolume bound alone. Write
Lambda=F-perp intersect Z^N=K^*, of rank r=505, and
theta(t)=sum_(z in Z) exp(-t*z^2). If the complementary row block of X
has rank u, choose u independent rows there and complete them with f-u
rows of the original pivot set I to obtain another coordinate basis I'
of F. The complements J,J' are coordinate bases of F-perp, with overlap
size r-u. Real independence follows from independence modulo q.

For a fixed value c of the shared coordinates, the projections of
Lambda's fiber onto J minus J' and J' minus J are each injective. Dropping
all coordinates outside their union and applying Cauchy--Schwarz bounds
the fiber's Gaussian sum by exp(-t*||c||^2)*theta(2t)^u. Each of the two
sums in Cauchy--Schwarz is bounded by the full integer Gaussian sum in u
coordinates, so no determinant or fiber-multiplicity factor is omitted.
Summing over c gives

    theta_Lambda(t) <= theta(t)^(r-u)*theta(2t)^u
                    <= theta(t)^(r-h_f)*theta(2t)^h_f.    (2)

This is a two-injective-coordinate-chart bound, proved pointwise on the
same good event. It does not assert independence of coordinates or of
the selected subspace. Independent mathematical review confirmed (2).

For a radius-R ball and any beta>0, Gaussian majorization and Poisson
summation give

    #(K intersect B_R)/q^d
      <= exp(beta R^2)*(pi/beta)^(r/2)
         *theta_Lambda(pi^2/beta)/D.                    (3)

Here D=q^d det K. In particular the factor sqrt(p_F) from the grid density
cancels against the quotient size. Inserting an additional volume-saving
factor into (3) would be incorrect. The improvement over the previous
single-chart theta bound is only

    [theta(2t)/theta(t)]^h_f, t=pi^2/beta.

At the isotropic choice beta=r/(2R^2), r=505 and h_f=109, the checker
certifies the following relative decreases of that theta envelope:

| R | Relative decrease |
|---|---:|
|30.5|between3.52366e-14 and3.52367e-14|
|35.15|between2.31653e-19 and2.31654e-19|
|40|between1.50539e-25 and1.50540e-25|

It uses four positive theta terms and a rigorous geometric remainder;
an independent70-digit calculation reproduced the first value. This is
numerically negligible for this isotropic count, not a substantial gain
in the selected-history budget. Moreover (3) is an upper bound on an
average candidate count, not an upper bound on void. The volume profile
and (2) remain valid, but this direct application does not close the
missing coverage or signed-moment estimate.
