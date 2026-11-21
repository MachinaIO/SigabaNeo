# The quotient after choosing a shortest vector of a Haar lattice

The recursive exact-SVP definition of HKZ admits an explicit joint density for its Gram–Schmidt lengths. Its first transition is a Haar quotient weighted by a torus avoidance probability. The weight can vanish on an open set of quotient shapes. The recursion below retains this weight at every depth and gives a bounded-error integral for the joint density. A finite-width tour needs an additional selector for the block on which its oracle acts.

## What Proposition 3 says

Write $X_n=SL_n(\mathbb R)/SL_n(\mathbb Z)$ with invariant probability $\mu_n$, $a_i=\|b_i^*\|$, $y_i=\log a_i$, $P_k=\sum_{i\le k}y_i$, and $x_i=(i-1)/n$. In v1, quasi-HKZ means size reduction, HKZ in the quotient by the first vector, and $3a_1^2/4\le a_2^2+\mu_{2,1}^2a_1^2$. This includes every HKZ basis. The proposition quantifies over bases and hence over any algorithm returning such a basis. With probability $1-e^{-\Omega(n)}$ it gives, simultaneously over these bases,
$$
\max_{0\le k\le n}|P_k/(n\log n)-p(k/n)|=o(1),\qquad
p(x)=-\tfrac12(1-x)\log(1-x),\quad p(1)=0.
$$
It also gives, for each fixed $0<\varepsilon<1$ with the same high probability,
$$
n^{-1}\sum_{x_i\le1-\varepsilon}
\left|y_i/\log n-\tfrac12(1+\log(1-x_i))\right|=o(1).
$$
Thus prefix covolumes concentrate even under adaptive choice. The second conclusion is a mean absolute error. Neither conclusion specifies a conditional transition density. The proof bounds maxima by summing over eligible primitive pairs and applying quotient averaging. [Abstract](https://arxiv.org/abs/2610.15265) · [Definitions, Proposition 1 and Proposition 3, equations (4.9)–(4.13)](https://arxiv.org/html/2610.15265v1)

## Primitive incidence and the selected law

Let $d\ge2$, $m=d-1$, $V_d=\pi^{d/2}/\Gamma(1+d/2)$. Count both signs in the primitive-vector incidence measure $\mu_d(dL)\sum_{v\in L_{\rm prim}}\delta_v$. Its marginal in $v$ is $dv/\zeta(d)$. Given $v=r\theta$, choose oriented orthonormal coordinates transversely, draw $H\sim\mu_m$, put $M=r^{-1/m}H$, and take a Haar character $t:M\to\mathbb R/\mathbb Z$ (independent uniform phases on a basis). The fiber lattice is
$$
E(v,H,t)=\{y+rs\theta:y\in M,\ s\bmod1=t(y)\}.
$$
Here $X_1$ is a point. Indeed the marked space is $G/\Gamma_{e_1}$, for $G=SL_d(\mathbb R)$ and the **integer** vector stabilizer. Unfolding the sum over $\Gamma/\Gamma_{e_1}$ gives its invariant measure. The base is $G/G_{e_1}$, the nonzero vectors. The real stabilizer consists of matrices with first column $e_1$, lower right block in $SL_m$ and arbitrary top row after its first entry. Modulo its integer subgroup the block gives $X_m$ and the row gives a torus over each block. Translation invariance makes its conditional law uniform and block invariance gives $\mu_m$. Transport to $v$ scales the transverse directions by $r^{-1/m}$. Primitive Siegel fixes the overall constant. This is a disintegration of an infinite counting measure. A uniform draw from all primitive vectors of one lattice does not exist. [Laarhoven, Proposition 1 and its unfolding reference](https://arxiv.org/html/2610.15265v1#S2.SS2)

**First-step law.** Use a fair sign for the shortest pair. Write $\|s\|_{\mathbb T}$ for distance to the nearest integer and set
$$
I_r(H,t)=\prod_{y\in M,\ 0<|y|<r}
{\bf1}\{|y|^2+r^2\|t(y)\|_{\mathbb T}^2\ge r^2\},
\quad w_r(H)=\int I_r\,dt,\quad Z_d(r)=\int w_r\,d\mu_m.
$$
Only finitely many projections occur. Minimizing over lifts proves that $I_r$ tests precisely whether there is a shorter off-line vector. Distinct primitive lines tie on a Haar-null set (countably many nonidentical analytic equal-length equations on $G$). Thus multiplying incidence by $I_r/2$ counts a unit mass per lattice. In particular the joint law of the signed first vector and the normalized quotient is
$$
\frac{dv}{2\zeta(d)} w_{|v|}(H)\,d\mu_m(H).
$$
The direction is uniform independent of the length and intrinsic quotient shape. The length density is $c_d(r) Z_d(r)$ where $c_d(r)=d V_d r^{d-1}/(2\zeta(d))$. At positive density the conditional quotient has Radon–Nikodym derivative $w_r/Z_d(r)$. The exact tail follows by integrating this density above the threshold.

**Quantitative Haar comparison.** If $\lambda_1(M)<\sqrt3\,r/2$ a shortest transverse vector has a lift with height at most $r/2$, forcing $w_r=0$. If $\lambda_1(M)\ge r$ then $w_r=1$. For $m\ge2$ this gives
$$
\mu_m\{\lambda_1(H)<(\sqrt3/2)r^{1+1/m}\}
\le d_{\rm TV}(\mathcal L(H\mid b_1=v),\mu_m)
\le 1-Z_d(r)\le\min\{1,V_d r^d/2, V_m r^d/(2\zeta(m))\}.
$$
The lower bound is positive since the cusp contains a nonempty open set. The upper TV bound follows by conditioning the full fiber on acceptance (TV cost $1-Z_d$) and projecting. The last term counts transverse primitive lines by Siegel. For the ball-volume term count *all* off-line pairs of lifts shorter than $r$. For each nonzero $y$, $t(y)$ is uniform even when $y$ is divisible. Summing over integer heights and averaging gives vertical slice length divided by $r$. Siegel on $M$ contributes transverse intensity $r$, and division by two removes signs. The expected count is $V_d r^d/2$. Markov proves the bound. Thus a very short first vector gives controlled absolute error for **every** tail observable, including the entire HKZ profile computed in its quotient. At volume of order one the estimate need not be small.

## What two moments determine

For $d\ge3$ and a centered ball or symmetric annulus $S$ of volume $V$, let $N$ count primitive pairs in $S$ and $h=V/(2\zeta(d))$. Then $\mathbb EN=h$ and $\mathbb E[N(N-1)]=h^2$. Distinct pairs correspond to independent vectors. Rogers order two gives Lebesgue product intensity on independent ordered vectors. Möbius inversion in the two contents multiplies it by $1/\zeta(d)^2$ (absolute convergence by the product of the two divisor sums $\sum j^{-d}$). Divide by four for signs. Hence for a ball of radius $R$,
$$
\max(0,1-h)\le\Pr(\lambda_1>R)
\le\min(1-h+h^2/2,1/(1+h)).
$$
These follow from Bonferroni and Cauchy–Schwarz. For a fixed shell the same moments give $\Pr(N\ge j)\le h^2/[j(j-1)]$ for $j\ge2$. For the random near-minimum window $[\lambda_1,C\lambda_1]$, $C\ge1$, the probability of a second primitive pair is at most $\Pr(\lambda_1>R)+h(CR)^2/2$ for any $R$, with $h(s)=V_ds^d/(2\zeta(d))$. Its exact count law can instead be obtained in the selected fiber by enumerating primitive lifts up to $Cr$ with the weight $I_r$. For $C<2$ all nonzero vectors in that window are primitive.

For a fixed ball the alternating sums through consecutive orders $j-1,j$ bracket the void probability with width $\mathbb E\binom Nj$. Primitive factorial moments with $j<d$ follow by content inversion and removal of repeated lines (equivalently truncate the content sieve first, then use dominated convergence against the integrable order-$j$ count). At fixed dimension “all orders” in the repository means $1\le j<d$. It does not justify an infinite inclusion–exclusion exchange. In the fixed fiber, inclusion–exclusion over the *finite* list of projected competitors is exact, using intersections of torus strips, with shared character phases. The archived marked lens moments concern different observables. [Stage 3 and archive rebuild](../PROOF_GAP.md#stage-3-sieving-assumption-b)

## Exact recursion for all HKZ lengths

Choose successive shortest pairs in the entire projected quotient and size-reduce the lifts. Work at unit determinant at each step. Denote the chosen normalized length in dimension $d$ by $s_d$. For any proposed positive tuple $(s_n,\ldots,s_2)$ construct random lattices **from the bottom up**. Start with $H_1=\mathbb Z$. At level $d$ draw fresh Haar character coordinates $t_d$ on $s_d^{-1/(d-1)}H_{d-1}$, evaluate $J_d=I_{s_d}(H_{d-1},t_d)$, and set $H_d=E(s_de_1,H_{d-1},t_d)$ with transverse coordinates in $e_1^\perp$. Then the Lebesgue density is exactly
$$
f(s_n,\ldots,s_2)=\left(\prod_{d=2}^n c_d(s_d)\right)\mathbb E\left[\prod_{d=2}^n J_d\right].
$$
To prove it, unfold the top shortest pair retaining the full reconstructed lattice in the integrand. Unfold its normalized Haar quotient by the same identity, carrying the outer shortest test as a function of the reconstructed quotient. Repeat to dimension one. Rotations disappear because the lengths and acceptance tests are intrinsic and character Haar measure is invariant under basis changes. Null tie sets stay null under the weighted disintegrations. This proves normalization and avoids any conditional independence assertion about selected shapes. For physical lengths start with $D_n=1$ and use $a_{n-d+1}=D_d^{1/d}s_d$, $D_{d-1}=D_d/a_{n-d+1}$, ending with $a_n=D_1$. Here $D_d$ is the remaining physical covolume.

There is an explicit absolute integration error even for deep prefixes. Sample each $s_d$ independently with density proportional to $c_d$ on $(0,2V_d^{-1/d}]$ (Minkowski's bound). The normalizing integral is $K_d=2^{d-1}/\zeta(d)$. For any measurable profile event $A$ the estimator per draw is $K\mathbf1_A\prod J_d$, $K=\prod K_d$. The recursion proves unbiasedness. For $N$ independent draws Hoeffding bounds the absolute error of their mean by $K\sqrt{\log(2/\delta)/(2N)}$ with confidence $1-\delta$. At a fixed tuple the same bound for the density uses $\prod c_d(s_d)$ instead of $K$. These are finite-dimensional error bounds for exact arithmetic, potentially expensive. They give no efficient asymptotic approximation by independent Haar minima.

## Finite blocks, planting and transfer

For a concrete finite-width first call one must specify how the input basis is drawn. Here is one exactly solvable block initialization. Sample a primitive rank-$b$ sublattice $U$ by incidence with covolume $D$ in $[A,B]$, $0<A<B$, $2\le b<n$, normalizing the count over all $(L,U)$. Extend a basis of $U$ to the input basis and apply exact SVP in its first block. By Laarhoven's Lemma 2, $D$ has density $nD^{n-1}/(B^n-A^n)$, and the two normalized block shapes are independent Haar (up to rotation). The first oracle length is $D^{1/b}s_b$ and the within-block quotient has the selected law above in dimension $b$. This initialization biases the ambient lattice by its number of eligible blocks. For ordinary Haar input and a basis section, the extra factor under incidence is the indicator that the section selects $U$ (or its conditional probability with coins), without the covolume cutoff. This follows by summing the indicator over primitive blocks, which counts one block per input. Subsequent overlapping primal or dual calls require the analogous selection test for the entire basis history, including lifts. Exact SVP alone supplies no law for that selector. The HKZ recursion applies to the first call of full width and to HKZ *within* a known block. A closed transition or quantitative profile estimate for ordinary finite-width slide on Haar input remains open here. [Split averaging, Lemma 2](https://arxiv.org/html/2610.15265v1#S2.SS3) · [Profile-history obstruction](wall1_profile_only.md)

One can nevertheless integrate a **specified slide implementation on ordinary Haar input** with an explicit error. In the bounded-radius recursion retain the reconstructed $H_n$ and apply an independent Haar rotation $O\in SO(n)$. For a measurable input basis section $B(L)$, an almost surely terminating reducer $S$ with fixed schedule and tie rules, and an output-prefix event $A$, replace $\mathbf1_A$ in the estimator by $\mathbf1\{S(B(OH_n))\in A\}$, interpreting $A$ on the output basis. Include the reducer's actual random coins if applicable. The proof of the recursion with a bounded terminal test gives the Haar integral of its rotational average, which equals its Haar integral by invariance. The same $K$ and absolute error apply. Equivalently the proposals accepted by $\prod J_d=1$ give exact Haar inputs after rotation, with acceptance probability $1/K$. This construction gives the joint pushforward law, including the first selected minimum and quotient, for any fixed initialization and implementation. Its rare acceptance and the need to execute the tour leave the analytic finite-width profile problem intact.

For a primitive plant of prescribed length $r$, use the probability fiber $E(r\theta,H,t)$ with uniform direction. Adjoining an independent vector directly to an ambient full-rank lattice almost surely gives a nondiscrete group (its multiples have infinite image in the compact quotient torus). In the fiber, HKZ captures the plant in its first pair with probability $Z_n(r)$ for almost every $r$; for $n\ge3$ the same formula holds at every $r>0$, since transverse lengths have diffuse intensity and the phases have continuous marginals. Conditional on capture, the tail is exactly HKZ of the tilted quotient above. On failure the original mark persists as extra data and one must track its image and divisibility under later choices. The preceding short-radius bound quantifies early capture. The repository also gives a deterministic separation criterion for all fully block-reduced outputs in this planting model. [Marked Haar model](wall1_haar_marked.md)

The discrete planted ensemble fixes congruences and an input presentation. Its discrete shapes preclude total-variation approximation by continuous Haar on the full space. A transfer would need estimates on the actual selected observables, for example joint probabilities of capture, vanishing or divisible projected mark, and an off-line competitor of length at most the projected mark's length on the uncaptured primitive stratum. This requires the discrete block selector and control of ties. Haar prefix determinants and unconditional count identities alone supply none of these probabilities. No quantitative transfer or finite-width recovery claim follows here. [Wall 1 frontier and corrected success event](../PROOF_GAP.md)
