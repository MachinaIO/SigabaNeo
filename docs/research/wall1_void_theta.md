# Gaussian smoothing of the fixed-profile void test

For every positive diagonal and every smoothing parameter, the theta count fails log-concavity on the size-reduction cube in every width at least two. The obstruction already occurs when only one shear varies. Gaussian smoothing does give an exact limiting test for the void and an explicit finite-temperature upper threshold on the void event. Turning either test into a probability estimate requires a lower-tail bound specific to this lattice ensemble.

## A threshold and the exact first moment

Normalize lengths by the head, put $a_j=g_j/g_0$, and write $L=B(g,\mu)\mathbb Z^w/g_0$ in upper triangular coordinates. Let $M(r)$ count all nonzero points of length at most $r$, including both signs. Write $s=\pi t>0$ and $T_s=\Theta_t$. Then
$$
 T_s=\int_0^\infty 2sr e^{-sr^2}M(r)\,dr .
$$
This follows by integrating each indicator and applying Tonelli. On the void, the points are unit-separated. Disjoint open balls of radius $1/2$ about points of length at most $r$, including the origin, fit inside the ball of radius $r+1/2$. Hence $M(r)=0$ for $r<1$ and $M(r)\le(1+2r)^w-1$ otherwise. In particular, for $s>w/3$,
$$
 T_s\le C_w(s):=3^w e^{-s}\frac{s}{s-w/3}.
$$
Indeed $\log(1+2r)\le\log 3+(r^2-1)/3$ for $r\ge1$ by differentiation, and the integral is elementary. For example $s=2w$ gives $C_w(2w)=(6/5)3^w e^{-2w}$. The strict radius matters because the head pair always contributes $2e^{-s}$.

In fact $\mathbf1_{\{T_s\le C_w(s)\}}\to\mathbf1_{\{N=0\}}$ pointwise as $s\to\infty$. On a hit, a pair at radius $r<1$ contributes $2e^{s(1-r^2)}$ to $e^sT_s$, whereas $e^s C_w(s)\to3^w$. Thus even the probabilities converge by bounded convergence.

The mean at fixed $t$ is explicit:
$$
 \mathbb E T_{\pi t}
 =2\sum_{j=0}^{w-1}
 \frac{t^{-j/2}}{\prod_{i<j}a_i}
 \sum_{k=1}^\infty e^{-\pi t a_j^2 k^2}.
$$
Group by positive last nonzero coefficient $x_j=k$ and restore both signs. In row $i<j$, conditional on the suffix coefficients and the other shears in that row, $k\mu_{ij}$ is uniform modulo one. Summing over $x_i$ and integrating unfolds the row Gaussian to $1/(a_i\sqrt t)$. Eliminate rows in increasing order. The same strict-ball count gives the elementary comparison $\mathbb E T_s\ge 2e^{-s}E$, where $E=\mathbb E N$. Neither first moment controls the probability below $C_w(s)$. [Fixed-chart unfolding](wall1_mu_moments.md) · [Window means](wall1_window_asymptotics.md)

## Curvature on a single shear

Fix every shear at zero except $u=\mu_{01}\in[-1/2,1/2]$. With $D=\prod_{j=2}^{w-1}\sum_{n\in\mathbb Z} e^{-\pi t a_j^2 n^2}>0$, Poisson summation in the first integer coordinate gives
$$
 1+T_{\pi t}(u)=\frac D{\sqrt t}
 \sum_{n,h\in\mathbb Z}e^{-\pi(t a_1^2 n^2+h^2/t)}\cos(2\pi hnu).
$$
The Gaussian coefficients permit termwise differentiation of every order. More generally smoothness on the cube follows from a uniform positive lower bound on the least singular value of the normalized basis on a compact neighborhood, which gives Gaussian domination even after polynomial derivative factors.

The shear slice is even and one-periodic, and its value at zero strictly exceeds its value at $1/2$ because the odd $hn$ terms lose twice their positive weight. Its derivative vanishes at both ends of the full period $[-1/2,1/2]$. A differentiable convex or concave function there with equal endpoint derivatives is constant, by monotonicity of its derivative. This rules out convexity and concavity for both $T_{\pi t}$ and $\log T_{\pi t}$, the latter being smooth, periodic and nonconstant as well. It applies to geometric profiles at the requested widths without a limiting argument.

For fixed integer $x$, the exponent is a concave quadratic in the shears, possibly degenerate. Prékopa's marginal theorem requires joint log-concavity in the retained and integrated variables. The integer index has disconnected support and the products $u x_j$ are bilinear under a real relaxation. Replacing the integer sum by a Lebesgue integral would give $t^{-w/2}/\prod_j a_j$, independent of every shear. The nonconstant Fourier modes above certify exactly what that replacement loses.

Even abstract log-concavity would supply no uniform relative-to-mean lower tail of the suggested kind. For $U$ uniform on $[0,1]$ and $F=e^{-bU}$, the mean is $(1-e^{-b})/b$. At fixed $0<\epsilon<1$ and sufficiently large $b$,
$$
 \Pr(F\le\epsilon\mathbb EF)=1-b^{-1}\log\!\frac b{\epsilon(1-e^{-b})}\longrightarrow 1.
$$
Here $\log F$ is affine. An estimate would need quantitative structure beyond the sign of its curvature.

## Gaussian representation and the missing estimate

Take an independent centered two-dimensional Gaussian with covariance $(2s)^{-1}I$. Its radial tail is $\Pr(\|Z\|\ge r)=e^{-sr^2}$, so $T_s=\mathbb E_Z M(\|Z\|)$ at fixed shears. Each hit in this representation is the exterior of a disk in $Z$, and the events for different vectors are nested. Gaussian averaging here introduces no independent vector trials. The conditional event that all vectors miss is exactly $\|Z\|<\lambda_1(L)$, whose probability is $1-e^{-s\lambda_1(L)^2}$. Averaging this expression over shears requires the very minimum distribution under study.

In shear space a fixed-vector hit is an affine inverse image of an open ball. It can be displaced from the origin, its complement can be nonconvex, and the shear law is uniform on a cube. Royen's inequality lower-bounds intersections of centered symmetric convex Gaussian events. Even for two such hits $A,B$, subtracting the two marginal probabilities gives $\Pr(A^c\cap B^c)\ge\Pr(A^c)\Pr(B^c)$, the opposite direction to a void upper estimate. [Royen’s proof and theorem statement](https://arxiv.org/abs/1512.08776)

Below deterministic packing exclusion, this route proves no positive exponent growing with $E$, either for one window or for joint acceptance. A sufficient missing input would be an upper bound on $\Pr_\mu(T_s\le C_w(s))$ at some profile-dependent $s$, or on its limit. The exact mean and the pointwise limiting test give neither a rate nor a lower-tail estimate on the rank-1023 surviving domain. The twelve Part 71 boxes already have void probability zero by a separate packing certificate. [Packing certificate](wall1_dense_packing_ld.md) · [Joint window acceptance](wall1_joint_acceptance.md)
