# Fourier bounds for a void in the fixed-profile triangular chart

For a single window there is an explicit profile-only bound
\[
  -\log\Pr(N=0)\ \ge\ \log\!\left(1+\sum_{j=1}^{w-1} E_j^2/\overline V_j\right).
\]
Here $E_j$ is the full last-index mean, $E=\sum_j E_j$, and $\overline V_j$ is the mean **conditional translate variance**, given below by radial integrals with the reciprocal GS lengths. The formula includes all positive last coefficients and their correlations. A stronger exponential estimate on a fixed history follows by revealing independent torus phases. Its exponent involves Fourier coefficient sums on that history. Neither estimate here establishes a uniform power of $E$ on the surviving profiles.

## Translate count and its harmonics

Write the prefix matrix as $B=\operatorname{diag}(g_0,\ldots,g_{j-1})U$ with upper unitriangular $U$, prefix lattice $D=B\mathbb Z^j$, covolume $d=\prod_{i<j}g_i$, and $R=g_0$. The fresh column's horizontal part $x$ is Haar modulo $D$, since the GS box tiles by backward rounding. For each integer $1\le m<R/g_j$ take $s_m=(R^2-m^2g_j^2)^{1/2}$ and $h_m=\mathbf1_{B_j(s_m)}$ for the open Euclidean ball. Then the column count is
\[
 X(x)=\sum_m\sum_{v\in D}h_m(mx+v).
\]
One may also use radial smooth functions supported in the closed balls, strictly positive inside and zero on their boundaries. For instance use $\exp[-1/(1-|y|^2/s_m^2)]$ inside. The zero event is identical and its indicator equals $\lim_{t\to\infty}e^{-tX(x)}$. For smooth weights write $A$ for the resulting mean. With indicators $A=E_j=d^{-1}\sum_m V_j s_m^j$, where $V_j$ denotes unit ball volume.

Use Fourier characters $e^{2\pi i\langle\xi,x\rangle}$ and the negative sign for the Euclidean transform. Periodization and the substitution $x\mapsto mx$ give, for $\eta\in D^*$,
\[
 c_\eta=d^{-1}\sum_{m:\eta\in mD^*}\widehat h_m(\eta/m),\qquad
 c_0=A,\qquad V(D)=\operatorname{Var}_x X=\sum_{\eta\ne0}|c_\eta|^2 .
\]
Indeed integrating a character against one period unfolds the Euclidean transform. The indicator periodizations are bounded on each fixed torus, so the identity holds in $L^2$ and Parseval applies. Smooth weights give absolute convergence. For a single ball this is the usual sum of squared ball transforms. Distinct multiples can contribute to the same harmonic.

## Exact dual average

The following operator evaluates $\mathbb E_D\sum_{\xi\in D^*\setminus0}F(\xi)$ for radial $F$. In the formula $a_i=1/g_i$ and the argument of $F$ is written as a radius:
\[
 {\cal I}_j(F)=\sum_{i=0}^{j-1}\sum_{k\in\mathbb Z\setminus0}
 \frac{1}{\prod_{l>i}^{j-1}a_l}
 \int_{\mathbb R^{j-1-i}} F\!\left(\sqrt{k^2 a_i^2+|z|^2}\right) dz .
\]
Empty-dimensional integrals are evaluations. This holds for nonnegative measurable functions and for absolutely integrable signed terms under this operator. In particular $\Pr(\lambda_1(D^*)<u)\le {\cal I}_j(\mathbf1_{[0,u)})/2$ by sign symmetry. The integrals there are ordinary ball sections, with a strict cutoff at $|k|a_i<u$.

To prove it, solve $B^T\xi=n$ recursively, putting $y_l=g_l\xi_l$. The first nonzero integer entry $n_i=k$ forces $y_i=k$. For $l>i$ we have $y_l=n_l-\sum_{h<l}U_{hl}y_h$. Given earlier columns, the fresh term $kU_{il}$ is uniform modulo one, independently of the other fresh entries. Summing $n_l$ and averaging unfolds $y_l$ with Lebesgue density. Unfold from the last coordinate backwards and rescale to physical coordinates $a_l y_l$. This proof uses no independence assumption on the entries of the inverse triangular matrix. It also explains the reversed reciprocal GS profile upon reversing the axes.

For $m,n$ in the column sum set $L=\operatorname{lcm}(m,n)$. The intersection $mD^*\cap nD^*=LD^*$ gives the explicit variance
\[
 \overline V_j=d^{-2}\sum_{m,n}{\cal I}_j\!\left(
 \widehat h_m((L/m)\,\cdot)\,\overline{\widehat h_n((L/n)\,\cdot)}
 \right).
\]
The diagonal terms are finite even for indicators. For fixed profile the GS recursion bounds the number of lifts in any translate uniformly over histories, so the single-section second moments are finite. Cauchy–Schwarz then bounds the absolute cross terms. This computation gives the **unconditioned** dual intensity.

## Successive conditioning

Let $p_j$ be the probability of passing all columns before $j$, so $p_1=1$. On each history, Cauchy–Schwarz applied to $X\mathbf1_{X>0}$ bounds the miss probability by $V(D)/(V(D)+A^2)$. This fraction is increasing and concave in the variance. Given previous survival the average variance is at most $\overline V_j/p_j$, by nonnegativity. Hence, if $p_j,A,\overline V_j>0$,
\[
 p_{j+1}\le\frac{p_j\overline V_j}{\overline V_j+p_j A^2},
 \qquad
 p_{j+1}^{-1}\ge p_j^{-1}+A^2/\overline V_j .
\]
This proves the opening bound using indicators. A column with zero mean is skipped, and positive mean with zero variance forces failure. One can use the largest $A^2/\overline V_j$ from several weights at each column. Disjoint windows at fixed profile use independent entries, so their log penalties add. For overlapping windows one can bound their intersection by any disjoint subcollection. Simply adding unconditional log penalties for overlapping windows has no such justification.

## A one-sided exponential estimate on each history

For smooth weights let $x=B t$ with $t$ Haar on the product of unit circles. Group $c_{B^{-T}n}$ by the last nonzero coordinate $l$ of $n$, and let $b_l$ be the sum of absolute coefficients in that group. Revealing $t_0,\ldots,t_l$ successively yields martingale differences equal to the grouped real Fourier sums. Conditional on earlier coordinates each has mean zero and lies in $[-b_l,b_l]$. Convexity bounds its conditional exponential moment at $-t$ by $\cosh(tb_l)\le\exp(t^2 b_l^2/2)$. Iterating and optimizing $t$ gives
\[
 \Pr_x(X=0\mid D)\le \exp[-A^2/(2\sum_l b_l^2)] .
\]
If $\sum_l b_l<A$, the miss probability is zero by uniform Fourier inversion. Both criteria allow any order of the independent phases. A positive deterministic lower bound $f_j$ for the exponential penalty on all passing histories would add across columns by the tower property. If it holds except on histories of unconditional probability $\delta_j$, the valid recursion is $p_{j+1}\le e^{-f_j}p_j+(1-e^{-f_j})\delta_j$. Thus a polynomial exceptional probability can dominate an exponentially small target.

There is a limitation intrinsic to this particular martingale estimate. Whenever a hole exists, $A\le\sum_l b_l$, hence $A^2/(2\sum_l b_l^2)\le j/2$. No improvement in the short-dual-vector estimate alone removes this ceiling. Across a disjoint family of windows of total rank 1023 and widths at most 800, the sum of these finite exponents is at most $1023\cdot799/4<205000$. This ceiling concerns the displayed martingale formula on histories admitting holes. It does not constrain exact coverage or the true void exponent.

## Why Gaussian smoothing and short-vector counts leave a gap

A periodized Gaussian has strictly positive nonconstant Fourier coefficients and is positive everywhere. Its log cannot be concave on all translates: a periodic concave function restricted to any lattice-period line is constant there, which would force constancy in all basis directions. Moreover its zero set is empty even when a ball has holes. A Gaussian approach would need a comparison of two levels, for example on a radius-$s$ hole one has $\sum_v e^{-t|x+v|^2}\le e^{-(t-u)s^2}\sum_v e^{-u|x+v|^2}$ for $0<u<t$. The comparison requires quantitative control of the two theta sums.

Even a large section mean and an exact shortest dual length leave the translates sensitive to shape. In dimension two, take $D=h\mathbb Z\times H\mathbb Z$ and $0<h<H$, $0<2s<H$. The section has mean $\pi s^2/(hH)$ and misses with probability at least $1-2s/H$, since an entire band of vertical phases cannot hit. As $h\downarrow0$ the mean diverges and the dual minimum stays $1/H$. This illustrates the fixed-torus obstruction only. Such a prefix with $h<R$ fails the preceding shortest-vector test and gives no counterexample on surviving profiles.

The reciprocal bound computes a profile-dependent penalty; even variance of order $E_j$ would produce only a logarithm of the summed means by this argument. A power-law exponent would require, for example, a much sharper one-sided estimate exploiting cancellation within the groups on surviving histories, with exceptional histories controlled at the scale of the void. The dual first moment above does not supply that conditional estimate. No new rank-1023 suppression or terminal radius is certified here. The twelve earlier witness boxes already have exact zero acceptance by the separate packing certificate. [Part 70](wall1_window_asymptotics.md) · [Part 72](wall1_mu_moments.md) · [Packing certificate](wall1_dense_packing_ld.md)
