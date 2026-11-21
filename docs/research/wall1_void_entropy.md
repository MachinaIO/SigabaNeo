# Entropy bounds for the fixed-profile void

Fix positive GS lengths, use upper triangular coordinates, and give the coefficient cube product uniform probability. Let $R=g_0$, let $N$ count sign pairs strictly inside radius $R$, and write $E=\mathbb E N$. The void $V$ includes ties. The two results below delimit the information in row projections and individual window volumes. Neither yields a growing single-window exponent on the remaining large-mean profiles.

## Proper row projections can lose the entire exponent

In any width $w\ge3$, take $g_0=\cdots=g_{w-2}=1$ and $g_{w-1}=r$ with $\sqrt{3}/2<r<1$. Put $s=\sqrt{1-r^2}$. The exact forbidden set is the cylinder
$$
 \sum_{i<w-1}\mu_{i,w-1}^2<s^2.
$$
Indeed, the last nonzero integer coefficient must be in the final column, by the height bound, and must equal one after sign selection. Every horizontal residual must have magnitude less than $s<1/2$. Starting immediately above the last row, once all intervening integer coefficients vanish the residual is an integer plus a centered last-column coefficient. Only the zero integer can work. This proves the claim by induction. Thus $E=\kappa_{w-1}s^{w-1}$, where $\kappa_d$ is unit ball volume, and the exact exponent is $-\log(1-E)$.

Project away **any** nonempty subset of the $w-1$ variable rows. Every remaining point extends to the void by choosing one omitted last-column entry in $(s,1/2)$. Hence even knowing the exact volumes of *all* proper row projections supplies zero exponent through Loomis–Whitney. The void also contains an open box, so its points cannot have positive mutual separation in any metric compatible with the chart topology. This example isolates a loss in the proposed statistic at small mean. It gives no counterexample to exponential decay at large mean.

## Interval windows and the best fractional product

Let $I=[a,b]$ be an inclusive interval with $a<b$. Its projected shortest-vector test uses only $S_I=\{(k,l):a\le k<l\le b\}$. Write $p_I$ for its pass probability at the specified profile, and $W$ for the probability that every listed test passes. The same reasoning applies to local joint tests with these declared supports. Fractional Hölder gives
$$
 -\log W\ \ge\ \sum_I t_I(-\log p_I),\qquad
 t_I\ge0,\quad \sum_{I:(k,l)\in S_I}t_I\le1 .
$$
Indeed, integrate one independent coordinate at a time, applying Hölder to the incident powered indicators with exponents $1/t_I$ and filling unused weight with the constant one. Subsequent steps act on the corresponding conditional integrals raised to the same weights. Zero weights can be discarded, and a zero pass probability already forces $W=0$. This is the indicator case of [Finner's product-space inequality](https://doi.org/10.1214/aop/1176989534).

**The optimized right side equals the maximum sum of costs over windows with disjoint adjacent edges.** Only the constraints for $(k,k+1)$ matter, since every window containing $(k,l)$ also contains $(k,k+1)$. The support on edges is the interval $[a,b)$. For a rational feasible vector $t$ with denominator $q$, take $qt_I$ copies of each interval. In order of increasing left endpoint, color each copy with one of $q$ colors, reusing a color when its preceding interval has ended. Every unavailable color occupies the current left edge, so the depth bound guarantees a color. The fractional cost is the average of the $q$ color-class costs. One class attains at least that average. Approximating weights from below gives the result for real weights, and the indicator weights of a maximizing class are feasible. Windows may share an endpoint vertex. Their coefficient sets are still disjoint.

For equal width $w$ and common marginal $p$ on all full windows of a length-$n$ geometric profile, the resulting exponent is exactly $\lfloor(n-1)/(w-1)\rfloor(-\log p)$. At $n=1023$ the multipliers for widths 406, 506, 647 and 800 are respectively 2, 2, 1 and 1. This optimality concerns the fractional product from the stated supports and marginals. A genuinely joint local probability can give a larger cost, as the width-three transfer integral illustrates. An interior projected window also tests a different radius and discards earlier coordinates, so its acceptance cannot in general be imposed as a necessary condition for a *single* head void. [Joint window acceptance](wall1_joint_acceptance.md)

## Grid counts and tube multiplicity

For a finite grid bound define $M_i=\lceil R/g_i+\tfrac12\sum_{j>i}M_j\rceil$ backwards. Every strict competitor everywhere in the cube has $|x_i|\le M_i$, by triangular substitution. Write $X$ for this finite box after omitting zero and selecting signs. For $x\in X$, the function $h_x(\mu)=\|B(g,\mu)x\|$ has sup-norm Lipschitz constant at most
$$
 L_x=\left(\sum_i g_i^2\left(\sum_{j>i}|x_j|\right)^2\right)^{1/2}.
$$
Partition each cube edge into $m$ equal parts. Count a center $c$ if $h_x(c)\ge R-L_x/(2m)$ for every $x\in X$. The fraction counted upper bounds the void volume: every cell meeting the void passes. These upper bounds converge to the volume as $m\to\infty$. At each point outside the void a fixed strict competitor eventually rejects the containing cell; bounded convergence applies. This is a deterministic certification procedure. Counting distinct forbidden-vector lists supplies no saving by itself: the list of actual hits is empty throughout every void cell, however many cells that list occupies.

For $T_x=\{h_x<R\}$, the known sum of tube volumes is the integral of their multiplicity $N$. If a positive-probability hit is possible, the exact relation is $1-|V|=E/\mathbb E[N\mid N>0]$. Isoperimetry of a torus controls expansion of a given union; the sum of the constituent measures does not specify the starting union measure. Even nested tubes occur here since $T_{kx}\subseteq T_x$ for positive integers $k$. An argument based on independent random translations would require an additional law for the placements. The iid chart coordinates sample a point in these fixed tubes.

## Conditional volumes and the missing estimate

For a single head, reveal columns from left to right. On survival up to column $j-1$, let $u_j(H)$ be the fraction of fresh shifts avoiding all competitors ending at $j$ for that prefix history $H$. Put $a_j=\mathbb E[u_j(H)\mid\text{prefix survives}]$. Then $|V|=\prod_{j=1}^{w-1}a_j$, with the recursion stopping at zero. For joint windows the same identity holds using all starts tested at the reveal. Part 68 bounds these *fibers*, with histories in column order. A projection instead asks whether there exists a completion. The distinction persists even when the whole collection of proper projections is known, as the cylinder example proves. [Conditional coverage](wall1_covering_fraction.md)

A sufficient missing estimate for a rate $f(E)$ is $\sum_j-\log a_j\ge f(E)$ on the profiles of interest. It requires coverage on the distribution of surviving prefixes, or another bound on their joint volume. Part 70 computes the unrestricted mean and Part 72 describes its multiplicities. Neither provides that conditional coverage estimate. The projection and grid arguments above give no new large-mean $f(E)$ below deterministic exclusion. On the twelve Part 71 witness boxes a particular window already has zero void volume by the separate packing certificate; those boxes cannot validate a finite-rate extrapolation to the remaining domain. [Geometric means](wall1_window_asymptotics.md) · [Fixed-chart moments](wall1_mu_moments.md) · [Packing certificate](wall1_dense_packing_ld.md)
