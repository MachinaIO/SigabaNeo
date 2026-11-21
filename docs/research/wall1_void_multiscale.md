# Short lifts across consecutive block boundaries

A cut with many nonparallel suffixes admits a logarithmic void exponent from pairwise independence, even when its rational rank is two. Consecutive cuts can accumulate these exponents if each new block lifts directly into the whole preceding prefix. The resulting bound depends on the profile. The full-window mean alone has not been shown to supply the required exponents.

## The torus law and its sharp limitation

Write the upper triangular GS matrix across a cut as $[A,C;0,H]$, with prefix dimension $t$ and suffix dimension $s$. Conditional on $A,H$, the columns of $C$ modulo $D=A\mathbb Z^t$ are independent Haar points $X_1,\ldots,X_s$ of $T=\mathbb R^t/D$. The centered GS box is a fundamental region by backward rounding. For a list of integer suffixes (rows of $V$), the horizontal displacements have law $VX$ on $T^k$. Its support is the connected image subgroup of dimension $t\operatorname{rank}V$. In Smith coordinates, unimodular changes preserve Haar and every nonzero Smith factor acts surjectively on $T$. Thus the image has normalized Haar law, and its ambient Haar measure is zero at deficient row rank and one at full row rank. A row-lattice index does not give an ambient mass of $1/I$. [Part 60](wall1_poisson_smallball.md)

For each nonzero suffix $v$ with $\|Hv\|<R=g_0$, let $p_v$ be the normalized measure of the projected open ball of radius $\sqrt{R^2-\|Hv\|^2}$ in $T$. For any finite list with no proportional pair, the lift indicators are pairwise independent, since every two-row submatrix maps onto $T^2$. If any $p_v=1$, survival has probability zero. Otherwise put $J=\sum_v p_v/(1-p_v)$. Then

$$\Pr(\text{no lift from the list}\mid A,H)\le (1+J)^{-1}.$$

Indeed, weight each hit by $1/(1-p_v)$. The weighted sum has mean and variance both equal to $J$. Cauchy–Schwarz on its nonzero set gives hit probability at least $J/(1+J)$ (the empty case is immediate). Along each rational line it suffices for this bound to take a primitive representative, which maximizes the projected radius. The argument gives credit to all lines, even when they vastly outnumber the columns.

**Sharp order for unrestricted row lists.** Take $T=\mathbb R/\mathbb Z$, ball $(-1/8,1/8)$, and rows $(1,j)$ for $0\le j<k$, $k\ge2$. The rows are primitive, pairwise nonparallel and span $\mathbb Z^2$. For independent Haar $X,Y$, on $X\in[3/8,5/8]$ and $\|Y\|_{\mathbb T}<1/(8k)$ every $X+jY$ misses. The void probability is therefore between $1/(16k)$ and $1/(1+k/3)$. Even saturated rank two and equal positive target measures permit only a logarithmic universal exponent in the hit mean. This is a counterexample for row lists. A short-vector ellipsoid also contains other rows and their target radii vary, so it does not give a lower bound for the full lattice void probability.

## Sequential prefix lifts

Partition the columns into consecutive blocks of size $s$ (a shorter final block is allowed). Reveal whole columns left to right, one block at a time. At the start $t>0$ of each block the entire previous prefix $A$ is known. Reveal the new diagonal block $H$ first. The rectangle $C$ of new columns against **all** preceding rows is still fresh, including conditional on the prefix surviving. A successful lift padded with trailing zeroes is a genuine full-window competitor. A short vector constructed only in an interior projected block has no such implication.

Here is an explicit deterministic product bound. For each cut choose $0<a<R$. Set $b=\sqrt{R^2-a^2}$ and

$$q_t(b)=\Pr\{\textstyle\sum_{i<t}g_i^2 U_i^2<b^2\},\qquad U_i\ \text{independent uniform on }[-1/2,1/2].$$

Every suffix of norm at most $a$ has $p_v\ge q_t(b)$ by restricting to the prefix GS box. Let $L(H,a)$ count rational lines with a nonzero such suffix. With $h$ the new block size, $m=\min_{t\le i<t+h}g_i$, $\Delta=\prod_{t\le i<t+h}g_i$, and $V_h$ the unit ball volume, a deterministic lower bound when $a\ge m$ is

$$L_* = \left\lceil\frac{\lceil V_h(a/2)^h/\Delta\rceil-1}{2\lfloor a/m\rfloor}\right\rceil.$$

Use zero when $a<m$. Indeed, the average number of lattice points in a translate of the open $a/2$ ball equals volume divided by determinant, by integration over a fundamental region. Some translate attains at least the ceiling. Subtraction of one of its points gives distinct differences of norm below $a$. Each line contains at most $2\lfloor a/m\rfloor$ nonzero differences since the last nonzero coefficient gives length at least $m$. This estimate can be replaced by exact line counting in the small revealed block.

In particular define

$$F_t(a)=-\log\mathbb E_H\!\left[\left(1+L(H,a)\,q_t(b)/(1-q_t(b))\right)^{-1}\right].$$

At $q_t=1$ the integrand is the indicator of an empty list. Replacing $L$ by $L_*$ gives an elementary lower bound for $F_t$. Conditional on any surviving prefix the next survival probability is at most $e^{-F_t(a)}$, because $H$ has its original law and the bound on the target measure is uniform in $A$. Iterating conditional probabilities yields

$$\Pr(N=0)\le \exp\!\left(-\sum_{t>0}\sup_{0<a<R} F_t(a)\right),$$

where the sum is over starts in the partition. Dropping the first block's survival factor only weakens the bound. One can maximize over partitions. This ordering counts each fresh rectangle once and charges each success at the first prefix where its chosen witness is available. In particular the product does not assume independent survival events. For joint window acceptance one may multiply the resulting bounds on windows with disjoint coefficient sets, or apply any one window's bound to the joint event.

## What the exponent measures

The proved exponent is a sum of logarithms of inverse conditional miss bounds. The expectation inside each logarithm is essential: a large mean line count need not suppress the histories with few lines. Moreover $E$ counts every lift with multiplicity, whereas $L$ counts directions and $q_t$ only certifies a portion of a projected ball. Splitting into smaller blocks further restricts the available suffix directions at each test. No comparison between this sum and a growing function of the Part 70 mean on the remaining profiles has been established. In particular neither $10^{-49}E$ nor $E^{0.11}$ follows. The rank-two example locates the missing ingredient even with fixed list size: an improvement beyond logarithmic cost per cut must use more of the actual ellipsoid or its varying radii. The twelve Part 71 boxes already have zero acceptance by deterministic packing. [Window mean](wall1_window_asymptotics.md) · [Moment obstruction](wall1_mu_moments.md) · [Box exclusions](wall1_dense_packing_ld.md)
