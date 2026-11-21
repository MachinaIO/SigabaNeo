# Capture at intermediate depth

For arbitrary Euclidean lattices, the smallest width that forces capture or terminal success from ambient uniqueness alone is exactly $d$, for every $d\ge3$. The example below fails at **every** proper width in the same size-reduced basis. This is a worst-case statement. The minimum width for the specified planted distribution and the verified slide output remains open.

## What the prefix inequalities give

Index rows from zero, put $s=d-\beta$, and let $t$ be the last nonzero basis coefficient of the primitive plant $u$. Write $W_i$ for the span of the first $i$ rows and $\pi_i$ for projection off it. If $b_0\ne\pm u$ and every vector outside $\mathbb Zu$ exceeds $R$, Parts 6 and 7 give $g_i>R e^{-P_i}$ with $P_i$ nondecreasing. For $0\le k\le s$, suppose $\|u\|\le R e^{-P_k}$. If $t\le k$, projection at $t$ gives $\|u\|\ge |a_t|g_t>\|u\|$. Thus under the no-first-row-capture hypothesis the conclusion is **$t>k$**. In fact $t\ge\min(d,k+\beta)$: if $k<t<k+\beta$, then $\pi_k u$ belongs to the nonzero part of the tested block, whose minimum is $g_k>\|u\|$. Only at $k=s$ does this exhaust all possible indices and force first-row capture. For earlier $k$, the block omits later coefficients. This argument does not force equality of an ambient row with $u$.

## An integral example in every dimension

Use orthonormal coordinate vectors $e_0,\ldots,e_{d-1}$. In order, take
$$
 b_0=200e_0,\qquad b_i=100e_0+174e_i\ (1\le i\le d-2),\qquad
 b_{d-1}=-100e_0+87e_{d-2}+160e_{d-1}.
$$
Mark $u=b_0-b_{d-2}+b_{d-1}=-87e_{d-2}+160e_{d-1}$. Its squared norm is 33169, and no row equals $\pm u$. For $d=3$ the three displayed row types give the entire example. All Gram–Schmidt coefficients below the diagonal have absolute value at most $1/2$.

**Ambient gap.** Every vector outside $\mathbb Zu$ has norm at least 200. To check this, consider a vector of norm strictly below 200 and write $z$ for its last row coefficient. The last coordinate forces $|z|\le1$. If $z=0$, at most one middle coefficient can be nonzero, and it must then be $\pm1$. Its first coordinate has magnitude at least 100, giving squared norm at least $100^2+174^2>200^2$. With all middle coefficients zero only the zero vector qualifies. For $|z|=1$ negate as necessary to set $z=1$. Every middle coefficient except the one at $d-2$ vanishes since $174^2+160^2>200^2$. The remaining coefficient must be 0 or $-1$, since otherwise the penultimate coordinate has magnitude at least 261. In the former case the first coordinate has magnitude at least 100 and $100^2+87^2+160^2>200^2$. In the latter it must vanish, leaving exactly $u$. Thus one may take $R=199$.

**Block minima.** Fix any $2\le\beta<d$. The first block excludes the last row, so the ambient gap proof gives minimum 200, attained by $b_0$. At each middle index $i$, projection removes $e_0,\ldots,e_{i-1}$. The remaining middle rows are orthogonal of length 174. Even allowing the entire suffix, a combination using the last row has length at least 320 for $|z|\ge2$, and at least $\sqrt{87^2+160^2}>174$ for $|z|=1$, since its penultimate coordinate is an odd multiple of 87. Thus the first projected row attains the minimum at every middle index. The last block has rank one. These checks establish exact overlapping-block reducedness for every proper width.

**Terminal failure.** For every such width, $1\le s\le d-2$, so $\pi_s u=u$ while $\pi_s b_s=174e_s$ is strictly shorter and independent of $u$. In particular the failure is off the planted line and persists even when capture anywhere in the output counts. At width $d$ the first block is the whole lattice, so ambient uniqueness and primitivity force first-row capture.

## Interpretation for the plain planted calculation

The [Part 7 calculation](ratio_unique.md) certifies success with probability at least $1-2^{-63}$ at $\beta=d=701$ for the plain 512 shape with $m=188$. This also bounds the probability of the enlarged success event from below. The example explains why merely replacing first-row capture by capture anywhere cannot give a general uniqueness-only certificate at 406. It does not establish an optimal width for the prime-modulus plain embedding, or the probability of this obstruction under its selected-prefix law. In particular, an event forcing a larger quantitative gap than the example's gap can support stronger conclusions. None of the arguments assumes a GSA profile or transfers overlapping-block reducedness to slide reduction.
