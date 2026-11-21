# Kelmer's shear average at the head radius

On every relocated Part 82 box, the explicit volume-centered estimate derived below gives **zero nats** in every window. Recentring the same estimate at the exact mean gives a positive finite formula, but even its optimistic disjoint-window budget is **below 0.064 nat** at rank 1023. These are limitations of the explicit majorant. They are not lower bounds on the true void probability.

## The measure and the endpoint

In Theorem 1, fix a real invertible row basis matrix $g$ in dimension $d$. For the indicator of the centered Euclidean ball of radius $T$, let $K$ count all points of $\mathbb Z^d u g$, including zero, and $V=\kappa_d T^d/|\det g|$, with $\kappa_d$ the unit-ball volume. The paper bounds $\int(K-V)^2 du$ by $c(g)T^{d-1}\log^2 T$. Integration is over $U_d(\mathbb Z)\backslash U_d(\mathbb R)$ with unit-mass Lebesgue measure in the strictly upper entries. The slicing proof uses strict inequalities. The statement prints $T\ge1$. Literally no such constant exists there: for $g=3I$ in dimension two, $K=1$ at $T=1$ for every shear (look at the first nonzero integer coordinate), while $V=\pi/9$. Below we prove the large-radius statement for every $T\ge2$. One may rescale the entire input to make the head radius 2. [Kelmer, Theorem 1, §§2–4](https://arxiv.org/pdf/1512.06012)

In the factorization $g=u_0 a k$ with $a$ positive diagonal and $k$ orthogonal, right translation by $u_0$ preserves quotient measure and $k$ preserves the ball. Thus only the ordered diagonal matters. Transposing the repository's upper triangular column matrix and reversing both indices gives the row model with $a_i=g_{d-i}$ for $1\le i\le d$ (here $g_j$ denotes a GS length). For the left quotient, reduce each row by later rows, visiting columns from left to right within the row. The pivot one gives a unique centered representative in each entry, up to boundary choices. The coordinate Jacobian of unipotent translation is one by triangularity. Hence iid uniform centered entries give precisely this law, although for $d\ge3$ the quotient is a nilmanifold. This identification applies at fixed profile before shortest-vector conditioning.

## An effective constant

Here is one explicit majorant obtainable by Kelmer's slicing and Fourier argument. We give constants because treating the theorem's implied constant as one gives a different numerical conclusion. Use empty products equal to one. For $1\le i\le d$ put $q=d-i+1$, $s=(q+1)/2$, $P_i=\prod_{h=i}^d a_h$, and set
$$
 B_q=1+\kappa_q+\exp(q^2),\qquad
 D_i=B_q a_i^s/P_i,\qquad Q_i(T)=\prod_{h<i}(1+2T/a_h).
$$
Define $Z_i=1$ if $q=1$, and $Z_i=2D_i(1+1/(s-1))$ otherwise. Set
$$
 L(T)=\sum_{i=1}^d T^{(q_i-1)/2}
       (Z_i+\sqrt{128 Q_i(T)}D_i),\qquad q_i=d-i+1.
$$
Then $\|K-V\|_2\le L(T)$. In particular a constant in Theorem 1 for $T\ge2$ is
$$
 c(a)=(\log2)^{-2}\left[\sum_i(Z_i+D_i\sqrt{128 Q_i(1)})\right]^2.
$$
Indeed $Q_i(T)\le T^{i-1}Q_i(1)$ for $T\ge1$. This version even omits the large-radius logarithmic loss before conversion to Kelmer's normalization.

**Proof.** Integrate out successive last physical coordinates of the ball, dividing by their mesh lengths. Telescope the resulting weighted prefix counts from dimension $d$ down to zero. At step $i$ a fixed integer prefix $n$ of length $i-1$ and physical norm $<T$ leaves radius $r=(T^2-|n u' a'|^2)^{1/2}$. Its slice is the periodization, in phase $n\cdot x$, of the function $\kappa_{q-1}(r^2-y^2)^{(q-1)/2}/P_{i+1}$ on $|y|<r$ with mesh $a_i$; $x$ is the fresh uniform column. The constant Fourier coefficient gives exactly the next weighted prefix count. The empty prefix at the end gives $V$. This is also a deterministic telescoping identity before estimating its summands.

For nonzero Fourier mode $l$, the coefficient is the Fourier transform of the $q$-ball at $|l|/a_i$, divided by $P_i$. Its absolute value is at most $D_i r^{(q-1)/2}|l|^{-s}$. Indeed with frequency $t>0$ in cycles per unit length the radial transform is $(r/t)^{q/2}J_{q/2}(2\pi rt)$ (integrate the one-dimensional ball section using the Bessel integral). For $2\pi rt<1$ use the ball volume. For $z\ge1$ put $y=\sqrt z J_{q/2}(z)$ and $H=y^2+(y')^2$. Bessel's equation gives $|H'|\le |q^2-1|H/(4z^2)$; the fixed-order large-argument asymptotics of $J_\nu$ and $J_\nu'=(J_{\nu-1}-J_{\nu+1})/2$ give $H(\infty)=2/\pi$. Integration proves the asserted bound with the displayed $B_q$. The zero prefix has phase zero and contributes discrepancy at most $Z_i T^{(q-1)/2}$ by absolute summation for $s>1$. For $s=1$ an open interval's integer count differs from its length by at most one, including at an integral endpoint.

Condition on the old columns. For nonzero $n$, nonconstant characters have frequencies $ln$ in the fresh uniform torus. Different primitive lines are orthogonal. On a primitive line there are $M$ positive multiples and their negatives in the prefix ball. For positive multiples $m,h$, the summed absolute products over coincident frequencies, after dividing by $D_i^2 T^{q-1}$, are at most $2\zeta(2)\gcd(m,h)^2/(mh)$, using $s\ge1$. The two signs of the prefixes cost at most another factor four. Writing $(m,h)=b(j,k)$ with coprime $j,k$ gives
$$
 \sum_{m,h\le M}\frac{\gcd(m,h)^2}{mh}
 \le 2M\sum_{k\ge1}H_k/k^2 <8M ,
$$
where $H_k\le1+\log k$ and integral comparison bounds the sum by 3. Fourier orthogonality is valid in $L^2$ even for the interval. Summing over lines costs at most $128 Q_i(T)$ in squared normalized units: coordinate-by-coordinate enumeration gives at most $Q_i(T)$ prefixes, since each next integer lies in an interval of length at most $2T/a_h$. Taking norms and adding the zero-prefix bounds proves the claim. The large $B_q$ trades numerical sharpness for a uniform elementary constant.

## Evaluation on the twelve boxes

Take $T=a_d$, the head, after common scaling. For the strict ball, $K=1+2N$. Thus direct application gives $p\le\min(1,L(T)^2/(V-1)^2)$ when $V\ne1$. For $V=1$ it gives 1. The following bounds evaluate this expression simultaneously for every start and every admissible width on each box. Every prefix of rank $j$ in repository order satisfies the Part 82 cap, hence its radius-$T$ volume divided by its determinant is at most $2^j$ (the certified packing density bound is at most one, also at rank one). This uses the checked profile inequalities and requires no realization by a surviving lattice. In particular $V\le2^d$. Also $Q_d(T)\ge 2^{d-1}V/\kappa_d$. Since $\kappa_d\le6$ by the two-step volume recurrence and its initial values through dimension seven, $128Q_d(T)\ge V^2$. For $V<1$ use $Q_d(T)\ge1$. The last summand of $L(T)^2$ alone dominates $(V-1)^2$ since $D_d=B_1>1$. The clipped probability therefore equals **one exactly**, including on any disjoint schedule. The same argument works at any smaller radius using $a_d\ge T$ in the bound on $Q_d$.

**Recentring.** With $E=\mathbb E N$, $4\operatorname{Var}N=\mathbb E(K-V)^2-(1+2E-V)^2$. One may either retain this known bias subtraction or bound the variance directly by the squared norm of the sum of the nonzero-prefix terms. The zero-prefix terms in the telescope are deterministic. Hence $4\operatorname{Var}N\le U=(\sum_i T^{(q_i-1)/2}D_i\sqrt{128Q_i(T)})^2$. The bias-subtracted $L^2$ bound is at least $U$ since the absolute bias is bounded by the sum of the zero-prefix majorants. Cauchy–Schwarz against the hit indicator gives the explicit certified exponent $F=\log(1+4E^2/U)$, with $E$ the exact section sum in V2. This estimate is usually extremely loose.

Here are outward enclosures even without evaluating the Bessel constants numerically. For each signed suffix there are at most two first-coordinate lifts at the head radius, so $E\le Q_d(T)$. Also the V2 positive-height section sum in prefix dimension $j$ is at most half the normalized $(j+1)$-ball volume there, by bounding a decreasing positive grid sum by its integral. Consequently $E\le\sum_{j=1}^{d-1}2^j=2^d-2$. Thus $4E^2/U\le E/32$ and $0\le F\le d\log2$. A disjoint family costs at most $1023\log2<710$. The following intervals enclose $F$ per full window; the disjoint bound also allows all shorter windows. The last columns give lower bounds on the remaining Part 82 log residual at quarter, half and 0.85 GSA even after granting the entire disjoint ceiling as an extra penalty.

| Width | Per-window nats | Disjoint nats | Quarter | Half | 0.85 |
|---:|---:|---:|---:|---:|---:|
|406|[0,282]|[0,710]|794939|809772|812172|
|506|[0,351]|[0,710]|558159|575096|579515|
|647|[0,449]|[0,710]|359949|374865|379768|
|800|[0,555]|[0,710]|217292|234275|240490|

Integer interval certificate: $0.693147<\log2<0.693148$ follows by summing $2\sum_{k=0}^{7}3^{-2k-1}/(2k+1)$ and bounding the omitted terms by $2(9/8)3^{-17}/17$. Multiply the upper rational endpoint by each width or by 1023 and round up. Subtract 710 from the directed lower endpoints of the Part 82 table. The extra penalty is an optimistic budget comparison, without any independence assumption between existing charges and new tests. The direct volume-centered estimate leaves those endpoints unchanged. [Part 82, Surviving mass and coverage](wall1_small_d_caps.md)

**Sharpening with the actual box slope.** The Part 82 certificate checks every adjacent center drop is at most 0.055 in log length. Allowing its two endpoint errors gives $g_j/T\ge\exp(-0.055002j)$ in every subwindow at its head radius (centering cancels). Match the mean $E_j$ from column $j\ge1$ to the term $i=d-j$, $q=j+1$ in $\sqrt U$. The grid integral above gives $2E_j\le\kappa_q T^q/P_i$. Dividing by the corresponding term gives at most
$$
 \frac{\kappa_q}{\sqrt{128}B_q}(T/g_j)^{(q+1)/2}
 \le \frac6{\sqrt{128}}\exp(-0.972 q^2).
$$
Here $j(q+1)=q^2-1$. Sum before squaring. Since $q\ge2$ and $\log(1+x)\le x$, every nontrivial window on every box has $0\le F\le (36/128)e^{-7.776}<1/8000$ nat. The last rational comparison follows by lower bounding $e^{7.776}$ by its degree-16 Taylor polynomial at $972/125$. At most 511 disjoint windows have rank at least two. Their total is in **$[0,511/8000]$ nats**, including all mixed-width schedules. For full-width windows only, the four upper endpoints are respectively $2/8000,2/8000,1/8000,1/8000$. Thus the sharper remaining log residual for each of the twelve entries is its Part 82 value minus at most $511/8000$; in particular the closest exceeds **218001.936 nats**. This tiny upper endpoint comes from the deliberately conservative explicit Fourier constant. It says nothing about what an optimal variance calculation would give.

## What can be charged on a column chain

Kelmer averages an entire window. Disjoint windows are independent at fixed profile. On overlapping windows an unconditional upper bound gives no new multiplicative factor after conditioning on survival. Thus the direct estimate adds exactly zero along a chain as well. There is a sharper comparison than counting hypothetical independent copies. Let $A_j$ and $v_j$ be the exact mean and variance of the positive-height count in column $j$. Its conditional mean given the prefix is deterministic, so the full variance is $\sum_j v_j$. Even an exact variance in the recentered whole-window inequality can give at most
$$
 \log\left(1+\frac{(\sum_j A_j)^2}{\sum_j v_j}\right)
 \le \log\left(1+\sum_j A_j^2/v_j\right).
$$
This is weighted Cauchy–Schwarz; omit zero-mean terms and interpret a positive mean at zero variance as deterministic success. The right side is already V5's reciprocal recursion, valid along the column chain without independence. The raw volume-centered Markov ratio cannot improve exact Cantelli either: minimizing $\mathbb E(K-t)^2/(1-t)^2$ over centers $t$ gives the Cantelli bound. Thus even perfect constant extraction for this use of Theorem 1 gives no new exponent over exact V5. V2 uses a within-column triangle inequality and a sharp variance could improve that relaxation; no pointwise ordering of the two *upper variance estimates* is needed or established. [V2](wall1_void_affine.md) · [V5](wall1_void_fourier.md)

Kelmer's induction smooths ball sections as it lowers dimension. It never increases the moment order. In higher even powers the torus integral retains all additive frequency relations, including relations among different primitive lines. Squaring the second-moment bound repeatedly does not estimate those integrals. With variance equal to $E$, Cantelli gives $1/(1+E)$, attained for integer $E$ by a count supported on $0,E+1$ with that void mass. This example establishes the logical limit of two moments, not a lattice counterexample. Smaller variance or a higher-moment estimate on surviving histories could give more. No such estimate follows here. The numbers above concern the relaxed upper-bound integral only; the actual acceptance on the relocated boxes remains open.
