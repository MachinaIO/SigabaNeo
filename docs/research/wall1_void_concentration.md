# Concentration on the triangular coefficient cube

The global bounded-difference and log-Sobolev estimates for the smoothed count can have exponents tending to zero even when the mean tends to infinity on the Part 70 geometric family. There is a different, one-sided estimate obtained by revealing all rows except the first. Grouping suffixes by rational line gives a conditional void exponent of at least log one plus the sum of their hit probabilities. This estimate can use arbitrarily many lines in a fixed suffix rank of at least two. Turning it into an exponent growing with the *unconditional* mean requires control of the lower rows.

## Cutoff and row influences

Use physical row coordinates $g_i y_i$, where $y_i=x_i+\sum_{j>i}\mu_{ij}x_j$, and set $R=g_0$, $r_x=\|Bx\|/R$. Sum over sign representatives with positive last coefficient. Take a smooth nonincreasing $0\le\phi\le1$, equal to one up to $1-\sigma$ and zero from 1 onwards, with $|\phi'|\le K/\sigma$ for an absolute $K$. Write $F=\sum_x\phi(r_x)$, $M=\mathbb EF$, and $E=\mathbb EN$. Then $N=0$ implies $F=0$. For $0<s\le1$ define
$$
H(s)=\sum_{j=1}^{w-1}\frac{V_j}{\prod_{i<j}g_i}
\sum_{m\ge1}((sR)^2-m^2g_j^2)_+^{j/2}.
$$
Unfolding one column gives $H(1)=E$ and $H(1-\sigma)\le M\le E$. Continuity permits choosing $0<\sigma<1/2$ with $M\ge3E/4$ for each profile of positive mean. This treats the requested threshold $E/2$ with a positive deviation $t=M-E/2$. All estimates below for the void itself can take $t=M$. [Exact first moment](wall1_window_asymptotics.md)

Define $b_i=R/g_i+\tfrac12\sum_{j>i}b_j$ backwards. Only the finite integer box $|x_i|\le b_i$ can contribute anywhere, by back substitution. Let $A_i$ be its sign representatives with endpoint $>i$. For row replacement by any other allowed row, a single summand changes by at most $\min(1,K g_i\sum_{j>i}|x_j|/(R\sigma))$, by the reverse triangle inequality. Thus a valid row oscillation bound $c_i$ is the sum of these quantities over $A_i$. The mean *absolute* row change under independent resampling is at most twice the expected smoothed count with endpoint $>i$ by nonnegativity. In particular the first row gets no endpoint discount. To control its squared change one needs the simultaneous movements of the lifts.

Writing $D_i=F(\mu)-F(\mu^{(i)})$ for independent row replacement and $V=\frac12\sum_i\mathbb E D_i^2$, McDiarmid and Efron–Stein followed by Cantelli give respectively
$$
\Pr(F\le M-t)\le \exp(-2t^2/\sum_i c_i^2),
\qquad
\Pr(F\le M-t)\le V/(V+t^2).
$$
Both are finite profile formulas (zero variance is interpreted directly). For $V$ one can use $\mathbb E D_i^2\le c_i\mathbb E|D_i|$. The exact resampling variance proxy may be much smaller, and the range obstruction below gives no lower bound on it. Talagrand's witness argument for counts would need a bound on how many hits one changed row can invalidate. Endpoint support supplies only $|A_i|$. Even a single accepted long-endpoint vector generally involves every earlier row.

Where $\phi'$ is nonzero the coordinate derivative is
$$
\partial_{ij} F=\sum_{x\in A_i}\phi'(r_x)\frac{g_i^2 y_i x_j}{R^2r_x}.
$$
Set $L=\sup\|\nabla F\|_2$. One explicit upper bound is the Euclidean norm over $i<j$ of $K g_i\sum_{x\in A_i}|x_j|/(R\sigma)$. Tensorizing the unit interval inequality $\mathrm{Ent}(h^2)\le(2/\pi^2)\mathbb E\|\nabla h\|^2$ and applying Herbst to $-F$ gives exponent $\pi^2t^2/(2L^2)$. Hypercontractivity for the corresponding heat semigroup controls a heat-smoothed observable. A radial cutoff in vector length does not truncate the Neumann spectrum in the coefficient variables. [Ghang, Martin and Waruhiu, Theorem 2.2](https://arxiv.org/abs/1208.5548)

## A range obstruction for the optimal global constants

Put $d=w(w-1)/2$. If one configuration has $F\ge B>M$, there is another with $F\le M$. A path replacing rows one at a time and Cauchy–Schwarz give $\sum_i c_i^2\ge(B-M)^2/(w-1)$ even for optimal oscillations. Euclidean diameter gives $L^2\ge(B-M)^2/d$. Replacing scalar coordinates gives the analogous McDiarmid denominator lower bound $(B-M)^2/d$. These bounds apply to the total observable and allow cancellations between vector contributions.

For $w=406$, excess $.0002$, Part 72 certifies $E<6919492$ and $2^{49}$ pairs at radius below $\sqrt{.162}<1/2$. Thus one can take $B=2^{49}$ for every cutoff above. Even at $t=M$, the row exponent is at most $810(6919492/(2^{49}-6919492))^2<2\cdot10^{-13}$. On the Part 72 asymptotic family with excess $8\log w/[w(w-1)]$, the same construction has radius $o(1)$, $B=2^{\lfloor w/4\rfloor-1}$ and $E\sim w^4/2$. Both global exponents are $O(w^2 E^2/(B-E)^2)=o(1)$. The rarity of this configuration does not affect the global constants. A one-sided entropy proof using gradients under a negative exponential tilt could avoid it, but would need an estimate such as $\mathbb E[e^{-sF}\|\nabla F\|^2]/\mathbb E e^{-sF}=O(M)$ over an interval of positive $s$ independent of the profile. No such estimate follows from the support calculation. [Part 72 certificate and asymptotic construction](wall1_mu_moments.md)

## Lower-tail estimate after revealing the suffix

Condition on rows $1,\ldots,w-1$ and denote their suffix matrix by $H$. Enumerate primitive integer directions $v$ in the suffix modulo sign with $\|Hv\|<R$. For each let $z_v=\langle\mu_{0,>0},v\rangle\bmod1$ and set
$$
U_v=\bigcup_{1\le k<R/\|Hv\|}
\{z\in\mathbb T:\ \|kz\|_{\mathbb T}<\sqrt{1-k^2\|Hv\|^2/R^2}\},
\qquad p_v=|U_v|.
$$
Here length on the circle is normalized. Minimizing over the integer top coefficient proves that $N=0$ exactly when every $z_v$ misses $U_v$. The head-only vectors cannot be strictly short. This handles dependent multiples and all possible integer lifts before applying any moment bound.

For distinct directions the two integer characters have rank two, so the map onto the two-torus is surjective and sends Haar to Haar. Consequently $X=\sum_v1_{U_v}(z_v)$ has conditional mean $S=\sum_v p_v$ and variance $Q=\sum_v p_v(1-p_v)$. Cantelli gives the unconditional exponent
$$
f(g)=-\log\mathbb E_H\left[\frac{Q}{Q+S^2}\right],
\qquad \Pr(N=0)\le e^{-f(g)}.
$$
Use ratio one at $S=0$. A direction with $p_v=1$ gives conditional void probability zero directly. Since $Q\le S$, for any $s>0$ there is also the bound $\Pr(N=0)\le\Pr_H(S<s)+1/(1+s)$. The conditional second-moment bound works for more directions than a jointly independent list. It gives only logarithmic conditional suppression when $Q$ is comparable to $S$. The full-rank Haar argument for a cut is given in [Part 60](wall1_poisson_smallball.md).

Pairwise independence cannot justify replacing this ratio by $e^{-S}$. For example, circle characters $(1,j)$, $1\le j\le n$, with common target $\|z\|_{\mathbb T}<1/8$ have $S=n/4$, yet all miss whenever the first phase lies in $[3/8,1/2]$ and the second in $[0,1/(8n)]$. This gives void probability at least $1/(64n)$. This example concerns the character argument alone, since the ellipsoid also supplies other directions and prescribes their target widths. Janson–Łuczak–Ruciński inequalities for simultaneous occurrence of selected independent elementary trials need a representation of hits of that form. Circle-band hits under linear characters lack that representation in the given coordinates. Kim–Vu polynomial concentration likewise needs derivative bounds for a polynomial in independent inputs. The squared length is quadratic, but membership in a ball and the smoothed count are not bounded-degree polynomials. Approximating them would require controlling both approximation error after summation and polynomial influences.

For disjoint windows the profile exponents above add by independence. For overlapping windows sharing the same top row one can condition on all lower rows and union the corresponding target sets along each primitive direction (padding suffixes by zeros). The same conditional variance proof applies if the top GS scale and row coordinates are shared. Multiplying results from different starts with overlapping rows requires a separate conditional argument.

The achieved bounds depend on the profile. Even $S$ counts hit directions while $E$ averages lift multiplicities, and replacing $S$ by its mean inside the void bound has the wrong Jensen direction for $1/(1+S)$. No growing unconditional $f(E)$ below the deterministic packing threshold is established here. The twelve Part 71 boxes already have zero acceptance by the separate [dense-packing certificate](wall1_dense_packing_ld.md).
