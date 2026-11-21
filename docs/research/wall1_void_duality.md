# Duality of the fixed-profile void event

Reversing and size-reducing the dual basis gives exactly the independent uniform coefficient law at the reversed reciprocal profile. Gaussian Poisson summation also gives an exact correspondence, but preserves the direction of every tail at fixed profile. In particular, positive raw moments of dual Gaussian mass do not turn the primal void into a Markov upper-tail estimate. Below deterministic exclusion I obtain no positive exponent depending only on the short-pair mean from this argument.

## The dual chart

Use column bases in orthonormal Gram–Schmidt coordinates. Write $B=DU$, where $D=\operatorname{diag}(g_0,\ldots,g_{w-1})$ and $U$ is upper unitriangular with independent entries above the diagonal uniform on the centered half-open unit interval. Let $J$ reverse coordinates. Reversing the dual columns and applying the orthogonal map $J$ gives
$$
 JB^{-T}J=(JD^{-1}J)\,\phi(U),\qquad \phi(U)=JU^{-T}J .
$$
In particular the new Gram–Schmidt lengths are $h_i=1/g_{w-1-i}$. In dimension three the long upper entry of the raw matrix is $U_{01}U_{12}-U_{02}$, which exceeds $1/2$ on a set of positive measure. The raw matrix does not have the original cube law.

**Proof of the reduced law.** Let $G$ be the upper unitriangular real group and $\Gamma$ its integer subgroup. The cube is a fundamental domain for right multiplication by $\Gamma$. In each column $j$, reduce entries in order $j-1,\ldots,0$ by subtracting integer multiples of the corresponding earlier columns. Each pivot is one and subsequent steps preserve entries already centered. Uniqueness follows by descending through the entries of each column of $U\gamma$, which successively force the corresponding integer multipliers to vanish if both representatives are centered. Lebesgue measure in the strict upper entries is Haar measure since multiplication by a fixed group element on either side has triangular Jacobian with unit diagonal in increasing superdiagonal order. Thus the iid cube law represents invariant probability on $G/\Gamma$. The involutive group automorphism $\phi$ preserves $\Gamma$, so its pushforward on the quotient is again invariant probability. Returning to the unique centered representative proves the claim, including independence. Integer column operations preserve the lattice and the Gram–Schmidt lengths.

For $g_j=g_0 r^j$, $h_j=g_j/(g_0^2 r^{w-1})$. Up to deterministic scale and orthogonal reversal, the geometric ensemble is self-dual in distribution. The primal and its own dual are coupled by an involution. Sampling an independent second block would lose that coupling.

## What Poisson summation implies pointwise

Write $R=g_0$, $d=\prod_i g_i$, and $T_L(t)=\sum_{x\in L}e^{-\pi t\|x\|^2}$. The void means $\lambda_1(L)=R$, since the first basis vector has length $R$ and the counting ball is open. Gaussian Poisson summation gives, for every sample,
$$
 X:=T_{L^*}(1/t)=c\,T_L(t),\qquad c=d\,t^{w/2}.
$$
In particular $X\ge c\sum_{k\in\mathbb Z}e^{-\pi t k^2 R^2}$ for **every** sample. The origin and the known line cannot furnish a void-specific dual excess.

Here is an explicit upper threshold. If the void holds, disjoint open balls of radius $R/2$ centered at lattice points of norm at most $u$ fit in the ball of radius $u+R/2$. Integrating the nonzero point count against the negative derivative of the Gaussian yields
$$
 T_L(t)-1\le H_w(a):=\int_1^\infty 2av e^{-av^2}\big[(1+2v)^w-1\big]\,dv,\qquad a=\pi t R^2 .
$$
This includes points at the boundary $R$. Consequently the void implies $X\le c(1+H_w(a))=:b$. For any $s>0$, the number of nonzero dual points of norm at most $s$ is at most $e^{\pi s^2/t}(b-1)$ on the void. Also $H_w(a)\to0$ for fixed $w$ as $a\to\infty$. In the usual convention $\eta_\epsilon(M)=\inf\{u>0:T_{M^*}(u^2)\le1+\epsilon\}$, the bound $H_w(a)\le\epsilon$ gives $\eta_\epsilon(L^*)\le\sqrt t$. A bound on $\eta_\epsilon(L)\le 1/\sqrt t$ from the dual mass requires the separate condition $b\le1+\epsilon$. [Smoothing parameter and transference](https://arxiv.org/abs/1412.7979)

The correspondence is exact even in the zero-temperature limit. For any sequence $t\to\infty$,
$$
 -\frac{1}{\pi t}\log\left(\frac{X}{c}-1\right)\longrightarrow\lambda_1(L)^2 .
$$
Indeed the nonzero theta mass is at least one shortest-vector weight and, for $t\ge1$, at most $(T_L(1)-1)e^{-\pi(t-1)\lambda_1(L)^2}$. An anomalously small normalized dual excess thus encodes the primal void itself.

## Can a dual upper tail help?

* **Ordinary theta moments.** For every $k>0$, Markov on $X^k$ bounds the opposite tail to $X\le b$. If the universal lower bound from the known line is used as the upper-tail threshold, the Markov ratio is at least one. A legitimate lower-tail estimate is $\Pr[\mathrm{void}]\le\inf_{u\ge0}e^{ub}\mathbb E e^{-uX}$. Substituting $X=cT_L(t)$ and rescaling $u$ gives exactly the primal Laplace bound. The same equality holds for standardized centered moments. For example, if $m=\mathbb EX>b$, Cantelli gives $\operatorname{Var}X/(\operatorname{Var}X+(m-b)^2)$; the factor $c^2$ cancels. Estimating these expressions sharply under the reciprocal chart is a possible new input.
* **Successive minima.** Euclidean transference $\lambda_1(L)\lambda_w(L^*)\le w$ does give a genuine upper-count implication. On the void the dual ball of radius $w/R$ contains at least $w$ independent pairs. Its *ordinary count* can be enormous even without transference. For example in every even width $w\ge 4$ with packing-feasible determinant $d\ge V_w(R/2)^w$, that ball contains at least $(\pi/2)^w$ points including zero, for every sample. Here $V_w$ is unit ball volume. Indeed some translate of the dual ball of half the radius contains at least its mean occupancy $dV_w(w/(2R))^w$ by averaging over a fundamental domain. Subtract one occupant from the others, counting zero too. The resulting bound is at least $V_w^2(w/4)^w\ge(\pi/2)^w$ by $(w/2)!\le(w/2)^{w/2}$. In particular at even application widths ordinary count Markov at threshold $2w+1$ is vacuous. This calculation leaves open the probability of *full rank* among those points. Even that event is automatic on any reciprocal profile satisfying $\max_j(h_j^2+\sum_{i<j}h_i^2/4)\le(w/R)^2$, by the reduced dual basis itself.

Thus the direct positive-theta/Markov argument supplies only $f(E)=0$ on the packing-feasible range, in the sense of the bound one. Deterministically excluded profiles have void probability zero. This is a limit of the argument, not a lower bound on the actual void probability. A quantitative lower-tail law for dual mass, or an independently rare dual rank or other structural event forced by the void, remains missing. The involution supplies no product rule for overlapping tests and no new suppression estimate for the surviving bad-profile integral. [Wall 1 frontier](../PROOF_GAP.md) · [Fixed-profile moments](wall1_mu_moments.md) · [Packing exclusions](wall1_dense_packing_ld.md)
