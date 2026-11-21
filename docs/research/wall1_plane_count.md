# The terminal plane count at width 506

The horizontal contribution reduces to one indicator on the old lattice times the conditional probability that its designated shortest line wins. The positive-height contribution is a weighted disk count. Pulling the old-plane condition back one more selection preserves covolume exactly after multiplication by the selected length, but raises the required sublattice rank to three. There is no general propagation of the same physical plane cutoff, even for a single legal marked transition. The missing numerical estimate is a history average on the reduced graph experiment.

## One draw

Use the horizontal-first, no-lookahead kernel with its fixed signed ambient lexicographic tie rule. Condition on the state before the last draw, including its frame. Write $L=\Lambda$, $D=\det L$, $d=b-1$, and $U$ for a uniform class in $H$ with representative $\tilde U$. The window $W=L+\mathbb Z(\tilde U,1)$ has determinant $D$. Write $v$ for its signed winner, $s=|v|$, $Q=\pi_v W$, $G_i=V_i^{-1/i}$ for unit ball volume $V_i$, and set
$$
R(t)=cG_d(D/t)^{1/d},\qquad A(t)=tR(t).
$$
A primitive unoriented line in $Q$ lifts bijectively to a saturated plane through $v$ in $W$. Its primitive length is the plane covolume divided by $s$, by extending $v$ to a plane basis. Thus failure is exactly existence of a plane of area strictly below $A(s)$ through the winner. Rounding a lift along $v$ shows every nonzero quotient length is at least $\alpha s$, $\alpha=\sqrt3/2$. Write $h=G_bD^{1/b}$, $X=s/h$. Failure requires $X<K=(cG_d/\alpha)^{d/b}/G_b$. This includes part of the range above one. The Part 119 empirical association with $X<1$ gives no bound for the remaining strip. [First-pass kernel](wall1_first_tour.md) · [Experiment and audit](wall1_experiments.md)

## Horizontal planes

Let $x_0$ be the signed winner of $L$ in the inherited frame, $t=|x_0|$. Every selected horizontal line is this line. Put
$$
a_0= t\lambda_1(\pi_{x_0}L),\qquad
I_0(L)=\mathbf1\{a_0<A(t)\},\qquad
w_0(L,H)=\Pr_U(v=x_0).
$$
Here horizontal vectors are identified with their height-zero lifts. The conditional probability of at least one horizontal witness is **exactly** $I_0w_0$. The conditional expected number is $w_0$ times the number of primitive unoriented lines in $\pi_{x_0}L$ shorter than $R(t)$. Saturation in $L$ suffices since $W/L$ is free. The least area through $x_0$ satisfies
$$
t\sqrt{\lambda_2(L)^2-t^2/4}\le a_0\le t\lambda_2(L).
$$
For the upper bound project a vector independent of $x_0$ of length at most $\lambda_2$. For the lower bound round a shortest projected lift along $x_0$. Its length is at least $\lambda_2$ (it is independent and at least as long as $x_0$). In particular $\lambda_2(L)\ge\sqrt{R(t)^2+t^2/4}$ suffices to discard all horizontal witnesses. The exact property needed for their absence given a horizontal win is $a_0\ge A(t)$, which is weaker than excluding all small planes of $L$.

## Positive height and the selector

For a nonhorizontal plane its height image is $j\mathbb Z$, $j>0$. Choose its primitive horizontal kernel $x$ up to sign in $L$, and its positive-height basis vector $(y,j)$ modulo $(x,0)$, with $y\in j\tilde U+L$. Conversely each such pair generates a plane lattice $M$ with this kernel. Keep it precisely when saturated. Its area is
$$
B=|x|\sqrt{j^2+|\pi_x y|^2}.
$$
If $v=m(x,0)+k(y,j)$ belongs to $M$, its height is $kj$, with $\gcd(m,k)=1$. For $k=0$ the selected line is $x$ and the second generator has height $j$. For $k\ne0$ a complementary generator has height $nj$, where $mn-ka=\pm1$ for its coefficients $(a,n)$, and its height can be shifted by multiples of $kj$. Counting by $x,j,[y]$ avoids multiple counts from these completions, including when both selected-basis heights are nonzero.

Here is an exact conditional first moment $F$ of positive-height witnesses. Use the uniform area cap $C=A(Kh)$ since $A$ increases. Sum over $j>0$, primitive unoriented $x\in L$ with $j|x|<C$ and put $T=\sqrt{(C/|x|)^2-j^2}$. This is finite since $|x|\ge\lambda_1(L)$. For each such pair add
$$
\frac1{|jH|}\sum_{[y]\in L_j/\mathbb Zx,\ |\pi_x y|<T}
\frac1{|H[j]|}\sum_{U\in H:\ jU=y+L} f(x,j,[y],U),
\qquad L_j=\{y:y+L\in jH\}.
$$
Here $H[j]$ is the kernel of multiplication by $j$. Compute $W,v,s$ with this particular $U$. Set $f=1$ exactly when $M$ is saturated in $W$, $v\in M$, and $B<A(s)$. Saturation can be tested by primitivity of $(y-j\tilde U\bmod\mathbb Zx,j)$ in the free group $(L/\mathbb Zx)\oplus\mathbb Z$, by quotienting out the primitive first basis vector. Changes of representative give unimodular coordinate changes. Splitting $f$ by $k=0$ or $k\ne0$ gives disjoint height contributions to the moment. Replacing the selector by only certified competitor exclusions gives an upper bound if every true witness survives. Taking $f=1$ gives the raw Part 110 count in a cylinder modulo $\mathbb Zx$. In a projected disk count each point then has multiplicity $[L_j\cap\mathbb Rx:\mathbb Zx]$. The fiber weight follows by conditioning the uniform draw on $jU$ and applies even when $q\mid j$. [Averaged layers](wall1_additive_tour.md) · [Audit correction](wall1_experiments.md)

Consequently the conditional failure probability is at most $w_0 I_0+F$. One can multiply the positive-height filter by $1-\mathbf1_{v=x_0}I_0$ to charge only failures still uncovered. Denote the resulting moment by $F_*$. Alternatively replacing its count by a nonempty-set indicator inside each full draw gives equality.

## One step of induction

If $L=\pi_u W_-$, $a=|u|$, every saturated plane $P$ in $L$ has a unique saturated rank-three inverse image through $u$ of covolume $a\det P$. For example, the count of all planes of area below $C_0$ equals the count of saturated triples through $u$ in $W_-$ of covolume below $a C_0$. For $I_0$ retain also the flag lifting $x_0$ inside that triple. This identity incurs no repeated factor $\sqrt3/2$. Decomposing triples by height now requires horizontal triples and positive-height triples with a horizontal plane kernel. Iterating the horizontal branch increases rank again. The identity transfers the problem to flag statistics with selector weights.

A strict area loss at fixed rank is possible. Take an old lattice containing an orthogonal summand $D_3=\{z\in\mathbb Z^3:\sum z_i\text{ even}\}$ scaled by $r$, with $0<r<1/\sqrt2$, all remaining sides orthogonal of length 2, and append at $U=0$. Every shortest vector is in the summand and has length $\sqrt2 r$. Every old plane has area at least $\alpha(\sqrt2 r)^2=\sqrt3 r^2$ by planar reduction. The whole summand projects to a saturated plane of area $2r^3/(\sqrt2 r)=\sqrt2 r^2$. Thus at an intermediate cutoff the old count is zero and the new count is positive. This refutes monotone same-cutoff count propagation on the marked state space. It does not rule out induction on a distribution of flags for the actual graph histories. No closed rank-two induction or bound for that distribution follows from the last-step identities.

## Width-506 thresholds

In units of $h^2$ the required area cap at $X$ is $J X^{1-1/d}$ with $J=cG_d/G_b^{1+1/d}$. At $X=1$ it is between 0.94986 and 0.94987, and the sufficient horizontal exclusion is $\lambda_2(L)/h\ge1.07343$ when $t=h$. Across the entire gate $X<1.09661$ the cap stays below $1.04144h^2$. This last bound suffices for the enumeration cylinder and can greatly overcount near small $X$.

Take expectations over the unconditioned reduced $400\times105$ initial graph and the next 406 draws; the displayed fiber formula integrates draw 407. One sufficient allocation is $\mathbb E[w_0I_0]\le0.00488848$ and $\mathbb E[F_*]\le0.00488848$. More generally any sum at most $0.00977696$ works, including a charge for discarded histories if the moments are restricted to good histories. The coupling then gives original failure below 0.01. These are required upper estimates under the proposed allocation. Neither the measured small-width gate frequencies nor the deterministic GH floor estimates either expectation at 506. [Suffix coupling](wall1_idea_round2.md) · [Suffix probability](wall1_lit_projections.md) · [Physical target](wall1_idea_drift.md) · [Wall 1](../PROOF_GAP.md)

```python
from mpmath import iv
from fractions import Fraction as Fr
iv.dps = 50
I = iv.mpf
b, d, q = 506, 505, 3329
def V(n):
    return iv.pi**(I(n)/2) / iv.gamma(1+I(n)/2)
def G(n):
    return V(n)**(-I(1)/n)
c, alpha = I('.954'), iv.sqrt(3)/2
K = (c*G(d)/alpha)**(I(d)/b)/G(b)
J = c*G(d)/G(b)**(1+I(1)/d)
assert I('1.09660') < K < I('1.09661')
assert I('.94986') < J < I('.94987')
assert I('1.04143') < J*K**(1-I(1)/d) < I('1.04144')
assert I('1.07342') < iv.sqrt(J**2+I(1)/4) < I('1.07343')
prefix = V(b)*(1+iv.sqrt(b)/(2*q))**b*sum(q**i for i in range(1,106))/2
assert 2*Fr('.00488848') == Fr('.00977696')
assert prefix + I('.00977696') < I('.01')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

**Verified.**

* The horizontal factorization w_0·1{a_0 < A(t)}, with the bounds on a_0.
* The positive-height first moment. It counts each saturated plane once, and the fiber normalization |jH|·|H[j]| = |H| is exact.
* The rank-3 pullback identity, with covolume |u|·det P.
* The scaled D_3 obstruction, on the abstract marked state space. Whether it is reachable under the graph law is a separate
  question.

**Width 506.** The failure-witness area is below 1.04144·GH(W)², where JK^{1−1/505} ∈ (1.0414356763, 1.0414356764).

**Budget.** B(105) + 2·0.00488848 < 0.01. Unequal splits with the same total also suffice.

**Open.** The two history-averaged estimates.
