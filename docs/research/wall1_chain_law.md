# Selection along a one-pass chain of projected lattices

At rank $N=1023$ and widths $b=406,506$, the infimum over fresh basis selectors of the terminal 1% quantile is zero **in units of the terminal lattice's own Gaussian heuristic**. This holds at both remaining ranks $b$ and $b-1$. In fact one can force both normalized minima below any prescribed positive threshold for every input by adapting just the rank-$(b+1)$ window. This strengthens the physical-length counterexample in the [marked reducer note](wall1_markov_reducer.md). The assertion concerns freely reselected presentations. A fixed sliding implementation that must preserve its inherited window has fewer choices.

## A. Whole-state likelihood and a selector that concentrates shape

**Window realization.** In a rank-$d$ Euclidean lattice $M$, every primitive $v$ is the unique shortest pair $\pm v$ of some primitive rank-$(d-1)$ window, for $d\ge3$. Complete $v$ to a basis and let $C$ consist of the other columns projected onto $v^\perp$. In their integer coordinates take $u_j=h e_j+e_{j+1}$ for $1\le j\le d-2$. These columns extend by $e_1$ to a unimodular matrix (expand along $e_1$). Lift them using the original completion and put them after $v$. Every nonzero integer combination in the projected window has norm at least $\sigma_{\min}(C)(h-1)$ by the reverse triangle inequality. Choose an integer $h>1+|v|/\sigma_{\min}(C)$. Any window vector outside $\mathbb Zv$ is now longer than $v$. This constructs a basis whose first $d-1$ columns implement the desired mark by exact SVP.

**Two short directions.** Freeze any prefix ending at rank $d=b+1$. In a physical basis of its output take the first three columns $a,u,w$, write $D=\det M$ for the positive covolume, and choose
$$
v=k^2 a+k u+w,\qquad k\ge2.
$$
Its last nonzero coordinate is one, so the window construction applies. Write $P$ for projection orthogonal to $v$. The vectors $Pa$ and $P(ka+u)$ are independent since $w$ is independent of $a,u$. The identity $P(ka+u)=-Pw/k$ bounds its length by $|w|/k$, and $|Pa|\le |u|/k+|w|/k^2$. With $A=|a|+|u|+|w|$, both lengths are at most $A/k$ and $|v|\le Ak^2$. The new rank-$b$ lattice has determinant $D/|v|$. Its minimum $s$ is at most $A/k$. After its full-width SVP at least one of the two independent short vectors has nonzero projection, of norm at most $A/k$. This rank-$(b-1)$ quotient has determinant $D/(|v|s)$. Thus, writing $G_j=V_j^{-1/j}$ and $Y_j=\lambda_1(M_j)/(G_j\det(M_j)^{1/j})$ at remaining rank $j$,
$$
Y_b\le {A\over G_b}(A/D)^{1/b} k^{-1+2/b},\qquad
Y_{b-1}\le {A\over G_{b-1}}(A^2/D)^{1/(b-1)} k^{-1+1/(b-1)} .
$$
Both powers are negative for $b>2$. Choose the first integer $k\ge2$ for which both bounds are below $c$. This is a finite measurable choice for every nonsingular input. Completion can use integer elimination. A lattice-only version takes a measurable shortest-Frobenius-norm basis with uniform tie breaking over the finite minimizers. Rotation carries that finite set bijectively to the new minimizers, so the rule is rotation equivariant in law (use the same integer-coordinate completion). Even a fixed $k$ tending to infinity gives bad-event probability tending to one by bounded convergence for any fixed prefix law. These selectors make no claim to polynomial bit cost.

**Likelihood consequence.** At determinant $D'$, the Haar comparison shape has $\mu_j(Y_j<c)\le c^j/(2\zeta(j))$ by counting primitive pairs. Under the adaptive rule the same event has conditional probability one for almost every output determinant, by disintegration. Any conditional Haar density bound must therefore be at least $2\zeta(j)c^{-j}$ at either output rank. There is no selector-uniform finite bound, even allowing a different constant at each rank. The same test applies to a joint comparison that draws the actual output determinant and an independent Haar shape.

In primitive unfolding, at fixed input determinant and history the quotient likelihood given the normalized marked vector is proportional to $\int f(E)q_E(v)\,dt$, where $E$ is the reconstructed parent, $f$ its posterior density and $q$ the oriented selection mass conditional on the parent. Length conditioning integrates directions before dividing by the marginal. Bounding the integrand by a supremum leaves that denominator uncontrolled. Rotation invariance constrains directions while $Y_j$ is itself rotation invariant. The example exhibits the missing normalization even when the reducer can compute its window from the present lattice and fresh coins alone. [One-step disintegration](wall1_selection_law.md)

## B. Terminal pinning

For a terminal rank $j$, index candidates by saturated rank-$(N-j)$ prefix sublattices $S$ of the original $L$. Let $p_L(S)$ be the chain's probability of ending at that prefix span given $L$, summing over histories. Successive projections identify the terminal lattice isometrically with $P_{S^\perp}L$. The exact bad probability is the Haar expectation of
$$
\sum_S p_L(S)\,\mathbf1\{Y(P_{S^\perp}L)<c\}.
$$
Here $Y$ denotes the own-GH ratio in the indicated rank. For the constructed rule the sum is one almost surely at both indices. In particular the final full-width shortest-vector call can inherit a parent with two independent short directions, so its quotient is forced into the bad set. The factor two at one GH length in Part 46's setting assumes a Haar input and conditions on that length. Neither requirement follows from summing prefix counts. Part 86 obtains a determinant cutoff from *reversed dual window inequalities on the output basis*. A forward exact call enforces no such inequalities. A weighted-count proof for a specified implementation must bound the weight on bad prefixes or prove a cutoff for the prefixes it actually selects. The two-short-direction example precludes a selector-independent estimate below one. [Dual pinning](wall1_dual_pinning.md) · [Parts 45, 46, 86 and 103](../PROOF_GAP.md)

## C. Fresh invariant bases and product kernels

Fix the full parent and its presentation. Integer bases and their primitive windows form countable sets. There is no uniform probability on proper windows invariant under all integer basis changes, since the basis group acts transitively on infinitely many windows. Uniform ambient rotation exists, but rotating a presented lattice preserves all window Gram matrices. If the rotation is used to choose a new basis of the same lattice, conditional on the parent the normalized window shapes up to isometry are still countably supported. Haar shape up to isometry at these widths is nonatomic (each compact rotation orbit has lower dimension than lattice space). Thus their conditional total variation distance from a fresh Haar shape is exactly one. Even a normalized shortest length drawn from the fresh Haar minimum law is nonatomic, whereas the possible lengths from a fixed parent form a countable set. Haar has no atom at a specified minimum because the expected number of vectors on that sphere is zero.

Consequently fresh basis coins cannot implement the fresh-Haar one-step input law conditional on the requested full state. A product of the actual selector-dependent Markov kernels exists; its factors integrate over this discrete choice. A product for a coarser observable after averaging hidden states would require a separate identity for its posterior at every history. Countability alone does not exclude such a marginal identity for a specially designed selector. There is no tour-level numerical quantile at either width specified by invariance alone. The infima proved above are exact; each fixed terminating selector has positive 1% quantile since its normalized minimum is positive almost surely.

## Interval checks

The construction works for arbitrary $c>0$. At the one-step reference $c=0.925$ the necessary likelihood constants already exceed $10^{13}$ at all four output ranks. This check drops the factor $\zeta(j)>1$.

```python
from mpmath import iv
iv.dps = 60
c = iv.mpf(925) / 1000
for b in (406, 506):
    assert -1 + iv.mpf(2)/b < 0
    assert -1 + iv.mpf(1)/(b-1) < 0
    for j in (b, b-1):
        assert 2 / c**j > 10**13
        assert c**j / 2 < iv.mpf(1)/100
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Selector validity.** The selector is valid, terminating, Borel, and rotation-equivariant in law: it draws uniformly among
  Frobenius minimizers. Exact window SVP emits ±v.
* **Survival argument.** The two short projected candidates stay independent after projection along v, so at least one survives
  the full-width SVP.
* **Normalization.** It uses exact successive covolumes. The powers of k are negative at both ranks.
* **Conclusions.** The infimum over selectors of the 1% quantile is 0 at ranks b and b − 1. No selector-uniform density ceiling
  exists. Fresh basis coins have conditional TV distance exactly 1 from a fresh Haar shape.
* **Open.** Reducers that preserve their inherited window.

All embedded scripts were rerun with outward rounding.
