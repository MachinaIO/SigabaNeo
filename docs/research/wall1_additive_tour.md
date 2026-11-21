# Additive first-tour bounds and the determinant of a terminal run

For the exact no-lookahead, horizontal-first tour at $(m,n,q)=(511,512,3329)$, the following terminal thresholds have total failure probability **zero**, hence at most 1%. The improvement over the earlier terminal floor comes from keeping the length of the last run of subunit selections in the determinant bound. The optimum unconditional 1% quantile remains unknown.

| Width $b$ | Last full window, own GH | Retained quotient, own GH |
|---:|---:|---:|
| 406 | $8.66605\times10^{-6}$ | $8.54005\times10^{-6}$ |
| 506 | $5.27489\times10^{-6}$ | $5.21484\times10^{-6}$ |

## One draw and all its layers

Index the graph phase by the number $i$ of graph columns already processed. Put $r=b-1$, $D_i=\det\Lambda_i$, $G_d=V_d^{-1/d}$ for unit ball volume $V_d$. Initially $\Lambda_0=q\mathbb Z^r$ and $H_0$ is full torus $q$-torsion. Given the history, $g$ is uniform on $H_i$, the append has height one, and the new mark is $Q_*H_i$. These are the filtration and selection conventions of [Part 108](wall1_first_tour.md).

Fix the history and suppress $i$. For integer $0<|k|<R$ put $t=(R^2-k^2)^{1/2}$, $L_k$ the inverse image of $kH$ in the horizontal Euclidean space, and $J=|kH|$. The expected signed-vector count at this **single** height is exactly
$$
 M_k(t)=\#(L_k\cap B_t^\circ)/J,\qquad \det L_k=D/J.
$$
Indeed each coset has $|H|/J$ preimages. For prime $q$, $J=|H|$ unless $q\mid k$, when $L_k=\Lambda$ and $J=1$. Include the origin of the horizontal ball even then: its lift has height $k$ and is nonzero. For the total signed count add the nonzero horizontal count and twice the sum over positive heights.

Writing $\rho_k$ for the covering radius of $L_k$, integration over Voronoi cells gives
$$
 V_r(t-\rho_k)_+^r/D\ \le M_k(t)\le V_r(t+\rho_k)^r/D .
$$
The cells centered in the open ball cover the smaller open ball and are contained up to their boundary in the larger ball. Since $\Lambda\subseteq L_k\subseteq q^{-1}\Lambda$, one may use $\rho(\Lambda)$ in both bounds. Packing balls of radius $\lambda_1(\Lambda)/(2q)$ gives the alternative upper bound $(1+2qt/\lambda_1(\Lambda))^r/J$. For full torsion and $q\nmid k$, $L_k=q^{-1}\Lambda$, $J=q^r$, and $\rho_k=\rho(\Lambda)/q$. For example a relative error at most $\epsilon\in(0,1)$ is certified if $\rho_k/t\le\min((1+\epsilon)^{1/r}-1,1-(1-\epsilon)^{1/r})$. Thus $r\rho_k/t=o(1)$ suffices for asymptotic relative accuracy. Exactly, the relative error is the absolute lattice-point discrepancy divided by $V_rt^rJ/D$; a small covering-radius bound is sufficient, not necessary. The comparison is with volume at the *slice* radius $t$. Full cardinality alone supplies no uniform relative error near a grazing layer.

## Additive accounting and the cost of a projection

Write $a=|v|=\lambda_1(W)$ and $\alpha=\sqrt3/2$. A nonzero quotient vector shorter than $s$ has a lift shorter than $(s^2+a^2/4)^{1/2}$ by rounding along the primitive $v$. Its lift has length at least $a$, hence $\lambda_1(QW)\ge\alpha a$. The exact determinant update is $D'=D/a$. For target quotient ratio $c'$ the bad event implies
$$
 a<R(D)=\left(c'G_rD^{1/r}/\alpha\right)^{r/(r+1)}.
$$
For a target window ratio $c_W$ use $R(D)=c_WG_bD^{1/b}$ instead. Define $p(R)=\min(1,\sum_{1\le k<R} M_k(\sqrt{R^2-k^2}))$. Markov's inequality counts positive heights, with no independence assumption. Whenever $R(D)\le cG_rD^{1/r}$ on the good histories for $E_i(c)$, one obtains
$$
 \Pr(E_{i+1}(c'))\le\Pr(E_i(c))+\mathbb E[\mathbf1_{E_i(c)^c}p(R(D_i))].
$$
If the threshold condition fails, replace $p$ by one on histories with $\lambda_1(\Lambda_i)<R(D_i)$. Iteration adds the error terms. First-exit accounting may restrict each expectation to histories surviving all earlier tests. Thresholds can be predictable functions of the current state if the event definitions and the cutoff are adjusted accordingly.

In physical units start with $T_0=q$. At append $j$ choose cutoff $R_j\le T_{j-1}$ and charge $p(R_j)$ on surviving histories. Then $a_j\ge R_j$ outside the charged event and $T_j=\alpha R_j$ is the propagated physical floor. The exact corresponding own-GH floor is $T_j/(G_rD_j^{1/r})$ with $D_j=q^r/\prod_{l=1}^j a_l$. In relative units the largest next constant allowed by the horizontal cutoff at a fixed history is $c'=\alpha c(cG_rD_i^{1/r})^{1/r}$. Initially $c=1/G_r$, so even throwing away the entire fresh-layer charge gives a factor $\alpha q^{1/r}<0.884$. With the largest physical cutoffs, $R_j=q\alpha^{j-1}$, the first cutoff below one occurs at $j=58$. At the last window and quotient the optimistic physical floors are respectively $q\alpha^{511}$ and $q\alpha^{512}$. These describe the limit of this scalar propagation even with free fresh layers. They do not bound the actual minima from above. A sharper terminal treatment can forget the earlier physical floors.

## Terminal run with a coupled covolume estimate

For either terminal observation write $s$ for its minimum and $d$ for its rank. View a quotient observation as one extra shortest-vector selection without append. Every used graph prefix contains the $q$-multiples of its coordinate axes. Their projections span every retained space and have lengths at most $q$. If $s\ge1$, extend a shortest vector by $d-1$ projected axes. Hadamard gives $D_{\rm term}\le s q^{d-1}$ and normalized minimum at least $G_d^{-1}q^{-(d-1)/d}$.

Otherwise let $h$ be the length of the maximal terminal run of selections below one, including the observation. Its first length $a_1$ is at least $\alpha$: the previous selection had length at least one, and a subunit vector cannot use the new height. The cubic start also satisfies this bound. Write $L$ for the rank-$r$ retained lattice at the start of the run. All $h$ directions come from $L$ under successive projections, since earlier removals in its span preserve each newer vertical coordinate and the last used fresh column would contribute a nonzero integer there. Thus $h\le r$. This is a path-dependent suffix argument requiring at most $r$ subunit selections.

Lift the $h$ vectors back into $L$. They span a sublattice of covolume $a_1\cdots a_h$ in their span by Gram–Schmidt, with $a_h=s$. Complete this independent set to full rank with $r-h$ projected $q$-axes **at the start of the run**. Their perpendicular residuals have length at most $q$, so
$$
 \det L\le (a_1\cdots a_h)q^{r-h}.
$$
There are exactly $h-1$ removals between this state and the observation, including when the last observation omits an append. Every intervening append multiplies covolume by one. Cancellation therefore gives $D_{\rm term}\le s q^{r-h}$ at either output. The loss of one power of $q$ per additional subunit selection compensates for its possible reduction of $s$.

For completeness set $A_1=0$. For the suffix of $k$ run vectors the lifted sublattice has minimum at least $a_{h-k+1}$, since its first selection is shortest in that window. Applying Hermite's inequality to its product covolume, and also using the adjacent lift bound, gives by induction $\log(a_{h-k+1}/s)\le A_k$ with
$$
 A_k=\min\left(A_{k-1}-\log\alpha,\ 
 (\log(\gamma_k^{k/2})+\sum_{j<k}A_j)/(k-1)\right).
$$
Use $\gamma_2=1/\alpha$ and Blichfeldt's upper bound $\gamma_k^{k/2}\le 2^{k/2}(1+k/2)/V_k$ as in [the terminal run proof](wall1_terminal_mixing.md). Thus $s\ge\alpha e^{-A_h}$. Minimize
$$
 G_d^{-1}(\alpha e^{-A_h})^{1-1/d}q^{-(r-h)/d}
$$
over $1\le h\le r$, also including the $s\ge1$ case. This yields the table. The limiting run lengths are 83 at both outputs for width 406 and respectively 113 and 112 for width 506. These are minima of the certificate over run lengths, with no claim of attainable equality in the lattice inequalities.

To spend a positive failure budget effectively, one sufficient input is a bound on the *mass* of histories with an inherited vector below a chosen late cutoff, together with bounds on the expected positive-layer counts on the complementary histories whose sum fits the remaining budget. A joint bound on the shortest two independent window vectors can also sharpen the projection loss, because a short quotient lift must be independent of $v$. A history-uniform late restart at near-GH scale fails even with 64 draws remaining by the zero-prefix example in the terminal note. The [single Haar selection law](wall1_selection_law.md) supplies neither history estimate for [Wall 1](../PROOF_GAP.md).

## Interval verification

The logarithmic recurrence below encloses both endpoints, including at a minimum of overlapping intervals. The final assertions isolate the minimizing index against every competitor and round the displayed thresholds down.

```python
from mpmath import iv
iv.dps = 60
I = iv.mpf
q = I(3329)
alpha = iv.sqrt(3)/2
V = [I(1), I(2)]
for k in range(2, 507):
    V.append(2*iv.pi*V[k-2]/k)
A = [I(0), I(0)]
total = I(0)
for k in range(2, 506):
    power = 1/alpha if k == 2 else 2**(I(k)/2)*(1+I(k)/2)/V[k]
    x = A[-1]-iv.log(alpha)
    y = (iv.log(power)+total)/(k-1)
    A.append(I([min(x.a, y.a), min(x.b, y.b)]))
    total += A[-1]
assert q*alpha**57 < 1 < q*alpha**56
assert I('3.9853e-29') < q*alpha**511 < I('3.9854e-29')
assert I('3.4514e-29') < q*alpha**512 < I('3.4515e-29')
for r, d, h, lo in [(405,406,83,'8.66605e-6'), (405,405,83,'8.54005e-6'),
                    (505,506,113,'5.27489e-6'), (505,505,112,'5.21484e-6')]:
    assert alpha*q**(I(1)/r) < I('0.884')
    u = I(1)/d
    bounds = [V[d]**u*q**(u-1)]
    for j in range(1, r+1):
        bounds.append(V[d]**u*(alpha*iv.exp(-A[j]))**(1-u)*q**((j-r)*u))
    assert all(bounds[h] < x for j,x in enumerate(bounds) if j != h)
    assert I(lo) < bounds[h] < I(lo)+I('1e-11')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT. The note's scripts and both predecessors' scripts pass. An independent 80-digit computation
isolated the minimizing run length h for each case:

| b | Last window | Retained quotient |
|---:|---|---|
| 406 | h = 83, 8.66605749·10⁻⁶ | h = 83, 8.54005924·10⁻⁶ |
| 506 | h = 113, 5.27489036·10⁻⁶ | h = 112, 5.21484090·10⁻⁶ |

Verified ingredients:

* the √3/2 contraction of the propagated threshold, whose first maximal cutoff below one is at append 58;
* the terminal determinant bound D ≤ s·q^{b−1−h};
* the exact averaged layer count #(L_k ∩ B)/|kH| with Λ ⊆ L_k ⊆ q⁻¹Λ.

The optimal unconditional 1% thresholds remain open.
