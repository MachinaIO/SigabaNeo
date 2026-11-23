# A two-mark covering inequality for the first pass

An independent second column gives a quadratic drift bound for the **height-one void profile**, evaluated at two different radii. The bound averages the actual append-and-freeze transition, including its choice of shortest vector. It does not establish drift at the moving GH radius. The missing inputs can be expressed as the mass of a shell of nearest-coset distances and the fourth powers of the Fourier coefficients of its void indicator.

There is a quantitative loss in iterating the bound by discarding the length removed by projection. From every incoming draw-129 history, the probability of even one vector using the next 277 columns and already short enough *before* their intermediate projections, at radius $1.10\cdot35.0743$, is below $10^{-404.62}$. At radius 122 it is still below $10^{-13.64}$. These are upper bounds on the success of this sufficient test. They give no lower bound on the actual void.

## The observable and the exact update

Use the incoming history just before draw $i$, including the old columns and the tie-breaking frame. Write $M\subseteq K$ for the retained lattice and projected integer grid, $H=K/M$, $d=505$, $n=506$, $q=3329$, $D=\det M=V_n g^n$, and $V_n=\pi^{253}/253!$. Define the full physical-radius profile

$$
 p(b)=|H|^{-1}\#\{z\in H:\operatorname{dist}(\tilde z,M)>b\}.
$$

At appended radius $r\ge1$ the height-one miss has probability $p(\sqrt{r^2-1})$. For $r<q$ and $\lambda_1(M)>r$, the true long-winner probability is the fraction of marks $u$ for which **all** $1\le k\le\lfloor r\rfloor$ satisfy $\operatorname{dist}(k\tilde u,M)>\sqrt{r^2-k^2}$. A short horizontal vector or the period at radius $r\ge q$ settles the draw. Thus the height-one profile majorizes the tail after correcting its radius. [Part 217](wall1_long_winner_ceiling.md) · [Part 219](wall1_covering_ceiling.md)

Take independent uniform $U,V\in H$ by revealing two raw columns in the old frame. For each $u$, form $W_u=(M,0)+\mathbb Z(\tilde u,1)$, select its primitive shortest vector $w_u$, write $s=\|w_u\|$, and let $Q_u$ project off its line. The next state has $M'=Q_uW_u$, $H'=Q_{u*}H$, $g'=g s^{-1/n}$. Conditional on $U=u$, $Q_{u*}V$ is uniform on $H'$, including when the map has a kernel. For a mark represented by $v\in K$, its next horizontal distance is exactly

$$
 \min_{m\in M,\ j\in\mathbb Z}
 \left(\|z\|^2-\langle z,w_u/s\rangle^2\right)^{1/2},
 \qquad z=(v+m+j\tilde u,j).
 \tag{1}
$$

This is distance to $Q_u W_u$ in the quotient since the representatives are exactly the projections of the indicated translates. The minimum exists because the winner is a primitive lattice vector. Conversely any projected point of norm at most $b$ has a representative in this same affine lattice of norm at most $\sqrt{b^2+s^2/4}$, by subtracting an integer multiple of $w_u$. The rank-one term in (1) is where a short next representative can first become visible. [Part 108](wall1_first_tour.md) · [Part 227](wall1_frozen_contraction.md)

## Quadratic drift across radii

Let $S=\min(q,hg)$, $h=\sqrt{56.2142}\,V_n^{1/n}$, the incoming pathwise cap on $s$. Set $R=tg S^{-1/n}$, so $tg'\ge R$ on every branch. Assume $R^2\ge2$. Put $b_j=\sqrt{R^2-1-j^2}$ when real. Denote the random next height-one miss probability at its own threshold by $P'=p'(\sqrt{(tg')^2-1})$. For any set of available offsets $J$,

$$
 P'(u)\le \Pr_V\big[\operatorname{dist}(\tilde V+j\tilde u,M)>b_j
                         \ \text{for all }j\in J\big].
 \tag{2}
$$

Indeed a single old hit yields a representative in (1) of norm at most $\sqrt{R^2-1}$, leaving room for the next height one. This statement holds for the actual selected winner, even at a tie. The law used here conditions only on gates already decided by the incoming history.

For $j\ne k\pmod q$, the map $(U,V)\mapsto(V+jU,V+kU)$ preserves uniform measure on $H^2$. Its matrix is invertible since $qH=0$ and $q$ is prime. Thus the two misses on the right of (2) are *exactly independent before the first reveal*. No independence of the two selected winners is needed. In particular,

$$
 \mathbb E[P'\mid\text{incoming history}]\le p(b_0)p(b_1)\le p(b_1)^2 .
 \tag{3}
$$

Writing $p_{*}=p(\sqrt{(tg)^2-1})$, on entries with $S\ge1$ put $\Delta=p(b_1)-p_{*}\ge0$. Equation (3) gives strict contraction in conditional mean if $\Delta<\sqrt{p_{*}}-p_{*}$ for $0<p_{*}<1$. For example at $p_{*}=0.18$ the allowable shell mass is approximately 0.24426. This is a condition on **distinct marks** whose nearest distance falls in the shell. A first moment counting all their representatives cannot be used as their covered fraction.

The scale difference matters. At the illustrative scale $g=35$, $t=1.10$, the cap gives $S\approx47.862$, $R\approx38.207$, and $b_1/g\approx1.090875$. The ratio of the two Euclidean $d$-ball volumes at $b_1$ and $\sqrt{(tg)^2-1}$ lies in $(0.01765,0.01767)$. This computes a volume ratio only. No bound on $\Delta$ or assertion that a history has exactly $g=35$ is needed. Short winners make the actual next radius larger. Exploiting that gain in a drift estimate needs a lower bound on its frequency, whereas the short-winner first moments give upper bounds. The exact shell profile or the projection saving in (1) would supply different information. [Part 222, determinant feedback](wall1_long_winner_handle.md)

## From mean drift to exceptional histories

For a fixed prefix let $A=\{v:\operatorname{dist}(\tilde v,M)>b_1\}$, $p=|A|/|H|$, and $a=\mathbf1_A$. Since $b_0\ge b_1$, (2) bounds $P'(u)$ by $C(u)=\mathbb E_v[a(v)a(v+u)]$. With normalized Fourier coefficients on $H$,

$$
 \mathbb E_u C(u)=p^2,\qquad
 \operatorname{Var}_u C(u)=\sum_{\chi\ne1}|\widehat a(\chi)|^4.
$$

Indeed the Fourier coefficients of the correlation are the squared moduli, so the second identity follows by Parseval. Consequently for $\alpha>p^2$,

$$
 \Pr_u(P'(u)>\alpha)\le
 \frac{\sum_{\chi\ne1}|\widehat a(\chi)|^4}{(\alpha-p^2)^2}
 \le \frac{\max_{\chi\ne1}|\widehat a(\chi)|^2\,p(1-p)}{(\alpha-p^2)^2}.
 \tag{4}
$$

For example $p\le0.30$ and every nontrivial coefficient at most $1.18\cdot10^{-8}$ in modulus on incoming draws 128–404 would give total exception below $10^{-12}$ at $\alpha=0.18$ on the 277 next entries. This follows by predictable stopping and a union bound if the hypotheses hold until first exit. Any separate failure of those hypotheses needs its own charge. These are Fourier coefficients of the *void indicator*, distinct from Part 219's coefficients of the ball count. The estimate makes explicit which prefix information would suffice.

Density alone gives no such concentration for this correlation. In $H=\mathbb F_{3329}$, take $A$ to be 998 consecutive residues. It has density below 0.30. For each of the 797 shifts of centered magnitude at most 398 the intersection has at least 600 points, so $C(u)>0.18$ with probability at least $797/3329>0.2394$. Translating the interval does not affect the calculation. This tests the correlation bound on finite sets. It asserts neither that this interval is a reachable geometric void nor that (2) is attained.

## Loss over a block of draws

Fix any incoming prefix $a\le405$. Defer the columns $a,\ldots,405$, writing $l=406-a$ and $m=d+l$. In the frame frozen *before* $a$, the appended lattice consists of $(y,k)\in K\times\mathbb Z^l$ satisfying $[y]=\sum k_j U_j$, where the $U_j$ are independent uniform on the old $H$. A future witness of nonzero last height has a lift of this form with $k\ne0$, because freezing through 404 leaves the last coordinate untouched. Consider the sufficient test that looks for such a witness already inside the radius-$L$ ball in this frame. We can even allow every $k\ne0$, enlarging its success event.

**Block first moment.** At any $0<L<q$, its conditional success probability is at most

$$
 B_a(L)=\frac{(2\pi e L^2/m)^{m/2}}{V_n g_a^n}
 \left(1+\frac{2e^{-v}}{1-e^{-3v}}\right)^m,\qquad
 v=2\pi^2L^2/m .
 \tag{5}
$$

For fixed $(y,k)$ in the test, some $k_j\not\equiv0\pmod q$. Its incidence probability is $1/|H|$, without any joint-incidence hypothesis. Sum over fixed pairs and enlarge the deterministic grid count to the full ball. Bound its indicator by $e^{m/2}e^{-m\|\cdot\|^2/(2L^2)}$. Poisson summation on $K\times\mathbb Z^l$ gives the prefactor since $|H|\det K=V_n g_a^n$. Its dual lies in the ambient integer grid, as $K^*=F^\perp\cap\mathbb Z^N$. Some $m$ coordinate rows are injective on the dual span. Dropping the other coordinates bounds its theta sum by the $m$-th power of the integer-line theta sum, which gives (5) using $j^2\ge1+3(j-1)$ for $j\ge1$. This is the grid majorant of [Part 217](wall1_long_winner_ceiling.md), used *before* the intervening columns are revealed.

To bound $g_a$ from below, start with $x_1=(400\log q-\log V_n)/n$ and iterate $x_{i+1}=x_i-\min(\log q,x_i+\log h)/n$. The update is increasing on both branches, and $s_i\le\min(q,hg_i)$, so $\log g_a\ge x_a$ by induction. The table uses this floor and the fixed radius $L=t\cdot35.0743$. Entries are upper bounds on $\log_{10}B_a$. The radius covers the draw-405 threshold on the relevant late-crossing corridor of [Part 225](wall1_raw_graph_winner_cap.md). The probability calculation is conditional only on the prefix at $a$.

| Incoming draw $a$ | Block dimension $m$ | $t=1.10$ | $t=1.15$ |
|---:|---:|---:|---:|
| 129 | 782 | −404.62 | −389.53 |
| 200 | 711 | −255.10 | −241.38 |
| 300 | 611 | −88.30 | −76.50 |
| 350 | 561 | −21.78 | −10.95 |

At draw 129, (5) also gives $B_{129}(122)<10^{-13.64}$. Outside an event of conditional probability below this bound, every lift using a deferred column has norm $>122$ in the draw-129 frame. Hence if $g_{405}\le35.0743$, **every** final nonzero-height witness of length at most $1.10g_{405}$ must lose more than $89.998\%$ of its squared norm to the 276 directions frozen on draws 129–404. The captured fraction is greater than $1-(1.10\cdot35.0743/122)^2$ by orthogonality of the successive Gram–Schmidt directions, for every lift at once. It is a joint implication under the original law. It does not divide the exception by the probability of entering the corridor. An entirely old horizontal witness is outside this assertion. The calculation quantifies the loss of using only nonexpansiveness in (1) over the block. It leaves the probability of effective projection onto the selected directions open.

## What the proposed 0.18 ceiling would buy

At $t=1.10$, the pointwise cap and a 0.18 tail alone give the scalar fourth-moment majorant $0.82(1.10)^4+0.18h^4>1.8300$. The (B) threshold is 1.7860. Condition (C) uses 0.126 through draw 380. A ceiling of **0.18 through draw 405**, starting at 129, suffices in the same direct moment calculation as (C). For terminal index $j=395,\ldots,405$, put $u_i=(505/506)^{j-i}$, $F_p(u)=(1-p)1.10^u+ph^u$. In the positive $j$-th summand of Part 225 equation (6), the ratio of the new bound to the published C bound is

$$
 \prod_{i=129}^{380}\frac{F_{.18}(u_i)}{F_{.126}(u_i)}
 \prod_{i=381}^{j}\frac{F_{.18}(u_i)}{h^{u_i}}.
$$

The common prefix cancels. Direct interval multiplication gives a ratio below 0.832 for each of the eleven entries. The new sum is therefore below $0.832\cdot6.296\cdot10^{-11}$. Adding a single predictable-exit charge of $10^{-12}$ would give **less than $5.339\cdot10^{-11}$** against the $6.485\cdot10^{-11}$ allowance. The longer window is material to this implication. [Part 225, direct residual estimate](wall1_raw_graph_winner_cap.md)

Equations (3)–(5) prove a two-radius drift inequality, a sufficient conditional concentration estimate and a loss for iterating the unprojected test. The shell and Fourier hypotheses on the actual selected prefixes, a reachable gated counterexample, and the unconditional exceptional-history probability remain open.

## Interval verification

Run the embedded verifier from the existing scripts directory. This keeps the deliverable in one file.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_inductive_typicality.md | python -B -)
```

```python
from math import factorial
from mpmath import iv

iv.dps = 65
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
n, d, q = 506, 505, 3329
V = iv.pi**253 / factorial(253)
h = sqrt(I('56.2142')) * exp(log(V)/n)
t = I('1.10')
R = 35*t * exp(-log(35*h)/n)
assert I('38.206') < R < I('38.208')
b = sqrt(R**2-2)
ratio = (b/sqrt((35*t)**2-1))**d
assert I('.01765') < ratio < I('.01767')
assert I('.24425') < sqrt(I('.18'))-I('.18') < I('.24427')
assert 277*I('1.18e-8')**2*I('.21')/I('.09')**2 < I('1e-12')
assert I(600)/q > I('.18') and I(797)/q > I('.2394')

bounds = {129: ('-404.62','-389.53'), 200: ('-255.10','-241.38'),
          300: ('-88.30','-76.50'), 350: ('-21.78','-10.95')}
def log10_bound(m, x, L):
    v = 2*iv.pi**2 * L**2/m
    theta = 1+2*exp(-v)/(1-exp(-3*v))
    return (I(m)/2*log(2*iv.pi*exp(1)*L**2/m)
            + m*log(theta)-log(V)-n*x)/log(10)

Q = log(q)
x = (400*Q-log(V))/n
for i in range(1,351):
    m = d+406-i
    if i in bounds:
        for threshold, upper in zip(('1.10','1.15'), bounds[i]):
            assert log10_bound(m, x, I(threshold)*I('35.0743')) < I(upper)
    if i == 129:
        assert log10_bound(m,x,I(122)) < I('-13.64')
        assert 1-(t*I('35.0743')/122)**2 > I('.89998')
    Hx = log(h)+x
    assert Hx < Q or Q < Hx
    x -= min(Q,Hx)/n  # monotone cap update on log GH

assert I('.82')*t**4 + I('.18')*h**4 > I('1.8300')
def F(p,u):
    return (1-p)*t**u + p*h**u
for j in range(395,406):
    mult = I(1)
    for i in range(129,j+1):
        u = (I(d)/n)**(j-i)
        denominator = F(I('.126'),u) if i<=380 else h**u
        mult *= F(I('.18'),u)/denominator
    assert mult < I('.832')
assert I('.832')*I('6.296e-11')+I('1e-12') < I('5.339e-11')
print("Verified radius, concentration, block, projection and budget bounds.")
```

## Audit

**Confirmed for the stated no-lookahead law.** The embedded 65-digit interval verifier passed. The one-step estimate, volume ratio, projection-loss implication and conditional residual budget require no numerical correction.

**One-step drift.** Fix the full incoming history. Here $p(b)$ counts the fraction of cosets of $M$ in $K$ whose nearest representative has norm strictly greater than $b$. Given $U=u$, the second raw column still gives a uniform $V$ on the old $H$. The map $v\mapsto[Q_u(v,0)]$ pushes this law to the uniform law on its image $H'$, by equal fiber sizes. Thus the conditional miss at the branch radius is exactly $P'(u)$. If either $v$ or $v+u$ has an old representative of norm at most its respective $b_j$, attaching offset $j=0$ or $1$ gives squared length at most $R^2-1$ before $Q_u$. The selected projection can only shorten that representative, and $R\le tg'$. This proves the event inclusion for every branch, including ties. For fixed $u$ the two old tests can be correlated. Averaging over $u$ gives the product because $(u,v)\mapsto(v,v+u)$ is a bijection of $H^2$, with inverse $(x,y)\mapsto(y-x,x)$. This proves (3) at its two stated radii. Contraction at the moving threshold still requires control of the intervening shell.

**Volume and projection.** At $g=35$, $t=1.10$, the horizontal dimension is 505, giving $(b_1/\sqrt{(tg)^2-1})^{505}\approx0.017660026$, or $1.7660\%$ of the larger ball's volume. At draw 129 the unprojected block has dimension $505+277=782$. Every fixed candidate with $k\ne0$ and norm at most 122 has a coefficient invertible modulo $q$, so its incidence probability is $1/|H|$. Summing before any freeze gives $\log_{10}B_{129}(122)\approx-13.646554$. On the complement of that single short-lift event, every lift of a final nonzero-height witness has norm greater than 122, since its last coordinate survives all 276 freezes. For each lift, Pythagoras gives a removed fraction greater than $1-(38.58173/122)^2=0.8999899294\ldots$ when the two final bounds on $g_{405}$ and witness length hold. The exception is measured given the incoming draw-129 history. The corridor enters only in the implication.

**Residual budget.** Part 225's direct sum uses $j=395,\ldots,405$ for hits on draws 396–406. The largest ratio of corresponding summands is about $0.83138674$ at $j=395$. Thus the stated comparison, including one predictable-exit charge, gives $Z_{\rm rem}<0.832(6.296\cdot10^{-11})+10^{-12}=5.338272\cdot10^{-11}$. As a separate check, retaining Part 225's prefix through 128 and substituting $F_{.18}$ into each of its eleven moment bounds gives a sum below $9.287\cdot10^{-12}$ before the exit charge. Both calculations require the conditional tail ceiling at every surviving entry from 129 through 405 and a bound on the probability of any exit over the whole window. Establishing those hypotheses remains open.
