# How far fresh marks control the late plane hits

**Partial result for the width-506 chain.** On draws 396–406 the joint mass of vertical residual hits with incoming $g\ge34.807$ is below $6.4470\cdot10^{-11}$. Choosing $g\ge34.875$ instead costs less than $2.4014\cdot10^{-11}$ and leaves more than $4.0836\cdot10^{-11}$ for smaller scales. On the horizontal side the residual mixed class on draw 403 costs less than $2.880\cdot10^{-11}$, including all incoming scales. The full vertical and horizontal ceilings remain open. All probability estimates below refer to the finite chain before conditioning on selection or the two gates.

Counting more accurately has a demonstrable limit. On **every** incoming prefix with $g\le32.5$ in the eleven-draw range, the exact mean number of height-one candidates in the residual length shell exceeds 118. This includes only height one and keeps the strict lower length cutoff. It is a statement conditional on such a prefix. Its frequency, and the fraction of its marks that select a winner giving a qualifying plane, are unknown.

## The cutoff and the exact one-mark sum

Write $M=P L$, $K=P\mathbb Z^N$, $H=K/M$, $D=\det M=V_{506}g^{506}$, $a=1352/\sqrt3$, $R=\sqrt{\sqrt2 a}$, and $B=52/\sqrt3$. Here $V_d$ is unit ball volume. At the first residual vertical hit the old minimum exceeds $c=30.5$, the oriented winner has $1\le k\le12$, and $r_-(g)=\max(c,0.945g)<s\le R$. Use $g$ exclusively for the incoming scale. [Part 193 and its audit](wall1_z2_vertical.md#audit)

The recurrence for $\log D$ starts at $400\log q$ and updates $L$ to $\max(L-\log q,505L/506-\tfrac12\log56.2142)$. The incoming floors at draws 396, 401 and 406 are respectively $34.71350676\ldots$, $33.41938257\ldots$ and $32.18553678\ldots$. Attainment of these floors by surviving prefixes is unknown. The hard upper endpoint is $R/0.945=35.1587\ldots$. The interior number $35.15$ was a choice in evaluating $11(1.422743743939)(R/g)^{506}$, which grows by the inverse 506th power as $g$ decreases. The unrounded charge there is $6.57448019427\ldots\cdot10^{-12}$, slightly **above** the abbreviated $6.57448\cdot10^{-12}$. There is no change in height invertibility or GS recurrence at that point. [Part 212 audit](wall1_integrality_bound.md#audit)

For a basis of the dual integer section $K^*=F^\perp\cap\mathbb Z^N$ with Gram matrix $G$, put $A_G(x)=\#\{z\in\mathbb Z^{505}:z^\top G^{-1}z\le x\}$, zero for $x<0$. Exact preselection candidate multiplicity on a nonempty band, conditional on this prefix, is

$$
 m(G,g)=\frac1{|H|}\sum_{k=1}^{12}\big[A_G(R^2-k^2)-A_G(r_-(g)^2-k^2)\big]. \tag{1}
$$

Indeed the basis dual to the chosen basis of $K^*$ generates $K$, and $kU=[y]$ in $H$ has exactly one solution. A $g$-bin averages (1) over its **own prefix law**. A lower endpoint for $g$ supplies a uniform upper bound, but does not supply $G$ or that law. Equation (1) subtracts exact counts. Subtracting two upper bounds would give no shell bound. The integer denominators also matter: $qM^*\subset K^*\subset\mathbb Z^N$, whereas the primal quadratic form here is $G^{-1}$, generally with denominators from $\det G$. The verifier below includes a rational ellipsoid enumerator for supplied Gram data.

## A height-resolved upper estimate

For an $m$-dimensional projection of the cubic grid, let $2C_m(t)$ be the coefficient bounding its full radius-$t$ ball count by $2C_m(t)V_m t^m/\det K$. Use the 4096-bin formula (3) of Part 161 with $b=m$ and physical $z=t\sqrt{2\pi/m}$. The factor two restores the full ball, including both signs and the origin. This proof needs only that the dual section embeds by norm-decreasing restriction into $\mathbb Z^m$. It applies after any fixed rational orthogonal projection. Every theta factor in the formula decreases with $t$. [Part 161, Theorem 2](wall1_band_plane_hits.md#a-sharper-first-moment-for-the-lower-strip)

Put $S_n(r)=\sum_{k=1}^{12} V_{n-1}(r^2-k^2)^{(n-1)/2}/(V_n r^n)$. At $n=506,r=R$, $S_n(r)=0.3648847498\ldots$ and $C_{505}(\sqrt{R^2-144})<1.423$. Since $|H|\det K=D$, each eligible prefix has conditional hit probability at most

$$
  2(1.423)S_{506}(R)(R/g)^{506}<1.039(R/g)^{506}. \tag{2}
$$

This uses separate horizontal balls at the actual twelve integer heights. Keeping a large group $|H|=q^d$ divides each candidate weight by $q^d$ but increases the volume density of the candidate lattice by exactly $q^d$ at fixed $D$. Part 212 proves $d\ge115$ and squared frozen covolume $p_F\ge2^{99}$ on its regular late prefixes. The covolume is $\sqrt{p_F}\ge2^{99/2}$, and $\det K=1/\sqrt{p_F}$. Neither normalization leaves a further $q^{-1}$ or $2^{-99/2}$ in (2). The full Gram form still affects which candidates occur and share a mark. Equations (1) and (2) require no exception charge. [Part 212, equations (1)–(4)](wall1_integrality_bound.md)

## Determinant separation across eligible visits

**Lemma.** Start an interval of at most eleven freezes with incoming minimum $>c$, and suppose the first realized winner has length $>c$, for $c=26$ or $30.5$. At the end of every nonempty initial segment of this interval the incoming determinant from its start has decreased by a factor $>c$.

To prove this, keep the $j$ fresh unit axes in the coordinate system at entry. Lift the $j$ successive winners to the cumulative extension of $M$, using only coordinates available at their respective draws. Their Gram–Schmidt lengths are the actual winner lengths. Their generated lattice $J$ therefore has covolume $\prod_{h=1}^j s_h=D_{\rm start}/D_{\rm end}$. Its height image lies in $\mathbb Z^j$, with kernel a sublattice of the entry lattice $M$. If the kernel has rank $e>0$, extend a basis of the kernel by lifts of a height-image basis. Orthogonal projection from the kernel complement to the height axes contracts exterior volumes. Thus $\det J\ge\det(\ker)\det(\mathrm{im})\ge\det(\ker)$, using covolume one for the zero-dimensional image. For $e=1$ the kernel length is $>c$. For $2\le e\le11$, Minkowski's cube bound gives $\det(\ker)>(c/\sqrt e)^e>c$. If the kernel is zero, the square integer height matrix has full rank. It is triangular by the reveal order, so every newest-coordinate height is nonzero. Projection off earlier winners leaves that newest coordinate unchanged. All later winner lengths are at least one and the first exceeds $c$. This proves the claim in both cases, even when intermediate determinants increase.

**Summation under the prefix law.** Call a visit eligible if it meets predictable tests including $g\ge t$ and $\lambda_1(M)>c$. Register it after the draw when the winner has $s>c$. Suppose $p_i$, its conditional registration probability on eligible histories, is at least $1-\epsilon(t)>0$. For any nonnegative predictable charge $w_i$, the expected sum on eligible visits equals the expected sum of $w_i/p_i$ on registered visits, by conditional expectation. At consecutive registered visits, the incoming determinant ratio is $>c$ by the lemma. Hence for charges proportional to $D_i^{-1}$ their sum on **each path** is at most $c/(c-1)$ times their value at $V_{506}t^{506}$. This also holds conditional on any starting history for a suffix of the eleven draws. It uses the length test on the realized trajectory only after correcting by $p_i$.

For vertical visits take $c=30.5$. A failure to register requires a positive-height point through $c$, of conditional probability at most $\epsilon(t)=1.422743743939(c/t)^{506}$ by Part 193. Applying (2) gives the following cumulative bound, including the terminal and gate requirements by dropping them:

$$
 \Pr(Z_{\rm rem}\text{ event with }g\ge t)\le M(t):=
 \frac{30.5}{29.5}\frac{1.039(R/t)^{506}}{1-1.422743743939(30.5/t)^{506}}. \tag{3}
$$

| Minimum incoming $g$ | Upper bound from (3) |
|---:|---:|
| 35.15 | $4.513\cdot10^{-13}$ |
| 35 | $3.929\cdot10^{-12}$ |
| 34.875 | $2.4014\cdot10^{-11}$ |
| 34.8125 | $5.9517\cdot10^{-11}$ |
| 34.807 | $6.4470\cdot10^{-11}$ |
| 34.8 | $7.1377\cdot10^{-11}$ |

The rows are alternatives. Dyadic subdivision with no information on bin weights cannot charge each subinterval as a fraction of its width. Even the pathwise sum uses the largest inverse determinant, at the lowest possible visit. The last row already exceeds the entire allocation. Keeping the height label extends (3) to a larger portion of the residual. Write $w_k=2(1.423)V_{505}(R^2-k^2)^{505/2}/V_{506}$. For a fixed winning height $k$ the same proof gives the charge
$$
 \frac{c}{c-1}\frac{w_k}{t_k^{506}-1.422743743939c^{506}} .
$$
Each column below costs less than $2.8\cdot10^{-12}$. Use them only below $34.875$, where the cumulative charge above has already stopped.

| Winning height $k$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Minimum $g=t_k$ | 34.860 | 34.749 | 34.605 | 34.429 | 34.219 | 33.975 | 33.697 | 33.383 | 33.033 | 32.645 |

The union of $g\ge34.875$ at **all** heights and these ten extensions costs less than $5.2014\cdot10^{-11}$. In particular the height-12 extension covers the entire allowed scale on draws 396–404. The next calculation gives an obstruction for **exact** shell counts at the smaller heights.

## An explicit lattice-point discrepancy at height one

Set $d=505$, $b=d/2$, $\beta=(b+2)/(R^2-1)$ and $X(y)=\beta\|y\|^2-b$. The open cell $|X|<2$ at height one consists of vectors of lengths between $32.96314522\ldots$ and $R$. It is inside the residual length shell whenever $g\le34.36$. Weight points by $e^{-\beta\|y\|^2}$ and normalize their sum on $K$ by $\det K/(\pi/\beta)^b$. The continuum version of this finite measure makes $X+b$ a gamma variable of shape $b$ and rate one.

For frequencies $|u|\le4$, the absolute difference of their Fourier transforms at $u$ is at most

$$
 (1+u^2)^{-d/4}\left[\left(1+\frac{2e^{-v}}{1-e^{-3v}}\right)^d-1\right],\qquad
 v=\frac{\pi^2}{\beta(1+u^2)}. \tag{4}
$$

Complex Gaussian Poisson summation gives this expression after removing the dual origin and restricting $K^*$ injectively to $d$ integer coordinates. The phase from subtracting $b$ has modulus one. On $[0,1]$, $[1,2]$, $[2,4]$ use the left endpoint for the decreasing prefactor and the right endpoint for the increasing bracket. The respective errors are below $5.21\cdot10^{-7}, 2.13\cdot10^{-39}, 4.17\cdot10^{-56}$. This estimate is uniform in the embedded section, including its lift index. [Part 161 complex Gaussian argument](wall1_band_plane_hits.md) · [Regev, Gaussian transform and Poisson formula](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/FourierTransform.pdf)

Use the minorant $f(x)=(1-x^2/4)(\sin(x)/x)^4$ for the open-cell indicator, with the continuous value at zero. Its Fourier representation is supported in $[-4,4]$ with total variation at most $5/4$: sinc is the characteristic function of a uniform variable on $[-1,1]$, and $x^2\operatorname{sinc}^4x=\sin^2(x)\operatorname{sinc}^2x$, with the signed frequency measure of $\sin^2(x)$ of total variation one. Thus replacing the continuum integral of $f$ by the normalized grid sum costs less than $10^{-5}$. The density of $X$ exceeds $0.024$ on $[-1,1]$ and is everywhere below $0.027$ by the gamma density and its mode. In the central interval $f\ge(3/4)(5/6)^4$ by the sine Taylor bound. The negative tails cost at most $0.027\int_{|x|>2}(4x^2)^{-1}\,dx$. Consequently the normalized tilted **grid mass** of the cell exceeds

$$
 m_0=2(0.024)(3/4)(5/6)^4-0.027/4-10^{-5}>0.01060.
$$

Undo the tilt inside the cell, where $e^{\beta\|y\|^2}\ge e^{b-2}$. The exact conditional mean on height one in that cell is at least $m_0 e^{b-2}(\pi/\beta)^b/(V_{506}g^{506})$. For $g\le34.36$ this exceeds $6.9658\cdot10^{-11}$, above the entire $6.485\cdot10^{-11}$ vertical allocation. It exceeds **118** for $g\le32.5$ and **12,900** for $g\le32.2$. Every height-one candidate is primitive in its window. Even a perfect evaluation of (1) followed by the single-prefix first-moment inequality would give only the unit bound for $g\le32.5$. For example, even with the entire $6.485\cdot10^{-11}$ budget available, a sum of the *unclipped* shell means on eligible visits with $g\le32.5$ can fit only if their expected number is below $5.50\cdot10^{-13}$. A small *average* over the chain can still arise from the probability of visiting those prefixes, same-mark selection, the plane test, or subsequent gates. This is no lower bound on the mass of any residual event.

## What a second mark buys

At a fixed block entry let $U:\mathbb F_q^j\to H$ assign the $j$ unread displacements in the **entry** quotient. For prescribed lifts, let the columns of $T$ be their new-coordinate residues and let $C$ give the required old classes. If $\ker T\subseteq\ker C$, their simultaneous membership has probability $|H|^{-\operatorname{rank}T}$, and otherwise probability zero. Extend a basis of the image of $T$ to prove the count. Nonzero coordinates in two draws of **one** vector give one column of $T$ and at most one pivot. Recording two positive-height winners at two specified draws gives independent triangular pivots for fixed compatible lifts, but summing the two records also sums the candidate pairs. All vectors at a single draw must use the same $U$. [Part 201, block fibers](wall1_multistep_branch.md)

Here is an actual-law two-mark bound after summing candidates. Let $E_i(t)$ mean a vertical winner on draw $i$ with $g_i\ge t$, $30.5<s_i\le R$, $1\le k_i\le12$; this test drops the plane and terminal requirements. Equation (3) also bounds the probability of any $E_i(t)$ in a suffix conditional on its entry. Two occurrences imply that the earlier has $g_i>t c^{1/506}$, by determinant separation. Stop at the first $E_i(t c^{1/506})$ and apply the suffix bound to later draws: even if this first occurrence precedes both witnesses, at least one still lies later. Thus

$$
 \Pr(\text{at least two }E_i(t))\le M(t c^{1/506})M(t)\le M(t)^2/c.
$$

The respective bounds at $t=33.9$ and $t=34$ are $5.482\cdot10^{-11}$ and $2.782\cdot10^{-12}$. Iteration for three occurrences gives $M(t)^3/c^3$, below $1.746\cdot10^{-12}$ at $t=33.6$. In general the earliest of $m$ occurrences must satisfy $g>t c^{(m-1)/506}$ for $m>1$. Applying the suffix argument inductively gives $M(t)^m/c^{m(m-1)/2}$. No independence assumption on selected draws enters this product.

For one joint budget, take the height-dependent union above and add paths with two $E_i(34)$ or three $E_i(33.6)$. The total charge is below $5.6542\cdot10^{-11}$, leaving $8.308\cdot10^{-12}$ of the vertical allowance. This covers only residual hits lying on the indicated paths or in the indicated height/scale regions. A vertical first hit on draw 406 needs no later win. At an earlier hit the qualifying plane can survive projection by a later vertical winner regardless of its length, and a later horizontal winner outside its span preserves its rank. A proof that the residual requires two eligible wins, or a bound on the complementary single-win mass, is missing. Rank 115 (even at every pivot) settles neither question.

## Horizontal first hits

Use $Z_1$ here in the question's residual-budget sense: after the previously charged mixed cases and draws 155–171, the allowance for the wholly old term on 172–406 plus the remaining mixed term on 403–406 is $7.1275\cdot10^{-11}$. [Part 208, audit and budget](wall1_z1_terminal_law.md#audit)

**Mixed plane.** On the remaining mixed branch force projection off the pre-draw designated old shortest vector $v$, of length $26<s\le R$. Part 194 supplies a positive-height vector of length $<u=\sqrt{5a/4}$ in the resulting window of rank 505. Its height is the analogue of the vertical winner's height. At fixed positive height its horizontal part pins the projected mark, uniform on the projected group. Projection can lose at most one field dimension of the mark: the kernel on marks is the image of the lattice in the one-dimensional projection kernel, modulo its intersection with $M$. Even this smaller projected group has no spare factor after counting its grid. The full preimage grid for that group has covolume times group order $D/s$. Thus heights 1–12 have normalized upper coefficient $2(1.423) S_{505}(u)$ as in (2), this time using the 504-dimensional grid. For all heights $k\ge13$ inject $(y,k)\mapsto(y,k-12)$ into the positive part of the radius-$\sqrt{u^2-168}$ ball and use $C_{505}(\sqrt{u^2-168})<1.423$. This counts labels with their original weights and requires no winner at the translated point. The resulting per-prefix coefficient satisfies

$$
 2(1.423) S_{505}(u)+1.423(1-168/u^2)^{505/2}<1.015.
$$

Hence the mixed first-hit probability on draw 403 alone is below $1.015 R V_{505}u^{505}/D^*_{402}<2.880\cdot10^{-11}$. This leaves more than $4.2475\cdot10^{-11}$ for the wholly old term and mixed draws 404–406. At the draw-406 floor the same one-draw expression exceeds $2.56\cdot10^{-6}$. Alternatively, on all four draws with $g\ge t$ the registered-visit argument at $c=26$ bounds the mixed contribution by

$$
 \frac{26}{25}\frac{1.015 R V_{505}u^{505}}{V_{506}t^{506}}\frac1{1-1.422743743939(B/t)^{506}}.
$$

On these eligible old prefixes a winner through 26 would need positive height and is covered by the Part 193 count through $B>26$. At $t=32.875$ the last display is below $5.874\cdot10^{-11}$. This alternative includes all of draw 403 and some scales of the later draws; its overlap with the single-draw estimate must be counted only once. [Part 194, first-hit lengths and the mixed plane](wall1_z1_horizontal.md#first-hit-lengths-and-the-mixed-plane-estimate)

**Wholly old plane.** On a fixed incoming history the geometric test is a saturated old triple through $v$ of determinant at most $as$. Its fresh-height matrix has rank zero. If such a triple exists, the conditional joint test of its projection and the horizontal win has probability exactly the horizontal win fraction. For instance on a prefix with $s\le R$ and $g\ge35.15$ that fraction is at least $1-1.422743743939(R/35.15)^{506}>1-6.0\cdot10^{-13}$, since losing requires a positive-height competitor through $s$, including a possible tie. This is a pointwise implication before future gates and says nothing about how often the triple is present.

A later fresh mark can be pinned when a prescribed later lift has nonzero fresh height (for a projected test, in the projected group). The terminal event only asks that some plane qualifies. If the old plane survives, there is no prescribed such lift. If it dies, a replacement can itself be wholly old at its creation. Even the geometric two-step example in Part 208 has restart probability zero by its audit, so it supplies no numerical lower bound here. For an exact estimate both the mass of surviving first planes and the mass of terminal hits after loss must be included. For a first hit at 406 there is no continuation mark at all. The unresolved horizontal quantity is the history-weighted old triple incidence times the relevant win and continuation weights, together with the uncharged late mixed term.

## Reproduction

The interval verifier and exact counting routine are embedded to keep the change to one file. From the repository root, run the following in the existing research scripts directory. It checks the analytic enclosures with outward intervals and tests an exact rational shell enumerator on a non-diagonal projected grid. It does not enumerate the distribution of adaptive 505-dimensional Gram matrices.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_fresh_mark_extension.md | python -B -)
```

```python
from fractions import Fraction as F
from math import isqrt
from mpmath import iv

iv.dps = 55
I = iv.mpf
q = 3329
V = [I(1), I(2)]
for d in range(2, 507):
    V.append(2 * iv.pi * V[-2] / d)
a = 1352 / iv.sqrt(3)
R, B = iv.sqrt(iv.sqrt(2) * a), 52 / iv.sqrt(3)
u = iv.sqrt(5 * a / 4)
C, c = I('1.422743743939'), I('30.5')


def half_ball(dim, radius):
    # Part 161, eq. (3). Decreasing and increasing factors use opposite endpoints.
    z2 = radius**2 * 2 * iv.pi / dim
    width = I(8) / 4096
    total = I(0)
    for j in range(4096):
        x, y = j * width, (j + 1) * width
        v = iv.pi * z2 / (1 + y*y)
        theta = 1 + 2 * iv.exp(-v) / (1 - iv.exp(-3*v))
        total += width * (1 - x/8) * (1 + x*x)**(-I(dim)/4) * theta**dim
    J = (2 * iv.pi * iv.exp(1) / dim)**(I(dim)/2) / V[dim]
    return J * total / (8 * iv.sin(1)**2 * (1 - iv.exp(-I(1)/2)))


for dim, sq in [(505, R**2-144), (504, u**2-144), (505, u**2-168)]:
    assert half_ball(dim, iv.sqrt(sq)) < I('1.423')


def layers(n, r):
    return sum(V[n-1] * (r*r-k*k)**(I(n-1)/2) for k in range(1, 13)) / (V[n] * r**n)


assert I('0.3648847498') < layers(506, R) < I('0.3648847499')
assert 2 * I('1.423') * layers(506, R) < I('1.039')
assert I('1.423') * (2*layers(505, u) + (1-168/u**2)**(I(505)/2)) < I('1.015')
assert I('35.1587') < R/I('.945') < I('35.1588')
old_charge = 11*C*(R/I('35.15'))**506
assert I('6.57448019427e-12') < old_charge < I('6.57448019428e-12')


def vertical(t):
    return c/(c-1) * I('1.039')*(R/t)**506 / (1 - C*(c/t)**506)


for t, cap in [('35.15','4.513e-13'), ('35','3.929e-12'), ('34.875','2.4014e-11'),
               ('34.8125','5.9517e-11'), ('34.807','6.4470e-11'), ('34.8','7.1377e-11')]:
    assert vertical(I(t)) < I(cap)
assert vertical(I('34.8')) > I('6.485e-11')
height_floors = ['34.860', '34.749', '34.605', '34.429', '34.219',
                 '33.975', '33.697', '33.383', '33.033', '32.645']
for k, tk in enumerate(height_floors, start=3):
    wk = 2*I('1.423')*V[505]*(R**2-k*k)**(I(505)/2)/V[506]
    assert c/(c-1)*wk/(I(tk)**506-C*c**506) < I('2.8e-12')
assert vertical(I('33.6'))**3/c**3 < I('1.746e-12')
assert vertical(I('33.9'))**2/c < I('5.482e-11')
assert vertical(I(34))**2/c < I('2.782e-12')
assert old_charge/11 < I('6.0e-13')

horizontal_numerator = I('1.015') * R * V[505] * u**505
L = 400 * iv.ln(q)
for i in range(1, 407):
    g = iv.exp((L - iv.ln(V[506]))/506)
    floors = {396:'34.71350676', 401:'33.41938257', 406:'32.18553678'}
    if i in floors:
        assert I(floors[i]) < g < I(floors[i]) + I('1e-8')
    if i == 403:
        assert horizontal_numerator/iv.exp(L) < I('2.880e-11')
        assert g > I('32.875')
    if 396 <= i <= 404:
        assert g > I('32.645')
    if i == 406:
        assert horizontal_numerator/iv.exp(L) > I('2.56e-6')
    p, h = L-iv.ln(q), 505*L/506-iv.ln(I('56.2142'))/2
    assert p < h or h < p
    L = max(p, h)
t = I('32.875')
assert I(26)/25 * horizontal_numerator/(V[506]*t**506)/(1-C*(B/t)**506) < I('5.874e-11')

# Fourier error and the mass of the open height-one cell.
d, b = 505, I(505)/2
beta = (b+2)/(R**2-1)
cell_start = iv.sqrt(1+(b-2)/beta)
assert I('32.96314522') < cell_start < I('32.96314523')
assert cell_start > I('.945')*I('34.36') and cell_start > c
for lo, hi, cap in [(0,1,'5.21e-7'), (1,2,'2.13e-39'), (2,4,'4.17e-56')]:
    v = iv.pi**2/(beta*(1+hi*hi))
    err = (1+lo*lo)**(-I(d)/4)*((1+2*iv.exp(-v)/(1-iv.exp(-3*v)))**d-1)
    assert err < I(cap)


def density(x):
    return iv.exp((b-1)*iv.ln(b+x)-(b+x))/iv.gamma(b)


assert density(-1) < I('.027') and min(density(-1), density(1)) > I('.024')
m0 = 2*I('.024')*I(3)/4*(I(5)/6)**4-I('.027')/4-I('1e-5')
assert m0 > I('.01060')
for t, floor in [('34.36', I('6.9658e-11')), ('32.5', 118), ('32.2', 12900)]:
    assert m0*iv.exp(b-2)*(iv.pi/beta)**b/(V[506]*I(t)**506) > floor


# A_G from (1) for an exact rational squared radius (closed outer boundary).
def ball_count(gram, radius2):
    if radius2 < 0:
        return 0
    n = len(gram)
    lower = [[F(0) for _ in range(n)] for _ in range(n)]
    diag = []
    for i in range(n):
        for j in range(i):
            cross = sum(lower[i][k]*lower[j][k]*diag[k] for k in range(j))
            lower[i][j] = (F(gram[i][j])-cross)/diag[j]
        diag.append(F(gram[i][i])-sum(lower[i][k]**2*diag[k] for k in range(i)))
        assert diag[-1] > 0
        lower[i][i] = F(1)

    def count(coords, remaining):
        i = len(coords)
        if i == n:
            return 1
        center = sum((lower[i][j]*coords[j] for j in range(i)), F(0))
        p, h = center.numerator, center.denominator
        bound = remaining*diag[i]*h*h
        delta = isqrt(bound.numerator // bound.denominator)
        total = 0
        for z in range(-((delta-p)//h), (p+delta)//h+1):
            offset = z-center
            total += count(coords+[offset], remaining-offset**2/diag[i])
        return total

    return count([], F(radius2))


# K* basis (1,-1,0),(0,1,-1). Compare every test to a brute-force exact shell.
G = [[2,-1],[-1,2]]
for h in range(-1, 31):
    brute = sum(2*(x*x+x*y+y*y) <= h for x in range(-10,11) for y in range(-10,11))
    assert ball_count(G, F(h,3)) == brute
print('Verified height layers, visit bounds, mixed-draw charges, shell discrepancy and rational enumeration.')
```

## Audit

**Verdict.** All three probability bounds hold under the original width-506 chain law. The height-one lower bound holds for the conditional mean over the unread mark on each specified prefix. The following intervals enclose the numerical bounds used in the proofs.

| Quantity checked | Independent outward enclosure |
|---|---:|
| Eleven-draw vertical majorant $M(34.807)$ | $(6.44697362,6.44697363)\cdot10^{-11}$ |
| Two-win majorant $M(34)^2/30.5$ | $(2.78189200,2.78189202)\cdot10^{-12}$ |
| Draw-403 residual mixed majorant $1.015R V_{505}u^{505}/D^*_{402}$ | $(2.87954219,2.87954220)\cdot10^{-11}$ |
| Height-one mean lower bound evaluated at $g=32.5$ | $(118.27389,118.27390)$ |

**Vertical counting and separation.** At each positive height through 12, multiplication by $k$ permutes $H$. Dividing the entire horizontal ball count by $|H|$ therefore gives its expected multiplicity before selection. Summing those twelve sections gives a coefficient in $(1.03846199,1.03846200)$ using the full-ball factor $2(1.423)$. A qualifying winner has $s>c$, so its incoming old minimum also exceeds $c$.

For two registered draws $i<j$, lift the winners on $i,\ldots,j-1$ into the extension of the entry lattice by those fresh coordinates. The determinant of their span lattice is $D_i/D_j$ in incoming-draw notation. A nonzero height kernel lies in the entry lattice and has covolume greater than $c$ by the rank-one or cube bound above. Its quotient projects contractively onto an integer height lattice of covolume at least one. With zero kernel, triangularity forces every newest height to be nonzero, so the product of winner lengths is again greater than $c$. This covers arbitrary intermediate draws. For an eligible prefix, the Part 193 short-candidate estimate gives $p_i\ge1-C(c/t)^{506}>0$ at the thresholds used. The conditional identity $\mathbb E[\mathbf1_{\rm registered}/p_i\mid\text{prefix}]=1$ on eligibility justifies summing reciprocal determinants on the registered path. It gives the same upper bound on each suffix conditional on its entry history. On a two-win path the earlier win has $g_i>34c^{1/506}$. Stopping at the first win above that threshold leaves a later qualifying win and justifies the product of the two suffix bounds.

**Horizontal mixed draw.** Part 194 fixes the old line before revealing the mark. Projecting carries the uniform mark onto the quotient of the projected grid by the projected old lattice, whose determinant is $D/s$. All candidate heights through $u$ are invertible. Translating heights $k\ge13$ by $-12$ lowers squared length by at least $168$ and preserves the weight per source label. The twelve sections plus this tail give a coefficient in $(1.01438659,1.01438660)$. Iterating the floor directly in covolumes from $3329^{400}$ gives incoming floors in $(32.91879713,32.91879714)$ on draw 403 and $(32.18553678203,32.18553678204)$ on draw 406. The draw-403 bound uses the floor after 402 updates and covers every incoming scale in the remaining mixed class.

**Height-one interpretation.** The Fourier minorant is nonpositive outside the open cell, and its frequency measure has total variation at most $5/4$. The three dual-tail estimates in (4) therefore change its integral by less than $10^{-5}$. Undoing the Gaussian tilt on the cell and dividing by $|H|$ yields the last row of the table. Its lower bound increases as $g$ decreases. Several candidates can have the same mark, so this certifies a mean exceeding 118 on each such prefix. The count for an individual realized mark, the frequency of these prefixes, and their contribution to the selected-hit probability remain undetermined.

The embedded verifier passed, as did the existing verifiers for Parts 207–212 and 214. An independent 75-digit interval calculation used gamma-function ball volumes, the recurrence in physical covolumes, and all 4096 bins at each of the three radii. No numerical correction to this note is required. Its upward correction of the abbreviated Part 212 charge is valid. The complementary vertical and horizontal residual masses remain open.
