# High-codimension sections under the selected chain law

**Partial result.** The joint probability of any terminal hit with syndrome codimension through 132 is below $10^{-533}$, including replacement planes. On draw 406, wholly old creation through 132 costs less than $10^{-707}$. In the mixed interval, the old-kernel test through 133 costs less than $10^{-149}$, and through 134 it costs less than $10^{-52}$ when $g\ge32.66$. These bounds count rational spaces before revealing any columns. They improve on R93 by using the rank of a rational matrix in each coordinate chart. [R93 and audit](wall1_wholly_old_mass.md)

There are two further charges which hold at **every** codimension. Selecting the prescribed flags in R93's codimension-400 annulus family has probability below $10^{-47.36}$, by a global comparison on draw 21. Mixed hits with $32.32<g\le32.33547$ cost less than $4.62329\cdot10^{-16}$. After all charges below, the available balance is greater than $4.02031\cdot10^{-12}$. A modified codimension-400 family stays below the draw-21 threshold and has at most 185 proposed long winners, yet its membership first moment exceeds $10^{356.13}$. The general high-codimension remainder is open.

## Counting rational graphs by matrix rank

Write $q=3329$, $T\subset\mathbb Q^N$, $k=\dim T$, $m=N-k$, $S=T\cap\mathbb Z^N$, and $h(T)=\det S$. For $\sigma(x,y)=x-Ay\bmod q$, put $d=400-\dim_{\mathbb F_q}\sigma(S)$. R93 gives the fixed-space probability $\Pr(d(T)\ge d)\le2q^{-d(k-400+d)}$. A hit with $\det(L\cap T)/q^{400}\le B$ at exact deficiency $d$ has $h(T)\le H=q^dB$. The following count applies with deterministic $B$ and $H\ge1$. At $H<1$ the list is empty.

Choose $k$ coordinate axes giving an isomorphism on $T$. In this chart $T$ is the graph of a rational $m\times k$ matrix $X$. Denote $\epsilon=.01$, $Z=400$, $\beta=.710$, and set
\[
 f_k(u)=\frac{2\sqrt{13}(\sqrt{13}+\sqrt\pi)^k}{\Gamma((k+1)/2)}
       +\left(1+\frac{2e^{-13}}{1-e^{-39}}\right)^k\beta^u.
\]
Fix an integer $1\le r<\min(k,m)$. We count the two possible rank ranges separately in each chart.

**Two coordinate bases.** Suppose the current graph has $p$ appended rows, at least $u$ of which are independent. There are two coordinate bases of size $k$ differing in $u$ positions. Keep the original axes as the first basis. Replace $u$ axes corresponding to a nonsingular $u$-column minor of the independent rows by those rows for the second basis. For the current integer section $S_p$, put $\theta(v)=\sum_{j\in\mathbb Z}e^{-vj^2}$. Then
\[
 \sum_{x\in S_p} e^{-v\|x\|^2}\le \theta(v)^{k-u}\theta(2v)^u .
\]
Indeed, write $C$ for the common coordinates, and $D,D'$ for the two disjoint sets of remaining coordinates. In the Gaussian discard coordinates outside their union. Apply Cauchy–Schwarz to the two factors whose squared weights put coefficient one on $C$ and two on $D$ or $D'$. Restriction to either coordinate basis injects $S_p$ into $\mathbb Z^k$, proving the bound.

For every positive integer $n$ and $s\ge k+1$ this gives
\[
 \sum_{w\in S_p^*}(1+\|w/n\|^2)^{-s/2}
 \le h(S_p)n^k f_k(u),\qquad h(S_p)=\det S_p. \tag{1}
\]
To see this, decrease $s$ to $k+1$ and use its gamma integral with variable $t$. Gaussian Poisson summation gives the factor $h(S_p)n^k(\pi/t)^{k/2}$ and the Gaussian sum on $S_p$ with exponent $\pi^2n^2/t$. Decrease $n$ to one in that exponent. For $t\ge13$, the ratio $\theta(2\pi^2/t)/\theta(\pi^2/t)=2^{-1/2}\theta(t/2)/\theta(t)$ is below $.710$. The common factor after reverse Poisson is $\theta(t)^k\le(1+2e^{-13}/(1-e^{-39}))^k$. For $0<t<13$ use $u=0$ and $\theta(t)\le1+\sqrt{\pi/t}$. Integration gives the first term of $f_k$. The small-$t$ term carries no factor $\beta^u$. [R93, graph extension inequality](wall1_wholly_old_mass.md#an-unconditional-union-over-rational-subspaces) · [Gaussian Poisson formula](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/FourierTransform.pdf)

**Rank at least $r$.** Choose $r$ independent rows first, at cost $\binom mr$, using their original relative order. After $p$ rows, (1) applies with $u=\min(p,r)$. A row of least denominator $n$ over the current section, represented by $w/n$ in its dual coordinates, multiplies the height by $n\sqrt{1+\|w/n\|^2}$. Thus the sum of inverse $s$-powers of child heights is at most $h(S_p)^{1-s}f_k(u)\zeta(s-k)$. Iterate backwards starting at $s=N+\epsilon$. The product of zeta factors is at most $101e^{1.2}<Z$ by the R93 estimate. For a fixed chart the resulting height count is at most
\[
 Z\binom mr H^{N+\epsilon}\prod_{p=0}^{m-1}f_k(\min(p,r)). \tag{2}
\]

**Rank $j<r$.** Write $K=\ker X$ and $Y=\operatorname{im}X$. Then
\[
 h(K)h(Y)\le h(T). \tag{3}
\]
Choose a basis of the primitive integer section of $K$ and extend it to a basis of $S$ in the graph. This is possible since the kernel of the image map is saturated. In the exterior product of that basis, take the component with $k-j$ original axes and $j$ appended axes. Its norm is $h(K)$ times the covolume of the image of $S$ in $Y$. The latter lattice has positive integer index in $Y\cap\mathbb Z^m$. Orthogonality of the exterior-coordinate components proves (3).

For a fixed $K,Y$, choose deterministically $j$ original coordinate units whose classes span $\mathbb Q^k/K$, and $j$ output coordinates giving a basis of $Y^*$. The corresponding $j\times j$ submatrix determines $X$. Its graph height is at most $h(T)$. In fact the Plücker coordinates of $T$ in this chart are a common multiplier times all minors of $X$, including the empty minor 1. Restricting this integer vector to the minors of the submatrix and dividing by their gcd gives its primitive graph coordinates. Both operations decrease or preserve the norm.

With $s_0=\max(k,m)+\epsilon$, (3) bounds the number of kernel/image pairs by $H^{s_0}$ times the product of their inverse-height sums at $s_0$. For $K$ use dimension $k-j$ in ambient dimension $k$. For $Y$ use $Y^\perp$ of dimension $m-j$ in $\mathbb Q^m$, with the same primitive height by the exterior Hodge star. The one-basis calculation above gives each chart sum at its ambient dimension plus $\epsilon$ at most $Zf_{\rm rank}(0)^j$. Increasing the exponent preserves the bound. The square submatrix has a specified chart in dimension $2j$, so its height count is at most $Zf_j(0)^jH^{2j+\epsilon}$. Together these give the following low-rank count **in the original chart** for $j\ge1$:
\[
 Z^3\binom kj\binom mj
 [f_{k-j}(0)f_{m-j}(0)f_j(0)]^j H^{\max(k,m)+2j+2\epsilon}. \tag{4}
\]
At $j=0$ there is exactly one graph. The verifier bounds it by $H^{\max(k,m)+2\epsilon}$ to use a common cumulative estimate. The rational rank in (2)–(4) and the deficiency $d$ over $\mathbb F_q$ are distinct.

## Joint charges

Add (2) and (4) over the appropriate ranks, then multiply by $\binom Nk$ and the fixed-space probability. The verifier upper-bounds the low-rank sum by $r$ times its largest term and the sum of the two branches by twice their maximum. To sum over $d$ it uses the ratio of each resulting exponential envelope at successive deficiencies. For an exponent $a_0$ of $H$ that ratio is $q^{a_0-(k-400+2d-1)}$ from $d-1$ to $d$. Where it exceeds $q^{100}$, the final bound divided by $1-q^{-100}$ suffices.

Use $a=1352/\sqrt3$, $R=(\sqrt2a)^{1/2}$, $D_i=V_{506}g_i^{506}$, and the period/Hermite determinant floor $D_i^*$. The terminal test uses $B=a\sqrt{56.2142}(D_{406}^*)^{-505/506}$. Wholly old creation uses $B=aR/D_i^*$. On the mixed strip $g\ge z$ use $B=29.2R/(V_{506}z^{506})$ for the old kernel, winner and 405 frozen directions. All three are determinant bounds on the full specified inverse image. [Part 221](wall1_z1_last_pieces.md) · [R93 audit](wall1_wholly_old_mass.md#audit)

| Witness | $(N,k)$ | $r$ | Through $d$ | $\log_{10}$ cumulative majorant | $\log_{10}$ single majorant at next $d$ |
|---|---|---:|---:|---:|---:|
| Any terminal hit | $(911,408)$ | 144 | 132 | $(-533.85,-533.84)$ | $(1604,1605)$ |
| Wholly old creation, 406 | $(910,408)$ | 144 | 132 | $(-707.60,-707.59)$ | $(1430,1431)$ |
| Mixed old kernel, $g>32.32$ | $(910,407)$ | 144 | 133 | $(-149.08,-149.07)$ | $(1985,1986)$ |
| Mixed old kernel, $g\ge32.66$ | $(910,407)$ | 145 | 134 | $(-52.63,-52.62)$ | $(2073,2074)$ |

The last column uses $r=146,146,146,147$, respectively. It measures the loss in this certificate at the next integer. For each of the 234 earlier wholly old creation draws $172$–$405$, the cumulative cost through at least 132 is below $10^{-30}$. At draws $172,200,250,300,350,380,405$ the same allowance covers through $263,246,215,187,160,145,132$, respectively. R93's larger previously paid ranges at other early draws still apply.

The scale information can also pay higher codimensions at draw-406 wholly old creation. With $g\ge32.5,34,36,40,60,100$, respectively, the cutoffs $133,137,142,152,193,258$ each cost less than $10^{-30}$ using $r=144$ and $B=aR/(V_{506}g_{\min}^{506})$. These are joint upper bounds for the indicated scale ranges. Their proof requires no assumption about how often the chain reaches a given scale.

## The global comparison for the codimension-400 family

In R93's annulus construction, use the lower envelope immediately **before** draw 21. The proposed length on that draw is greater than
\[
 t=\sqrt{r_{21}^2-1}-\sqrt{499}-1\in(3289.03206,3289.03207).
\]
Every raw vector with nonzero last coordinate projects to a nonzero candidate, since all earlier frozen vectors have zero in that coordinate. Its projected length is at most its raw length. Thus selecting the R93 prefix requires absence of every such raw candidate of length $\le t$. Part 222, equation (3), gives on the original law, for $G_N=(q^{400}/V_N)^{1/N}$,
\[
 \Pr(\text{the selected prefix belongs to this family})
 \le\Pr(s_{21}>t)\le4(G_{526}/t)^{526}<10^{-47.36}.
\]
This uses only the annulus on draw 21 and applies to all subsequent gate and first-hit restrictions. The same charge covers **all** selected histories with $s_{21}>t$, at any deficiency. [R93 construction](wall1_wholly_old_mass.md#how-large-the-wholly-old-membership-sum-can-be) · [Part 222, raw ball lemma](wall1_long_winner_handle.md#a-count-before-shortest-vector-selection)

One can also compare first moments. On a realization of the selected flag through 405 the prefix span is fixed. For each of the three prescribed anchor patterns, two compatible perturbations would differ after projection by a vector of the incoming graph lattice of norm at most 1. On a family hit the selected draw-406 winner has length at least $\sqrt{842}$, so this difference vanishes. A projected perturbation determines its lift modulo the frozen span. There is therefore at most one R93 full space per realization with this selected prefix and the prescribed winning triple. Dividing the selected first moment by the R93 membership sum shows that the retained membership-weighted fraction is below $10^{-10210.77}$. This pays for the selection of the prescribed flags. A realization reaching the same rational space along a different flag would need its own test.

### A family below the draw-21 threshold

Keep R93's 405 private pivots, active grid of rank 499, three anchored vectors, and membership equations. In its radius recursion, impose two additional upper bounds **before** the factor $.9$ on draws 399–405. On $i\le67$ use $G_{505+i}$. On $i\le220$ also use $1.10\exp((l_{i-1}-\log V_{506})/506)$, where $l_{i-1}$ is the running lower bound on $\log D_i$. The latter cap ensures $s_i\le1.10g_i$ for each proposed prefix through 220, so there can be at most 185 long winners among the first 405. On draw 21 the cap $G_{526}<2666.13$ puts all these proposed winners below $t$.

For clarity, write $\delta=\sqrt{499}/2$, $c_i=\sqrt{r_i^2-1}$ and $t_i=c_i-2\delta-1$. In each annulus the proposed lengths satisfy $t_i<s_i\le r_i$. Start $l_0=b_0=400\log q$ and update $l_i=l_{i-1}-\log r_i$, $b_i=b_{i-1}-\log t_i$. Voronoi covering in the projected active grid gives the weighted number of children per parent at least
\[
   e^{-b_{i-1}}V_{499}\big[(c_i-\delta)^{499}-(c_i-\delta-1)^{499}\big].
\]
The three final centered perturbations each supply another factor $e^{-b_{405}}V_{499}(1/4)^{499}$. R93's primitivity, distinctness and ternary-area proofs use the private pivots and the final perturbation radii, which this construction preserves. Multiplying these factors gives a membership first-moment lower certificate with $\log_{10}$ in $(356.13715,356.13717)$. The incoming $g_{406}$ is between 33.92816 and 38.71029. These are wholly old proposed crossings, with all 405 suffix pivots. Even the full $4.02\cdot10^{-12}$ allowance would require a retained fraction below $10^{-367.53}$ in a selection-weighted first moment for this family. The estimate gives no lower bound on the probability of a selected hit.

## A mixed strip at every deficiency

Let $E$ be any event of probability at least $p=10^{-7}$. Part 222 gives $\Pr(s_i>x)\le4(G_N/x)^N$ for $1690\le x\le q$, $N=505+i$ in its stated range. When $G_N\ge1690$, integrating the bound on the conditional tail of $\log s_i$ gives
\[
 \mathbb E[\log s_i\mid E]\le \log G_N+\frac{\log(4/p)+1}{N}.
\]
Indeed, above $x_0=G_N(4/p)^{1/N}$ the conditional tail is at most $(x_0/x)^N$ up to $q$ and zero thereafter. If $x_0\ge q$ the period bound suffices. This argument conditions on a single event throughout and allows arbitrary dependence between draws.

Start $L_1=400\log q$. If $L_i\le\mathbb E[\log D_i\mid E]$, then $L_{i+1}$ can be taken as the maximum of $L_i-\log q$, $(505/506)L_i-\tfrac12\log56.2142$, and $L_i$ minus the preceding raw-vector cap where applicable. This follows from the exact update $\log D_{i+1}=\log D_i-\log s_i$ and the two pathwise caps. Using the raw bound only through draw 60 gives $\exp((L_{406}-\log V_{506})/506)>32.33547$. Taking $E=\{g_{406}\le32.33547\}$ proves $\Pr(E)<10^{-7}$. The crossing is measurable before mark 406. On eligible prefixes with $g>32.32$, Part 221 bounds the conditional fresh mixed charge by $4.62329\cdot10^{-9}$. Multiplication proves the claimed $4.62329\cdot10^{-16}$ joint charge, without conditioning the last mark on a future gate. [Part 221, fresh-mark weight](wall1_z1_last_pieces.md#retaining-the-fresh-mark-weight)

## What high deficiency forces

For any rational $T'\subset T$, $\sigma(T'\cap\mathbb Z^N)\subseteq\sigma(T\cap\mathbb Z^N)$. Thus $d(T')\ge d(T)$. In particular **every** subsection of a deficiency-400 space still has deficiency 400, irrespective of its Rankin height. Even if one is allowed to replace directions, two spaces with intersection $U$ obey $d(T')\ge d(T)-\dim(T'/U)$, by extending a basis of the saturated section of $U$. Reducing 400 to 128 takes at least 272 independent new directions.

There is a genuine coordinate consequence. For $J=L\cap T$, reduction of $J$ modulo $q$ in the ambient grid is the kernel of $\sigma$ on $S/qS$, of dimension $k-400+d$. The graph code projects injectively to the inputs. With only $105+t$ inputs through cut $t$, the suffix rank is at least $\max(0,k-400+d-105-t)$. At draw-406 wholly old creation with $d=400$ this requires at least 303 suffix pivots after cut zero. R93 already has 405. The adaptive choice of the pivots still has to be accounted for.

The two whole-section Hermite tests alone have no $d$ dependence at fixed $B'=\det J/q^{400}$. Indeed $\det J=q^{400}B'$ and $\det(L^*\cap T^\perp)=B'$. As a numerical test take $k=408$, $N=910$, $g=32.5$, $s=29$, and plane area 770, so $B'=29\cdot770/(V_{506}32.5^{506})$. The Part 77 caps give upper bounds in $(2173.20,2173.21)$ and $(1.26927,1.26928)$ on the section and complementary dual minima, respectively. Both exceed the gate thresholds 250 and $R_0(405)<0.20000$. The integer height requirement $q^dB'\ge1$ holds for every $d\ge110$. These are scalar feasibility checks. The figures do not establish a reachable prefix or an integral section of exactly that height. A test on a smaller subspace or an individual matrix can have more force. [Part 205, both gates](wall1_doubly_gated.md) · [Part 206, terminal indices](wall1_raw_section_compression.md) · [Part 77 cap integers](wall1_lcz_all_widths.md#all-dimensions)

**Remaining mass.** Subtracting the displayed charges conservatively, even where they overlap R93, leaves more than $4.02031\cdot10^{-12}$. Unpaid wholly old histories require an uncharged creation and a terminal lift of deficiency at least 133, allowing the first plane to survive or be replaced. On $32.33547<g<32.66$ the mixed old-kernel deficiency starts at 134, and on $32.66\le g<32.75$ it starts at 135. All these histories can be restricted to $s_{21}\le t$. The target is an upper bound on their joint mass within the available balance. This note does not establish that bound. The syndrome has dimension 400, so deficiencies 401–405 are empty; 405 in the old construction counts suffix pivots.

## Reproduction

Run the embedded verifier from the research scripts directory. It uses outward intervals and creates no additional repository files.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_high_codim_sections.md | python -B -)
```

```python
from functools import lru_cache
from math import comb
from mpmath import iv

iv.dps = 55
I, ln, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
q = 3329
Q, ln10 = ln(q), ln(10)
eps, Z, b = I('.01'), I(400), I('.710')
alpha = I(505)/506
cap = ln(I('56.2142'))/2
V = [I(1), I(2)]
for n in range(2, 912):
    V.append(2*iv.pi*V[n-2]/n)
lv = ln(V[506])
a = I(1352)/sqrt(3)
R = sqrt(sqrt(2)*a)
assert 101*exp(I('1.2')) < Z
assert (1+2*exp(I('-6.5'))/(1-exp(I('-19.5'))))/sqrt(2) < b

def max_iv(*xs):
    # Interval extension of max, including overlapping or equal branches.
    return I([max(x.a for x in xs), max(x.b for x in xs)])

@lru_cache(None)
def constants(k):
    return (2*sqrt(13)*(sqrt(13)+sqrt(iv.pi))**k/iv.gamma(I(k+1)/2),
            (1+2*exp(-13)/(1-exp(-39)))**k)

@lru_cache(None)
def logf(k, u):
    e, h = constants(k)
    return ln(e+h*b**u)

@lru_cache(None)
def chart_constants(N, k, r):
    m = N-k
    assert 1 <= r < min(k, m)
    high = (ln(Z*comb(m,r)) + sum(logf(k,u) for u in range(r))
            + (m-r)*logf(k,r))
    low = [I(0)]
    for j in range(1, r):
        low.append(3*ln(Z)+ln(comb(k,j)*comb(m,j))
                   + j*(logf(k-j,0)+logf(m-j,0)+logf(j,0)))
    return high, low

def refined(N, k, logB, d, r):
    # Natural log majorant at exact d. Called only for nonempty height ranges.
    m = N-k
    h = d*Q+logB
    assert h > 0
    high, low = chart_constants(N,k,r)
    low_sum = ln(r)+max_iv(*(v+(max(k,m)+2*j+2*eps)*h
                              for j,v in enumerate(low)))
    total = ln(2)+max_iv(high+(N+eps)*h,low_sum)
    return ln(2*comb(N,k))+total-d*(k-400+d)*Q

floors = [None, 400*Q]
for i in range(1,406):
    L = floors[i]
    floors.append(max_iv(L-Q,alpha*L-cap))

def mixed(z):
    return ln(R*I('29.2'))-lv-506*ln(I(z))

termB = ln(a)+cap-alpha*floors[406]
oldB = ln(a*R)-floors[406]
def cumulative(N,k,B,d,r):
    # For all nonempty heights through d the forward multiplier in every
    # exponential envelope is >= q^100. Empty initial height ranges cost zero.
    assert max(k,N-k)-(k-400+2*d-1) >= 100
    return (refined(N,k,B,d,r)-ln(1-I(q)**(-100)))/ln10

def show(label, value):
    print(label, float(value.a), float(value.b))

for label,N,k,B,d,r,upper in [
    ('terminal',911,408,termB,132,144,'-533.84'),
    ('old 406',910,408,oldB,132,144,'-707.59'),
    ('mixed',910,407,mixed('32.32'),133,144,'-149.07'),
    ('mixed upper strip',910,407,mixed('32.66'),134,145,'-52.62'),
]:
    value = cumulative(N,k,B,d,r)
    show(label,value)
    assert I(upper)-I('.01') < value < I(upper)

for label,N,k,B,d,r,lo in [
    ('terminal next',911,408,termB,133,146,1604),
    ('old next',910,408,oldB,133,146,1430),
    ('mixed next',910,407,mixed('32.32'),134,146,1985),
    ('mixed upper next',910,407,mixed('32.66'),135,147,2073),
]:
    value = refined(N,k,B,d,r)/ln10
    show(label,value)
    assert lo < value < lo+1

# For earlier draws use the old height count where it is sufficient.
for i in range(172,406):
    N,k,d = 504+i,i+2,132
    B = ln(a*R)-floors[i]
    h = d*Q+B
    if h < 0:
        continue
    assert h > 0
    crude = (ln(2000*comb(N,k))+(N+eps)*h-d*(k-400+d)*Q
             -ln(1-I(q)**(-100)))/ln10
    if crude > -30:
        assert cumulative(N,k,B,d,144) < -30
    else:
        assert crude < -30

for i,d,r in [(172,263,20),(200,246,52),(250,215,60),(300,187,92),
              (350,160,108),(380,145,132),(405,132,116)]:
    assert cumulative(504+i,i+2,ln(a*R)-floors[i],d,r) < -30

# Direct finite sums also apply where the simple common ratio is too weak.
for z,cut in [('32.5',133),('34',137),('36',142),('40',152),
              ('60',193),('100',258)]:
    B = ln(a*R)-lv-506*ln(I(z))
    total = I(0)
    for d in range(cut+1):
        if d*Q+B < 0:
            continue
        total += exp(refined(910,408,B,d,144))
    assert total < I('1e-30')

# R93 family, using the lower envelope immediately before draw 21.
rad = sqrt(I('56.2142'))*exp(floors[21]/506)
assert rad < q
t = sqrt(rad**2-1)-sqrt(499)-1
def logG(N):
    return (400*Q-ln(V[N]))/N
joint = (ln(4)+526*(logG(526)-ln(t)))/ln10
assert 1690 < t < q
show('R93 winner threshold',t)
show('R93 selected probability log10',joint)
assert joint < I('-47.36')
assert I('3289.03206') < t < I('3289.03207')
assert joint-I('10163.4140') < I('-10210.77')

delta = sqrt(499)/2
lower = upper = 400*Q
mass = I(0)
for i in range(1,406):
    caps = [I(q),exp(cap+lower/506)]
    if i <= 67:
        caps.append(exp(logG(505+i)))
    if i <= 220:
        caps.append(I('1.10')*exp((lower-lv)/506))
    radius = -max_iv(*[-x for x in caps])
    if i >= 399:
        radius *= I('.9')
    if i == 21:
        assert exp(logG(526)) < I('2666.13') < t and radius < I('2666.13')
    c = sqrt(radius**2-1)
    inner, x = c-2*delta-1, c-delta
    assert inner > 1
    mass += ln(V[499])+499*ln(x)+ln(1-(1-1/x)**499)-upper
    lower -= ln(radius)
    upper -= ln(inner)
mass += 3*(ln(V[499])+499*ln(I('.25'))-upper)
show('modified R93 log10 membership certificate',mass/ln10)
assert I('356.13715') < mass/ln10 < I('356.13717')
assert (mass-ln(I('4.02e-12')))/ln10 > I('367.53')
assert exp((lower-lv)/506) > I('33.92816')
assert exp((upper-lv)/506) < I('38.71029')

# Conditional mean of log D on an arbitrary event of probability >= p.
p = I('1e-7')
L = 400*Q
for i in range(1,406):
    branches = [L-Q,alpha*L-cap]
    N = 505+i
    if i <= 60:
        assert logG(N) > ln(1690)
        mean_cap = logG(N)+(ln(4/p)+1)/N
        branches.append(L-mean_cap)
    L = max_iv(*branches)
gbar = exp((L-lv)/506)
show('conditional determinant floor in g units',gbar)
assert I('32.33547') < gbar < I('32.33548')
logB = ln(29*770)-lv-506*ln(I('32.5'))
raw = exp((I(781360932708)/10**9+400*Q+logB)/408)
dual = exp((I(1010175917271)/10**9+logB)/502)
rho = (exp((510*Q-ln(408000)-ln(V[910]))/910)-sqrt(910)/2)/q
assert I('2173.20') < raw < I('2173.21')
assert I('1.26927') < dual < I('1.26928')
assert I('.19999') < rho < I('.20000') and 109 < -logB/Q < 110
charge = ((234+6)*I('1e-30') + I('1e-530')+I('1e-705')
          +I('1e-148')+I('1e-30')+I('1e-47')+p*I('4.62329e-9'))
assert I('4.02078e-12')-charge > I('4.02031e-12')
```

## Audit

**Verdict.** The four joint probability bounds, the draw-21 flag charge, the modified-family membership lower bound, and the remaining balance hold under the stated chain law. No numerical correction is required. The mixed bounds apply to Part 218's residual hit on draw 406, with positive height 1–4 and old kernel generator of length in $(28.22,29.2)$.

The embedded interval verifier passed. Independently, I evaluated the ball volumes with $\log\Gamma$, updated the determinant in determinant units, and summed the majorant directly over every nonempty exact deficiency at 85-decimal-digit precision. The base-ten logarithms were $-533.84105830\ldots$ for the terminal lift through 132, $-707.59965089\ldots$ for wholly old creation on draw 406 through 132, $-149.07669578\ldots$ for the mixed old lift through 133, and $-52.62368233\ldots$ for the mixed old lift through 134 at $g\ge32.66$.

For (2), reordering an independent set of $r$ rows first gives two injective coordinate restrictions differing in $\min(p,r)$ positions at each parent. Cauchy–Schwarz gives the stated theta product, and the large-$t$ ratio contributes one factor of $.710$ per exchanged position. For (4), the exterior component with $j$ output directions gives $h(K)h(Y)\le h(T)$. Restricting to the selected minor coordinates and taking the primitive integer representative gives the square submatrix height bound. I also checked both height inequalities on 60 separate exact rational graphs with $2\le k,m\le4$, computing each squared height from the integer minors divided by their common gcd. These rational checks were performed separately from the embedded verifier's 60-draw interval recursion.

At exact $d$ the height list is deterministic, so the fixed-space probability applies before the union over charts. The terminal witness is the full inverse image of the plane present after draw 406. Its determinant bound uses all 406 frozen lengths and covers a replacement plane. For a mixed hit the counted object is the old lift of the kernel and winner through the preceding 405 freezes.

The R93 annulus forces $s_{21}>3289.03206157\ldots$. A raw graph vector with nonzero newest coordinate survives projection, so the original-law raw-ball inequality bounds the log probability of selecting the prescribed flag by $-47.36254422\ldots$ in base ten. This charge also permits restricting every unpaid history to $s_{21}\le t$. It covers a visit to the same rational space along a different flag only if that visit also satisfies $s_{21}>t$. In the modified family the first 220 proposed lengths obey $s_i\le1.10g_i$, leaving at most $405-220=185$ long proposals. Direct multiplication of the 405 annulus factors and the three final ball factors gave a membership lower certificate with base-ten logarithm $356.13715951948\ldots$. The probability of actually selecting those proposals remains open.

For the mixed strip, the conditional log-determinant floor on any event of probability at least $10^{-7}$ gives $32.33547171955\ldots$ in $g$ units. Consequently $\Pr(g_{406}\le32.33547)<10^{-7}$. This event is known before mark 406, so Part 221's fresh-mark bound gives the joint charge $<4.62329\cdot10^{-16}$ on the strip. Subtracting the verifier's rounded charges from $4.02078\cdot10^{-12}$ leaves more than $4.0203176709\cdot10^{-12}$.

The unpaid mixed old-lift deficiency lies in $[134,400]$ for $32.33547<g<32.66$, and in $[135,400]$ for $32.66\le g<32.75$. For wholly old histories both the creation lift and the terminal lift must have deficiency in $[133,400]$, subject to the stronger creation cutoffs already paid at individual draws and scales. These are necessary ranges. An upper bound on their joint mass within the remaining balance is still open.
