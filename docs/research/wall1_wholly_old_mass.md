# Counting the integer sections of a selected plane

**Partial bound under the original chain law.** Any terminal hit whose full inverse image has syndrome codimension at most 128 costs less than $10^{-505}$, summed over all such planes. This covers a wholly old plane that survives and a replacement after the first plane disappears. On draw 406 the wholly old *creation* test at the same codimension costs less than $10^{-683}$. For the outstanding mixed interval, the old kernel together with the frozen directions and the horizontal winner has codimension at most 129 with joint hit probability below $10^{-89}$. Codimension 130 also costs less than $10^{-36}$ on $32.68\le g<32.75$.

Higher codimensions remain open. A family of distinct wholly old integer sections of codimension 400 gives a membership first moment above $10^{10163.4140}$, even with the earlier column equations, the four terminal suffix ranks, and the local crossing of the ternary area threshold. Its fraction passing the global winner comparisons, first-hit exclusions and raw gates is unknown. The construction measures the loss from dropping those tests. The $4.02\cdot10^{-12}$ target for the full remainder is unresolved. [Part 221 and audit](wall1_z1_last_pieces.md#audit)

## An unconditional union over rational subspaces

Write $q=3329$, $L=\ker\sigma$ in $\mathbb Z^N$, $\sigma(x,y)=x-Ay\bmod q$, with 400 independent uniform rows of $A$. For a rational $k$-space $T$, set $S=T\cap\mathbb Z^N$, $h=\det S$, and $d=400-\dim\sigma(S)$. Then $\det(T\cap L)=q^{400-d}h$. Part 212 gives a lower bound $2^{99}$ on the **squared** covolume of the late frozen integer section off its stated exception. In fact its projected ambient grid has covolume $1/h_F$. A lower bound on $h_F$ gives no upper bound on the number of raw spaces across different histories. Here the hit gives an **upper** bound on $h$ once $d$ is specified. [Part 212, section identities](wall1_integrality_bound.md#which-gram-determinant-is-integral)

**Fixed-space probability.** For $0\le d\le400$ and fixed $T$,
\[
 \Pr(400-\dim\sigma(S)\ge d)\le 2q^{-d(k-400+d)}. \tag{1}
\]
Indeed $S/qS$ embeds in the ambient space. Let $b$ be its dimension supported purely on the 400 horizontal coordinates. Its syndrome there is a fixed $b$-space. A possible $d$-dimensional annihilator must be in the orthogonal of that space. If $d>400-b$ the event is empty. Otherwise there are at most $2q^{d(400-b-d)}$ choices by the finite Grassmannian product. On the other $k-b$ independent input directions a fixed annihilator imposes $d(k-b)$ independent uniform scalar equations. Multiplication gives (1), including when the right side exceeds one.

**Height count.** For $174\le k\le408$, $1\le N-k\le505$, $H\ge1$, the number of distinct rational $k$-spaces in $\mathbb R^N$ of height at most $H$ satisfies
\[
             N_k(H)\le 1000\binom Nk H^{N+0.01}.                  \tag{2}
\]
Choose $k$ coordinate axes on which projection is nonsingular and order them first. In this chart, adjoining one coordinate to a space with primitive integer section $S$ amounts to taking the graph of a rational linear form. Write the form as $x\mapsto\langle w,x\rangle/n$ for $w\in S^*$ and least positive denominator $n$. Its integral domain in $S$ has index exactly $n$ by minimality. The graph therefore has height $nh\sqrt{1+\|w/n\|^2}$. In an upper sum we can include every $w$ at each $n$.

For $s>k$ put $C_{k,s}=\sum_{z\in\mathbb Z^k}(1+\|z\|^2)^{-s/2}$. For each integer $n\ge1$,
\[
 \sum_{w\in S^*}(1+\|w/n\|^2)^{-s/2}\le h n^k C_{k,s}.         \tag{3}
\]
Use the gamma integral of $e^{-t\|w/n\|^2}$ against $e^{-t}t^{s/2-1}/\Gamma(s/2)$. Gaussian Poisson summation gives the prefactor $hn^k(\pi/t)^{k/2}$ and a sum over $v\in S$ with exponent $-\pi^2 n^2\|v\|^2/t$. Restriction to $k$ independent integer coordinates injects $S$ into $\mathbb Z^k$ and can only decrease norm. Bound the dual sum by the integral-grid sum with $n=1$ and apply Poisson there in reverse. All terms under the gamma integral are nonnegative. [Gaussian Poisson formula](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/FourierTransform.pdf)

Thus the sum of inverse $s$-powers of heights over the extensions of one parent is at most $h^{1-s}C_{k,s}\zeta(s-k)$ for $s>k+1$. Start in the chosen $k$ axes at height one. Iterating from outer exponent $N+0.01$ down to $k+1+0.01$ bounds the chart sum by $C_{k,k+1}^{N-k}\prod_{j=1}^{N-k}\zeta(j+0.01)$. Multiplication by $H^{N+0.01}$ and summation over charts gives (2) with the following constants.

For $t\le13$, the one-dimensional Gaussian sum is at most $1+\sqrt{\pi/t}$ by integration. For $t\ge13$ it is at most $1+2e^{-13}/(1-e^{-39})$. Splitting the gamma integral for $C_{k,k+1}$ bounds it by
\[
 \frac{2\sqrt{13}(\sqrt{13}+\sqrt\pi)^k}{\Gamma((k+1)/2)}
       +\left(1+\frac{2e^{-13}}{1-e^{-39}}\right)^k<1.002 .
\]
The verifier checks every indicated rank. Also $\zeta(1.01)\le101$ by integration. For $j\ge2$ one has $\log\zeta(j)\le 2^{-j}+2^{1-j}/(j-1)$, whose infinite sum is $1/2+\log2<1.2$. This gives $1.002^{505}\,101e^{1.2}<1000$.

**Joint bound.** Suppose the selected hit supplies a space satisfying $\det(T\cap L)/q^{400}\le B$ for deterministic $B$. At exact codimension $d$ it has $h\le q^dB$. Combining (1) and (2), its joint probability is at most
\[
 U_{N,k}(B,d)=2000\binom Nk(q^d B)^{N+0.01}q^{-d(k-400+d)}.     \tag{4}
\]
If $q^dB<1$ the event is empty and (4) is still an upper bound. The candidate spaces are enumerated before the random matrix is read. All selection and gate restrictions can be imposed afterward in this upper bound. In the applications below $N-k\ge502$, so consecutive summands increase by a factor exceeding $q^{100}$ for $1\le d\le400$. The entire sum through $d_0$ is at most $U(B,d_0)/(1-q^{-100})$.

## Application at creation and at the terminal draw

Let $a=1352/\sqrt3$, $R=(\sqrt2 a)^{1/2}$, $V_n=\pi^{n/2}/\Gamma(1+n/2)$ and $D_i=V_{506}g_i^{506}$ be incoming. Write $D_i^*$ for the pathwise floor from the period and squared Hermite cap 56.2142. A terminal hit in the rank-505 retained lattice supplies $k=408,N=911$ and $B=a\sqrt{56.2142}(D_{406}^*)^{-505/506}$ by the determinant quotient. This argument uses the final plane irrespective of its origin. At wholly old creation on draw $i$ the triple and all previously frozen directions are already in the old coordinates. They give $k=i+2,N=504+i$ and $B=aR/D_i^*$. [Part 221, terminal lift](wall1_z1_last_pieces.md#a-charge-that-also-covers-terminal-replacements)

The mixed residual on draw 406 gives one fewer old direction. Its designated winner $v$ and the old kernel line $x$ of the plane lift to a saturated rank-two section of the incoming lattice of determinant $s\|x\|$. Saturation follows by taking the full inverse image of the primitive line under quotient by $v$. Adding the 405 frozen directions gives $k=407,N=910$. For $g\ge z$ use $B=R\,29.2/(V_{506}z^{506})$. This counts a necessary old event before mark 406. Its positive generator height $1,\ldots,4$ is invertible modulo $q$, so adjoining it contributes exactly one to the suffix rank through 406 relative to the old kernel on any cut before draw 406. A lift of this generator splits the height map on the graph section, and has nonzero last coordinate modulo $q$. Thus the four paid terminal ranks also imply old kernel suffix ranks at least $44,26,9,0$ on the respective cuts. The old comparisons can share their pivots with frozen winners. [Part 218, mixed kernel and scale](wall1_z1_remainder.md#a-conditional-count-for-the-mixed-plane)

| Joint event | Largest $d$ charged | Upper probability summed through that $d$ | $\log_{10} U$ at the next $d$, rounded down |
|---|---:|---:|---:|
| Any terminal hit, full inverse image | 128 | $10^{-505}$ | 1770 |
| Draw-406 wholly old creation, full old triple | 128 | $10^{-683}$ | 1588 |
| Mixed residual, old kernel and winner, $g>32.32$ | 129 | $10^{-89}$ | 2179 |
| Mixed residual, same test, $g\ge32.68$ | 130 | $10^{-36}$ | 2225 |
| Incoming frozen section alone on 406, $B=1/D_{406}^*$ | 129 | $10^{-1065}$ | 1210 |

For earlier wholly old creations let $d_i$ be the largest $d$ for which the cumulative bound from (4) is below $10^{-30}$. Across all 235 draws from 172 to 406, creations at $d\le d_i$ cost less than $2.35\cdot10^{-28}$, including a later replacement. For $i=172,200,250,300,350,380,405,406$ the values are respectively $262,243,212,183,156,141,128,128$. A union of this estimate, the two mixed rows and the terminal bound costs less than $2.36\cdot10^{-28}$. Subtracting it from the audited balance still leaves more than $4.02078\cdot10^{-12}$. Earlier first hits of larger codimension can survive or be replaced by a terminal hit of codimension at least 129. For mixed creation the unpaid old-kernel ranks start at 130 below 32.68 and at 131 above it within the open interval. The codimension $d$ in this calculation measures deficiency of the syndrome image on the primitive integer section. The suffix pivot ranks in Part 221 measure coordinate rank on the graph section.

## How large the wholly old membership sum can be

For a fixed system of lifts, conditional on the initial columns, $u$ independent suffix pivots cost at most $q^{-400u}$ because the 400 scalar rows are independent. At $u=36$ this is $3329^{-14400}$ for one fixed lift. At the wholly old hit itself the final mark only enters the horizontal comparison. Echelon reduction from the right gives predictable column checks in draw order for that fixed system. Predictability alone supplies no charge for choosing a system. For example, prescribing $u$ particular columns in all $q^{400u}$ ways produces disjoint cylinders of total mass one. The following calculation retains the determinant path and the local geometry of a wholly old crossing. It adapts the projected-grid count of [Part 211](wall1_history_free_compression.md) to an incoming ternary section.

Reserve three horizontal axes $e_1,e_2,e_3$ and the three initial input coordinates 103–105. In the other coordinates use 397 horizontal axes and 102 initial inputs. At each of the first 405 freezes use the newest input as a private pivot $+1$ and only previously active coordinates elsewhere. After $i-1$ such choices the active projected integer grid has rank $m=499$, determinant $1/P$ for $P=\prod_{j<i}s_j$, and covering radius at most $\delta=\sqrt{499}/2$. The unit pivot minor gives primitivity. Independent projected coordinate units of length at most one give the covering bound by backward rounding. Choosing a projected point chooses an extension modulo the preceding span, and a point of norm $u$ gives $s_i^2=1+u^2$.

Start $l_0=b_0=400\log q$. Put $r_i=\min(q,\sqrt{56.2142}\,e^{l_{i-1}/506})$, multiplied by $0.9$ on draws 399–405. Put $c_i=\sqrt{r_i^2-1}$, $t_i=c_i-2\delta-1$, $l_i=l_{i-1}-\log r_i$, $b_i=b_{i-1}-\log t_i$. Take $t_i<u\le c_i$. Voronoi covering and disjoint interiors give at least $PV_m[(c_i-\delta)^m-(c_i-\delta-1)^m]$ choices. These satisfy the actual determinant-dependent upper caps and $l_i\le\log(q^{400}/P_i)\le b_i$. Weight each step by $q^{-400}$. Its contribution per parent is bounded below by
\[
       e^{-b_{i-1}} V_m[(c_i-\delta)^m-(c_i-\delta-1)^m].         \tag{5}
\]
The resulting incoming $g$ lies between 32.2322 and 36.9870. All these are proposed freezes in the counting sum.

After the 405 pivots, introduce the three old columns $v,x,y$. Give them unit pivots respectively on inputs 103, 104, 105 and horizontal components $29e_1$, $14e_1+28e_2$, $14e_1+27e_3$. Independently add to each a point of norm at most $1/2$ in the same projected active grid. There are at least $P V_m(1/4)^m$ choices for each. Indeed the mean number of points in a translate of the radius-$1/4$ ball is its volume divided by the determinant. Subtract one of the points in a translate attaining at least the mean to obtain distinct points in the centered radius-$1/2$ ball. Each point has an integral lift modulo the prefix.

In the resulting incoming ternary lattice $v$ is shortest, every old plane has area above $a$, and quotienting by $v$ gives area below $a$. For the unperturbed ternary lattice the only vectors through length 30 are $\pm v$ and zero. The independent pairs through length 32 all have area above $a$, as in Part 218. The perturbations add a positive semidefinite matrix to the ternary Gram form, so lengths and two-dimensional areas can only increase. The perturbed $v$ has squared length at most $842+1/4<900$. A Gauss basis of any putative old hit would have both lengths at most $2a/(\sqrt3\sqrt{842})<32$. After projecting by $v$, evaluate the two representatives $x-(406/842)v$ and $y-(406/842)v$. Their active perturbations each have norm below $3/4$. The product of their squared norms is at most $(330583/421+9/16)(307428/421+9/16)<a^2$. Projection onto $v^\perp$ can only decrease their area. The three private input pivots make this triple saturated. These comparisons are internal to the ternary lattice. [Part 218, base ternary form](wall1_z1_remainder.md#arithmetic-and-a-reachable-spacing-counterexample)

The full space determines the preceding frozen span by setting inputs 103–105 to zero. Within that span, setting each unused suffix to zero recovers the successive prefix spans. In the final triple, the three prescribed input pivot vectors distinguish each projected perturbation modulo the prefix. Thus different configurations give different full $408$-spaces, even without counting bases or intermediate flags separately. The combined input pivot minor is unimodular, so each space has exact graph membership probability $q^{-400\cdot408}$ and $d=400$ on membership. All 405 suffix pivots are present at creation. The same proposed terminal plane uses no coordinate on draw 406, meeting all four numerical suffix rank requirements. The incoming frozen section has $h_F=P$ and passes the Part 212 height threshold.

Multiplying (5) through 405 and then multiplying by $[e^{-b_{405}} V_m(1/4)^m]^3$ gives a lower certificate for the membership sum with base-ten logarithm in $(10163.4140,10163.4141)$. The number of distinct spaces exceeds $10^{585005.0254}$. Even allowing the entire $4.02\cdot10^{-12}$ for this family, a first moment that additionally tests the missing conditions must retain a membership-weighted fraction below $10^{-10174.8098}$ to certify the target. The large sum gives no positive lower bound on selected gated mass. In particular, meeting the numerical suffix ranks does not ensure the raw dual floors. A frequency estimate for the selected high-codimension spaces, or a count incorporating their global comparisons and gates, is still needed.

## Reproduction

The verifier runs from the research scripts directory and is embedded here to preserve the requested single-file change. It uses outward intervals for the height sums and determinant recursions and exact integer comparisons for the ternary lattice.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_wholly_old_mass.md | python -B -)
```

```python
from itertools import combinations
from math import comb
from mpmath import iv

iv.dps = 65
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
q, Q, ln10 = 3329, log(3329), log(10)
V = [I(1), I(2)]
for j in range(2, 912):
    V.append(2*iv.pi*V[j-2]/j)
a = 1352/sqrt(3)
R = sqrt(sqrt(2)*a)
gamma = I('56.2142')

for k in range(174, 409):
    small = 2*sqrt(13)*(sqrt(13)+sqrt(iv.pi))**k / iv.gamma(I(k+1)/2)
    large = (1+2*exp(-13)/(1-exp(-39)))**k
    assert small+large < I('1.002')
assert I('1.002')**505 * 101 * exp(I('1.2')) < 1000
assert I(1)/2+log(2) < I('1.2')

def strict_max(x, y):
    assert x > y or y > x
    return max(x, y)

floors = [None, 400*Q]
for i in range(1, 406):
    L = floors[-1]
    floors.append(strict_max(L-Q, I(505)/506*L-log(gamma)/2))

def bound(N, k, logB, d):
    # The base-ten log of (4) and of the geometric cumulative bound.
    assert 502 <= N-k <= 505
    single = (log(2000*comb(N,k)) + (N+I('.01'))*(d*Q+logB)
              - d*(k-400+d)*Q)/ln10
    return single, single-log(1-I(q)**(-100))/ln10

L = floors[406]
def mixed(z):
    return log(R*I('29.2'))-log(V[506])-506*log(I(z))

for N, k, logB, d, paid, next_lo in [
    (911,408,log(a*sqrt(gamma))-I(505)/506*L,128,-505,1770),
    (910,408,log(a*R)-L,128,-683,1588),
    (910,407,mixed('32.32'),129,-89,2179),
    (910,407,mixed('32.68'),130,-36,2225),
    (910,405,-L,129,-1065,1210),
]:
    _, cumulative = bound(N,k,logB,d)
    following, _ = bound(N,k,logB,d+1)
    assert cumulative < paid
    assert next_lo < following < next_lo+1
    print(N, k, d, float(cumulative.b), float(following.a))

starts = {}
for i in range(172,407):
    N, k, logB = 504+i, i+2, log(a*R)-floors[i]
    # Increasing in d; use binary search with certified comparisons.
    lo, hi = 0, 400
    assert bound(N,k,logB,lo)[1] < -30 < bound(N,k,logB,hi)[1]
    while hi-lo > 1:
        mid = (lo+hi)//2
        c = bound(N,k,logB,mid)[1]
        if c < -30:
            lo = mid
        else:
            assert c > -30
            hi = mid
    starts[i] = lo
assert [starts[i] for i in (172,200,250,300,350,380,405,406)] == [
    262,243,212,183,156,141,128,128]
new_charge = 235*I('1e-30')+I('1e-505')+I('1e-89')+I('1e-36')
assert new_charge < I('2.36e-28')
assert I('4.02079e-12')-new_charge > I('4.02078e-12')

# Enumerate all anchor vectors through length 32. Their private input
# coordinates bound the first coefficient; rows 2 and 3 bound the others.
def point(i, j, k):
    return (29*i+14*j+14*k,28*j,27*k,i,j,k)

def dot(x, y):
    return sum(a*b for a,b in zip(x,y))

v = point(1,0,0)
short = [point(i,j,k) for i in range(-32,33) for j in (-1,0,1)
         for k in (-1,0,1) if (i,j,k) != (0,0,0) and
         dot(point(i,j,k),point(i,j,k)) <= 32**2]
assert {x for x in short if dot(x,x) <= 900} == {v, tuple(-z for z in v)}
for x,y in combinations(short,2):
    det = dot(x,x)*dot(y,y)-dot(x,y)**2
    assert det == 0 or 3*det > 1352**2
assert 2*a/(sqrt(3)*sqrt(842)) < 32
assert (I(330583)/421+I(9)/16)*(I(307428)/421+I(9)/16) < a*a

m = 499
delta = sqrt(m)/2
lower = upper = 400*Q
log_mass = I(0)
for i in range(1,406):
    hermite = sqrt(gamma)*exp(lower/506)
    assert hermite > q or hermite < q
    radius = min(I(q),hermite)
    if i >= 399:
        radius *= I('.9')
    c = sqrt(radius**2-1)
    t = c-2*delta-1
    x = c-delta
    assert t > 1
    log_mass += log(V[m]) + m*log(x) + log(1-(1-1/x)**m) - upper
    lower -= log(radius)
    upper -= log(t)
assert I('32.2322') < exp((lower-log(V[506]))/506)
assert exp((upper-log(V[506]))/506) < I('36.9870')
assert 2*(400*Q-upper) > 99*log(2)
log_mass += 3*(log(V[m])+m*log(I('.25'))-upper)
assert I('10163.4140') < log_mass/ln10 < I('10163.4141')
assert (log_mass+400*408*Q)/ln10 > I('585005.0254')
assert (log_mass-log(I('4.02e-12')))/ln10 > I('10174.8098')
print('Creation, replacement, mixed rank bounds and section multiplicity verified.')
```

## Audit

**Verdict.** All four joint probability bounds and the codimension-400 membership first moment hold. One clarification applies to the opening summary. The mixed bounds charge the event that a Part 218 residual hit occurs **and** its old lift has codimension at most the stated cutoff. Part 218 supplies $\|x\|<29.2$ on that residual. The scale interval alone supplies neither this length bound nor a ceiling on the realized codimension.

**Order of revelation.** For each exact deficiency $d$, the witness must belong to the deterministic list of rational spaces $T$ with $\det(T\cap\mathbb Z^N)\le q^dB$. The determinant floor in the first two applications and the fixed scale endpoint $z$ in the mixed applications make $B$ independent of every column, including the 105 initial columns. For a fixed listed space, primitivity embeds its section modulo $q$. After choosing a basis for its $b$ purely horizontal directions, the other $k-b$ input projections are linearly independent. Their images under uniform $A$ are independent uniform 400-vectors. A fixed $d$-dimensional annihilator perpendicular to the horizontal images therefore costs exactly $q^{-d(k-b)}$. Summing over annihilators gives (1). Taking the union over the deterministic list now covers every adaptive choice of plane, frozen span and winner. The terminal witness can be taken from the final lattice even when the first plane has disappeared.

**Counting sections.** In a fixed coordinate chart the denominator $n$ is the order of the graph form modulo $S^*$, so its integral kernel has index $n$. The graph volume factor gives the stated child height. In (3), coordinate restriction sends distinct $v\in S$ to distinct integer points of norm at most $\|v\|$. This gives the upper inequality on the Poisson sum in the required direction. Iteration over the $N-k$ added coordinates ends at exponent $k+1.01$, where the denominator sum still converges. The chart factor and the verified bound on the product of constants give (2). Also $U(B,d)/U(B,d-1)=q^{N-k+401.01-2d}>q^{100}$ throughout the applications.

I reran the embedded interval verifier. Independently, I evaluated ball volumes with $\log\Gamma$, iterated the determinant floor in determinant units, and summed (4) directly from $d=0$ through each cutoff at 115-digit precision. The displayed values below are base-ten logarithms of these sums.

| Witness | $(N,k)$ | Cutoff | $\log_{10}\sum_{d\le d_0} U(B,d)$ |
|---|---|---:|---:|
| Terminal plane and all 406 frozen directions | $(911,408)$ | 128 | $-505.39182296\ldots$ |
| Wholly old triple and 405 frozen directions | $(910,408)$ | 128 | $-683.22772718\ldots$ |
| Mixed old lift, $32.32<g<32.75$ | $(910,407)$ | 129 | $-89.34300613\ldots$ |
| Mixed old lift, $32.68\le g<32.75$ | $(910,407)$ | 130 | $-36.09500968\ldots$ |

For the mixed rows the two old quotient lengths contribute $s\|x\|$ to the covolume, and the 405 earlier lengths contribute $q^{400}/D_{406}$. No probability factor for the last mark enters these bounds.

**Codimension 400.** Setting the three reserved input coordinates to zero recovers the 405-dimensional prefix from the full space. Its triangular suffix pivots recover each preceding span by truncation. Within the full space, fixing any one of the three reserved unit input patterns then determines its vector modulo the prefix, hence its projected perturbation. This proves that the product in (5) counts distinct full spaces. The input minor has determinant one up to sign, so the displayed integer columns generate the primitive section and have input rank 408 modulo $q$. The unconditional probability that this section lies in the graph is exactly $q^{-400\cdot408}$. Factoring this weight in the count requires no fresh randomness for the three reserved inputs after draw 405.

The active grid has rank 499 at each prefix. Subtracting the upper count for the inner ball from the lower count for the outer ball gives (5) with $P/q^{400}\ge e^{-b_{i-1}}$. In a separate integer enumeration, the ten nonzero anchor vectors through length 32 had least independent squared area $614856>1352^2/3$. Orthogonality of the perturbations to the anchor coordinates preserves this lower bound for pairs still through length 32, and the Gauss basis angle bound $\sin\theta\ge\sqrt3/2$ places both basis vectors of any putative old hit within that enumeration. The two displayed representatives after removing $v$ give a squared-area upper bound strictly below $1352^2/3$. The 405 suffix pivots also give rank $405-t$ after each of the four cuts $t$ through draw 406. A direct product of the 405 shell factors and the three ball factors gave $10163.414071367449\ldots$ for the base-ten logarithm of the weighted lower certificate and $585005.025440935566\ldots$ for the unweighted one. These certify the local crossing and the membership sum. The probability of a selected, gated hit in this family remains undetermined.
