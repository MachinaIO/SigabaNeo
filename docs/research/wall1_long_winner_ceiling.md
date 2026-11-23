# The conditional long-winner probability in the width-506 restart

The probability of a winner longer than $1.10g$ is **zero on draws 1–7**, on every history. On the remaining draws where the horizontal minimum and the period do not already settle the question, the conditional mean of the height-one count exceeds **$1.85\cdot10^{16}$**. I obtain an exact finite sum for its variance, but no uniform bound small enough to prove the proposed $0.126$ ceiling. No violating gated history has been identified.

There is a weaker sufficient hypothesis for the small-determinant problem. A conditional ceiling of **$0.126$ on draws 11–380 alone** gives crossing probability below $2.456\cdot10^{-11}$. Alternatively, **$0.1795$ on draws 11–405** gives less than $2.478\cdot10^{-11}$. Both use the weights of the individual determinant drops. The probability hypotheses in these two statements remain open. [Small-$g$ frequency and audit](wall1_small_g_frequency.md#audit)

## Draws and conditioning

Use $n=506$, $d=505$, $q=3329$, $V_j=\pi^{j/2}/\Gamma(1+j/2)$ and $c=11/10$. At entry let $D=\det M$, $g=(D/V_n)^{1/n}$ and $r=cg$. Each of draws 1–405 appends one fresh unit-height column to a retained rank-$d$ lattice $M$ and selects a shortest vector of the rank-$n$ window. There is no shrinking block in this range. The uniform mark is $U\in H=K/M$, with $K$ the projection of the integer grid. Write $h=|H|$. All expectations below condition on the revealed prefix. One may restrict to prefixes passing tests measurable at entry. A terminal gate involving unread columns can be imposed in a joint-event bound after integrating the transition. Conditioning the transition on that gate would require its posterior weights. The rank improvement in Part 212 excludes a small exceptional event and is unnecessary here. [Part 108](wall1_first_tour.md) · [Part 212 and audit](wall1_integrality_bound.md#audit)

**Period and horizontal tests.** The pure height-$q$ vector belongs to every window, and $M$ embeds horizontally. Thus $r\ge q$ or $\lambda_1(M)\le r$ gives conditional long-winner probability zero. Since $D_0=q^{400}$ and each freeze divides the determinant by at most $q$, draw $i$ has $g_i\ge(q^{401-i}/V_n)^{1/n}$. On draw 7 this lower bound exceeds $3031.60>q/c$; on draw 8 it is below $2983.41<q/c$. The latter comparison only locates the end of this universal period argument. On the remaining unresolved entries,
$$
 8\le i\le405,\qquad 32.18553<g<q/c,\qquad \lambda_1(M)>r.
 \tag{1}
$$
The lower endpoint follows from the decreasing certified floor through draw 406. [Determinant recurrence and floor](wall1_small_g_frequency.md#how-many-long-winners-does-a-crossing-require)

## Exact first and second moments on one prefix

For $1\le k\le\lfloor r\rfloor$ write $S_k=K\cap\overline B_{\sqrt{r^2-k^2}}$. On (1) all these heights are invertible modulo $q$. Each label $(k,y)$, $y\in S_k$, specifies the **single** mark $u(k,y)=k^{-1}[y]$. Positive heights suffice by sign symmetry. Take any subset of these labels, write $b_u$ for its multiplicity at $u$, and set
$$
 N=b_U,\qquad A=\sum_u b_u,\quad B=\sum_u b_u^2 .
$$
Then
$$
 \mu=\mathbb E N=A/h,\qquad
 \operatorname{Var} N=B/h-(A/h)^2,\qquad
 \Pr(N=0)=1-\#\{u:b_u>0\}/h.                         \tag{2}
$$
For all labels the last expression equals the long-winner probability on (1). For a subfamily it bounds that probability from above. Distinct labels with matching marks have joint probability $1/h$; with different marks they have joint probability zero. For $(k,y),(l,z)$ the test is $ly-kz\in M$. Even linearly independent residue classes have disjoint mark events. The pair law $q^{-2d_F}$ for two independent linear constraints on a random matrix does not apply after the prefix is fixed.

For height one write $S=S_1$, $\rho^2=r^2-1$. The concrete collision sum is
$$
 A=\#S,\qquad
 B=A+\sum_{0\ne v\in M,\ \|v\|\le 2\rho}
         \#\{y\in S:\ y+v\in S\}.                      \tag{3}
$$
Each ordered pair is counted once. On (1) only $r<\|v\|\le2\rho$ can contribute to the off-diagonal sum. Cauchy–Schwarz gives $\Pr(N=0)\le1-A^2/(hB)$ for $A>0$. The precise sufficient condition for this second-moment certificate is
$$
 hB/A^2\le 500/437
 \quad\Longleftrightarrow\quad
 \operatorname{Var}N/\mu^2\le63/437.                     \tag{4}
$$
Failure of (4) need not imply failure of the ceiling. For all heights, the actual ceiling fails precisely when the number of distinct marks is less than $437h/500$. Mark rank alone gives no lower estimate of that fraction. For example, at the level of multiplicities on an elementary $q$-group, making $b_u=qL$ on a hyperplane and zero off it gives mean $L$ and void fraction $1-1/q$ at any positive rank. This example makes no geometric or reachability claim.

**Arithmetic of a specified prefix.** Choose an integer basis matrix $C$ (basis vectors as columns) of $K^*=F^\perp\cap\mathbb Z^N$ and put $G=C^\top C$. In coordinates $t\in\mathbb Z^d$ on $K$, the point is $CG^{-1}t$ and its squared norm is $t^\top G^{-1}t$. A basis of $M$ in these coordinates gives an integer matrix $T$. Part 212 gives $qM^*\subset K^*$, equivalently $qK\subset M$. Thus $h=|\det T|$, and the mark comparison is $T^{-1}(lt-kz)\in\mathbb Z^d$ for coordinate vectors $t,z$. Ellipsoid enumeration and this rational congruence give (2)–(3) with zero counting error on supplied Gram and inclusion data. Each coordinate is bounded by $|t_j|\le\rho\sqrt{G_{jj}}$ at height one. Even the GH boundary can be resolved by successively enclosing $r^2=c^2(D\,253!)^{1/253}/\pi$: it is transcendental since $D$ is positive algebraic, whereas squared norms plus squared heights are rational. Integrality does not supply the individual $G,T$ along every selected history. [Part 215, exact ellipsoid enumerator](wall1_fresh_mark_extension.md#reproduction)

## A uniform estimate of the height-one mean

On every prefix in (1),
$$
              1.85\cdot10^{16}<\mu_1<7.273\cdot10^{21}.    \tag{5}
$$
Here $\mu_1$ counts positive height one, including every horizontal representative in its ball. This is a conditional mean over the actual finite subgroup.

For the lower bound put $b=d/2$, $\beta=(b+2)/\rho^2$. The cell $|\beta\|y\|^2-b|<2$ lies inside the required ball. In the Part 215 minorant proof the grid/continuum Fourier error increases with $\beta$ at fixed frequency. Our largest $\beta$ is below the one certified there, since $c\cdot32.18553$ exceeds its outer length $2^{1/4}\sqrt{1352/\sqrt3}$. The normalized tilted grid mass of this cell therefore exceeds $0.01060$ uniformly. On this cell the inverse Gaussian weight exceeds $e^{b-2}$. Since $h\det K=D$,
$$
 \mu_1>\frac{0.01060\,e^{b-2}}{V_n g^n}
           \left(\frac{\pi(c^2 g^2-1)}{b+2}\right)^b.
 \tag{6}
$$
Its dependence on $g$ is proportional to $g^{-1}(1-(cg)^{-2})^b$, decreasing for $(cg)^2>506$. At $g=q/c$ the right side exceeds $1.8513\cdot10^{16}$. [Part 215, cell minorant and error estimate](wall1_fresh_mark_extension.md#an-explicit-lattice-point-discrepancy-at-height-one)

For the upper bound use the Gaussian majorant at $\beta'=b/\rho^2$. Poisson summation on $K$ and restriction of the dual integer section to $d$ independent coordinates give
$$
 \mu_1\le\frac{e^b(\pi/\beta')^b}{V_ng^n}
 \left(1+\frac{2e^{-v}}{1-e^{-3v}}\right)^d,\qquad v=\pi^2/\beta'.
$$
The prefactor has the same monotonicity, and the theta factor decreases with $g$. The verifier evaluates at $32.18553$.

**What separation alone certifies.** Each fiber in the height-one ball consists of points separated by more than $r$. Lift $y$ to the unit sphere in $\mathbb R^{506}$ as $(y,\sqrt{\rho^2-\|y\|^2})/\rho$. Lifted distances exceed one, so distinct unit vectors have inner product below $1/2$. A cap of angular radius $\pi/4$ contains at most 506 of them. Indeed, projecting its points perpendicular to its axis gives pairwise strictly negative inner products. If an axial point occurs it is alone. Otherwise at most 506 vectors in dimension 505 can have this property: any affine dependence splits into two nonempty positive combinations with equal sum, whose mutual inner product would be negative. Averaging the cap over its axis now gives the following bound for each multiplicity, using $\cos\theta\le1$ in the numerator integral:
$$
 b_u\le 506/P,\qquad
 P=\frac{\int_0^{\pi/4}\sin^{504}\theta\,d\theta}
          {\int_0^\pi\sin^{504}\theta\,d\theta}
 \ge\frac{2^{-505/2}\Gamma(253)}
 {505\sqrt\pi\,\Gamma(505/2)} .
$$
This is the elementary spherical-cap averaging argument. [Cohn and Zhao, spherical-code bounds](https://arxiv.org/abs/1212.5966)

Taking $L=2.919\cdot10^{80}$ gives $B\le LA$ in (3). Equations (2) and (5) now prove the uniform, but weak, long-winner ceiling $1-6.33\cdot10^{-65}$. On **every** prefix in (1) the particular majorant $L/\mu_1$ for $hB/A^2$ exceeds $4.01\cdot10^{58}$, compared with $500/437$ in (4). This quantifies failure of the packing estimate even with the exact mean. The collision sum itself may be far smaller. No lower bound on actual long-winner probability follows.

## How many draws need conditional control?

With draws 1–7 deterministic, the original 100-winner argument gives $\Pr(\operatorname{Bin}(398,0.126)\ge100)<8.820\cdot10^{-12}$ if the other draws obey the ceiling. Letting one further arbitrary fixed draw be always long gives $\Pr(\operatorname{Bin}(397,0.126)\ge99)<1.772\cdot10^{-11}$. Two such exemptions give $\Pr(\operatorname{Bin}(396,0.126)\ge98)>3.531\cdot10^{-11}$, above the $2.72513\cdot10^{-11}$ allowance. These are limits of the unweighted count argument.

The time weights permit much longer exemptions. Put $a=505/506$, $H_0=\sqrt{56.2142}\,V_n^{1/n}$, $b_0=\log c$, $\delta=\log H_0-b_0>0$, and $x_i=\log g_i$. Let $x^*_{m+1}$ be the certified incoming floor in log units after $m$ unrestricted draws. Write $I_i=\mathbf1_{s_i>cg_i}$. For $i>m$,
$$
 x_{i+1}\ge a x_i-(b_0+\delta I_i)/506.
$$
Run the affine recursion with equality from $x^*_{m+1}$. It stays below the true path. Once this comparison path falls below $\log t$, $t=34.807$, it stays below, since even its larger affine map sends $\log t$ below itself. Hence any crossing on draws 396–406, for the values of $m$ below, implies
$$
 \sum_{i=m+1}^{405} w_i I_i>T_m,\quad
 w_i=a^{405-i},\quad
 T_m=\frac{506(a^{405-m}x^*_{m+1}-\log t)-b_0\sum_i w_i}{\delta}.
$$
Exempt the last $e$ draws by setting their comparisons to one and let $J=\{m+1,\ldots,405-e\}$, $T=T_m-\sum_{i>405-e} w_i$ (sum over the suffix through 405). If all draws in $J$ satisfy the conditional ceiling $p$, then for any $z>0$ the crossing probability is at most
$$
 \exp\left(-zT+\sum_{i\in J}\log(1+p(e^{zw_i}-1))\right). \tag{7}
$$
This follows by iterating conditional exponential moments. For ceiling hypotheses valid only until a predictable gate exit, set subsequent tested indicators to zero. The same bound holds for crossings reached on surviving paths, using the affine comparison up to the crossing and its persistence afterwards. Future gate conditions may only restrict this joint event.

| Draws requiring a ceiling | $p$ | $T$ (rounded) | $z$ used | Upper bound from (7) |
|---|---:|---:|---:|---:|
| 11–380 | 0.126 | 66.16485 | 1.286 | $2.456\cdot10^{-11}$ |
| 63–405 | 0.126 | 67.24729 | 1.238 | $2.677\cdot10^{-11}$ |
| 11–405 | 0.1795 | 90.58085 | 1.106 | $2.478\cdot10^{-11}$ |

Each row individually fits the audited remaining allowance. The second row uses the $2.72513\cdot10^{-11}$ allowance and exceeds the narrower $2.58815\cdot10^{-11}$ benchmark. The first row exempts the final 25 draws as well as the first ten. The gap for that row is a coverage estimate on the histories (1) at draws 11–380. Equations (2)–(4) specify the missing test before selection; no enumeration of all reachable gated prefixes or proof that any such prefix violates the target was obtained.

## Which incoming determinants can still contribute?

For the crossing bound one can further restrict which histories need a probability estimate. Define $u_{406}=\log t$ and, backwards for $i=405,\ldots,1$,
$$
 u_i=\min\{u_{i+1}+\log q/506,\ (u_{i+1}+\log H_0/506)/a\}.
$$
This is the inverse of the unrestricted increasing floor map $F(x)=\max(x-\log q/506,ax-\log H_0/506)$. On a prefix with $x_i\ge u_i$, iterating $F$ to draw 406 gives at least $\log t$. That lower comparison path could never have fallen below $\log t$, since $F(\log t)<\log t$. Thus no subsequent crossing is possible. For (7), a tested draw needs a ceiling only **before the first crossing**, on a still-gated prefix with
$$
  g_i^*\le g_i<\min(q/c,e^{u_i}),\qquad \lambda_1(M)>cg_i .
$$
Indeed, on every surviving crossing path all the preceding entries have $x_i<u_i$. Set tested indicators to zero once continuation to a first crossing becomes impossible or a crossing occurs. Up to a first crossing the omitted horizontal and period cases already have zero indicator. The same conditional-moment proof applies.

| Incoming draw | Certified $g_i^*$, rounded down | $e^{u_i}$, rounded up |
|---:|---:|---:|
| 63 | 1269.2983 | 1481.1154 |
| 100 | 749.7558 | 865.3950 |
| 200 | 216.0313 | 243.0135 |
| 300 | 77.8230 | 85.7133 |
| 380 | 39.3014 | 42.6786 |
| 400 | 33.6732 | 36.4500 |
| 405 | 32.4276 | 35.0743 |

These endpoints use only the scalar floor and do not certify that an extremizing determinant or a violating mark distribution is reachable. This restriction is for the residual objective. The proposed ceiling on *all* gated prefixes also includes histories that can no longer reach the crossing.

## Reproduction

The interval verifier is embedded so that the note is the only new file. Run it from the repository's research scripts directory.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_long_winner_ceiling.md | python -B -)
```

```python
from fractions import Fraction
from math import comb
from mpmath import iv

iv.dps = 75
I = iv.mpf
q, n, d = 3329, 506, 505
b, a, c = I(d)/2, I(d)/n, I(11)/10
V = iv.pi**253 / iv.factorial(253)
logV, Q = iv.ln(V), iv.ln(q)
x1 = (400*Q-logV)/n
logh = iv.ln(I('56.2142'))/2 + logV/n
logc = iv.ln(c)
floors = [x1]
for _ in range(405):
    x = floors[-1]
    period, hermite = x-Q/n, a*x-logh/n
    assert period > hermite or hermite > period
    floors.append(max(period, hermite))
    assert floors[-1] < x
assert iv.exp(floors[-1]) > I('32.18553')
assert iv.exp(x1-6*Q/n) > I('3031.60') > q/c
assert iv.exp(x1-7*Q/n) < I('2983.41') < q/c

gmin, gmax = I('32.18553'), q/c
assert (c*gmin)**2 > 506
assert (c*gmin)**2 > iv.sqrt(2)*1352/iv.sqrt(3)
beta = (b+2)/((c*gmax)**2-1)
mu_lower = I('.01060')*iv.exp(b-2)*(iv.pi/beta)**b/(V*gmax**n)
assert mu_lower > I('1.8513e16')
beta = b/((c*gmin)**2-1)
v = iv.pi**2/beta
theta = 1 + 2*iv.exp(-v)/(1-iv.exp(-3*v))
mu_upper = iv.exp(b)*(iv.pi/beta)**b*theta**d/(V*gmin**n)
assert mu_upper < I('7.273e21')
cap_lower = I(2)**(-b)*iv.gamma(253)/(d*iv.sqrt(iv.pi)*iv.gamma(b))
L = I('2.919e80')
assert 506/cap_lower < L
assert mu_lower/L > I('6.33e-65') and L/mu_upper > I('4.01e58')

p = Fraction(63,500)
for count, threshold, lo, hi in [
    (398,100,'8.819e-12','8.820e-12'),
    (397,99,'1.771e-11','1.772e-11'),
    (396,98,'3.531e-11','3.532e-11'),
]:
    tail = sum(comb(count,k)*p**k*(1-p)**(count-k)
               for k in range(threshold,count+1))
    assert Fraction(lo) < tail < Fraction(hi)

for m, e, prob, z, tval, cap in [
    (10,25,'.126','1.286','66.16485','2.456e-11'),
    (62,0,'.126','1.238','67.24729','2.677e-11'),
    (10,0,'.1795','1.106','90.58085','2.478e-11'),
]:
    weights = [a**j for j in range(405-m)]  # latest draw first
    T = (n*(a**(405-m)*floors[m]-iv.ln(I('34.807')))
         - logc*sum(weights))/(logh-logc) - sum(weights[:e])
    assert abs(T-I(tval)) < I('.000005')
    z, prob = I(z), I(prob)
    exponent = sum(iv.ln(1+prob*(iv.exp(z*w)-1)) for w in weights[e:])-z*T
    assert iv.exp(exponent) < I(cap) < I('2.72513e-11')
upper = {406: iv.ln(I('34.807'))}
for i in range(405,0,-1):
    period = upper[i+1]+Q/n
    hermite = (upper[i+1]+logh/n)/a
    assert period < hermite or hermite < period
    upper[i] = min(period, hermite)
for i, low, high in [
    (63,'1269.2983','1481.1154'), (100,'749.7558','865.3950'),
    (200,'216.0313','243.0135'), (300,'77.8230','85.7133'),
    (380,'39.3014','42.6786'), (400,'33.6732','36.4500'),
    (405,'32.4276','35.0743'),
]:
    step = I('.0001')
    assert I(low) < iv.exp(floors[i-1]) < I(low)+step
    assert I(high)-step < iv.exp(upper[i]) < I(high)
print('Verified the draws, first moment, packing certificate, crossing bounds and corridors.')
```

## Audit

**Verdict.** All four claims hold as stated. The period exclusion, height-one mean bound and collision identity hold on the indicated prefixes of the original chain. Each reduced-range crossing bound requires its stated conditional ceiling. Establishing either ceiling remains open. No correction is needed.

**Period and mean.** Starting from $D_0=3329^{400}$, the period-only incoming $g$ floor is $3031.607147\ldots$ on draw 7 and $2983.402352\ldots$ on draw 8. The floor decreases, so $s_i\le q<1.10g_i$ on every history through draw 7. At each entry in (1), $\beta=(b+2)/(c^2g^2-1)$ is smaller than the Part 215 value. Its Fourier error bound therefore decreases pointwise, and the same minorant gives tilted cell mass above $0.01060$. Dividing the resulting point count by $h$ uses the uniform fresh mark and $h\det K=D$. The logarithmic derivative of (6) with respect to $\log g$ is $-1+505/(c^2g^2-1)<0$ throughout (1). At the upper endpoint $q/c$, (6) evaluates to $1.85135067838\ldots\cdot10^{16}$. This certifies the conditional mean on every unresolved prefix.

**Variance.** At height one, $h\,\mathbb E[N^2]=\sum_u b_u^2$ counts ordered pairs $(y,z)\in S^2$ with $z-y\in M$. The diagonal contributes $A$. For each nonzero difference $v$, the pairs are in bijection with $y\in S$ such that $y+v\in S$, and the triangle inequality gives $\|v\|\le2\rho$. Both signs of $v$ occur in (3). Dividing this sum by $h$ and subtracting $(A/h)^2$ gives the exact variance.

**Crossing.** An independent 85-digit interval calculation updated the physical covolume by $D\mapsto D/\min(q,H_0g)$ from draw 1 through draw 10. It gives $g_{11}^*=2843.3383615\ldots$ and allows every outcome on draws 8–10. Starting there, use $g\mapsto(g^{505}/c)^{1/506}$ on tested draws for the comparison path with zero tested indicators. For the 11–380 row use $H_0$ in place of $c$ on all 25 draws 381–405, allowing each to be long. For the 11–405 row the suffix is empty. Each tested long indicator lowers the final comparison log scale by $\delta a^{405-i}/506$. Even the zero-indicator update sends $\log t$ strictly below itself, so crossing on any of draws 396–406 implies the single final weighted-tail event. This persistence also holds when tested indicators are set to zero after a first crossing.

The thresholds are $66.16484737\ldots$ and $90.58084827\ldots$, respectively. Direct multiplication of the conditional moment bounds at the stated $z$ gives $2.4557985871\ldots\cdot10^{-11}$ and $2.4770666443\ldots\cdot10^{-11}$. Each is below $2.72513\cdot10^{-11}$. A fresh uniform per tested draw couples its indicator below a Bernoulli($p$) indicator whenever its prefix probability is at most $p$. With a predictable gate, use the stopped indicators and count crossings reached while the gate survives. This proves the weighted bound with dependent draws. For the unweighted check, the exact binomial tails for zero, one and two additional fixed exemptions are $8.81971838\ldots\cdot10^{-12}$, $1.77134964\ldots\cdot10^{-11}$ and $3.53154321\ldots\cdot10^{-11}$.

The embedded verifier and the supporting Part 212, 215 and 216 verifiers all passed.
