# The small incoming determinant in the width-506 chain

On the original finite chain, the joint probability of a vertical residual hit on draws 396–406 with incoming $g\ge34.807$ is **less than $3.75987\cdot10^{-11}$**. This leaves **$2.72513\cdot10^{-11}$** for smaller scales. Alternatively, the same proof covers $g\ge34.77$ for $6.44035\cdot10^{-11}$. These are alternatives for the same budget. The small-$g$ frequency and the full $6.485\cdot10^{-11}$ bound remain open.

There is a pathwise restriction on that frequency. Reaching $g<34.807$ on any of the eleven draws requires **at least 100 earlier winners longer than 1.10 times their own incoming GH length**. The exact mark law identifies the probability of each long winner as a void probability. The short-candidate first moments control the opposite tail. The calculations below keep the common mark for every candidate on a draw. [Part 108](wall1_first_tour.md) · [Part 193](wall1_z2_vertical.md) · [Part 215 and audit](wall1_fresh_mark_extension.md#audit)

## Which tail of the determinant drop?

Let $n=506, q=3329, V_j=\pi^{j/2}/\Gamma(1+j/2)$. Write $D_j$ for the retained determinant **after** $j$ freezes, $g_i=(D_{i-1}/V_n)^{1/n}$ and $s_i$ for the winner on draw $i$. The initial 105 graph columns can affect the framed state. Its determinant is always $D_0=q^{400}$. Part 108 gives, pathwise,

$$
D_j=D_0/\prod_{i=1}^j s_i,\qquad
g_{j+1}<t\quad\Longleftrightarrow\quad
\sum_{i=1}^j\log s_i>400\log q-\log V_n-n\log t.
$$

At $t=34.807$ the right-hand threshold is in $(2308.9795681,2308.9795682)$ nats. Equivalently the incoming log determinant must be below $\log V_n+n\log 34.807$, approximately 935.19132690. The event at draw 406 uses 405 factors. A short winner increases the outgoing determinant relative to a longer winner at the same entry.

For the exact conditional distribution let $X$ comprise the lattice $M$, the mark group $H=K/M$, and the frame for the tie rule. Here $K$ is the projection of the ambient integer grid onto the retained space. For $r>0$, form the following subset of marks.

$$
C_X(r)=\bigcup_{1\le k\le\lfloor r\rfloor}
\{u\in H:\exists y\in K,\ [y]=ku,\ \|y\|^2\le r^2-k^2\}.
$$

Then

$$
\Pr(s_i>r\mid X)=\mathbf1_{\lambda_1(M)>r}
\left(1-\frac{|C_X(r)|}{|H|}\right).
\tag{1}
$$

The closed balls and strict inequality include ties correctly, even at integer $r$ or heights divisible by $q$. To obtain the exact joint law, start with the actual distribution of the initial framed state and a log-drop coordinate $z=0$. For each state and mark $u$, transfer mass $1/|H|$ times its incoming weight to $(X'(u),z+\log s(X,u))$, with the original tie rule in $X'$. The marginal in $z$ after step $j$ gives the drop law. For the union of incoming crossings retain a first-crossing flag before the corresponding transfers. Future gates can be tested on the extended history. A scalar convolution would require a separate argument that the conditional increment laws have the claimed dependence on the scalar state.

An upper bound on the sum of candidate multiplicities bounds $|C_X(r)|$ **above**. Bounding (1) from above needs coverage of distinct marks **from below** when the horizontal minimum exceeds $r$. In particular Part 215 gives a conditional mean exceeding 118 height-one candidates for $g\le32.5$. Several can share one mark, and that mean carries no information about the frequency of the prefix. The mark rank and the integral Gram lower bound give $D=q^{d_F}/\sqrt{p_F}$, so a lower bound on $p_F$ at fixed $d_F$ gives an upper bound on $D$. The low-rank Hermite constants control a specified short plane or suffix. They supply no void fraction in (1). [Part 212](wall1_integrality_bound.md) · [Part 139, Theorem 5, for a second-moment formula](wall1_lyapunov.md)

## How many long winners does a crossing require?

Put $a=505/506, Q=\log q, h=\sqrt{56.2142}\,V_n^{1/n}\in(1.36748103,1.36748104)$. Write $x_i=\log g_i$. The exact update gives $x_{i+1}=a x_i-\log(s_i/g_i)/n$. In particular

$$
 \sum_{i=1}^j a^{j-i}\log(s_i/g_i)
 = n(a^j x_1-x_{j+1}).
$$

At $j=405$ a crossing requires this weighted sum to exceed $46.18298$ nats. Both $s_i\le q$ and $s_i\le h g_i$ hold. If $s_i/g_i\le b$, define its scalar lower update

$$
 F_b(x)=\max\{x-Q/n,\ ax-\log(b)/n\}.
$$

In particular $F_h$ is the certified floor written in log-GH units. [Part 114](wall1_idea_drift.md) · [Certified determinant floor](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledCertifiedBounds.lean)

**Ordering lemma.** Given at most $k$ exceptions to $s_i\le b g_i$ in the first $j$ draws, with $0<b\le h$, one has

$$
 x_{j+1}\ge F_h^{\,k} F_b^{\,j-k}(x_1),\qquad 0\le k\le j. \tag{2}
$$

Both maps are increasing and $F_h\le F_b$. In the four affine branches of $F_h F_b$ and $F_b F_h$, the double-period branch agrees. Both mixed branches of $F_h F_b$ are at most $a x-(aQ+\log b)/n$, a mixed branch of $F_b F_h$. The double-Hermite branches compare by $a\log b+\log h\ge a\log h+\log b$. Thus moving an exceptional cap later weakens the floor. This proves (2), including the initial steps where the period cap is active.

| Incoming draw | $g$ floor, rounded down | $\log(V_n\,34.807^n)-\log D_{i-1}^{\rm floor}$, nats | Minimum number of $s_i>1.10g_i$ in preceding draws from (2) |
|---:|---:|---:|---:|
| 396 | 34.71350 | 1.3610 | 369 |
| 401 | 33.41938 | 20.5853 | 216 |
| 406 | 32.18553 | 39.6205 | 100 |

In draw order the eleven counts are $369,334,302,272,243,216,191,167,144,122,100$. For draw 406 the floor from 99 exceptions is $34.81859499\ldots$. Allowing 100 reduces it to $34.80628356\ldots$. The equality path that takes the largest permitted winner at each step realizes these lower floors in the scalar relaxation. Simultaneous attainment by a sequence of actual framed lattices has not been shown. A single uniform cap $s_i/g_i\le1.18197$ would deterministically exclude the crossing through draw 406. The critical squared Hermite coefficient in this calculation is between 41.9969 and 41.9970, compared with the available 56.2142.

As a quantitative test of the missing probability input, if (1) at $r=1.10 g_i$ were at most 0.126 on every incoming history through draw 405, the probability of **any** crossing would be at most

$$
 \Pr\{\operatorname{Bin}(405,0.126)\ge100\}<2.58815\cdot10^{-11}.
$$

Sequentially sample each binary long-winner indicator by comparing a fresh uniform random variable with its conditional probability, then sample the remaining transition given that indicator. This couples the indicators below independent Bernoulli variables with the larger parameter. It applies to all eleven draws at once by (2). For the original $3.8\cdot10^{-13}$ allowance the sufficient parameter 0.117 gives an upper bound of $3.35783\cdot10^{-13}$. Neither conditional parameter has been established. With just the period and Hermite caps the scalar relaxation permits probability one for a crossing.

There is also an unconditional upper bound from the transition law. Let $Z$ count zero raw columns among the 405 fresh columns. Their independence gives $Z\sim\operatorname{Bin}(405,q^{-400})$. Each zero column supplies the unit-height vector with zero displacement, hence $s_i\le1$. On that draw the determinant can only increase. Monotonicity of the floor update implies that after any prefix with $m$ nonzero columns the determinant is at least the floor after $m$ ordinary updates. If $Z\ge11$, every prefix has at most 394 nonzero columns. The scalar GH floors decrease up to this horizon, and after 394 updates the floor is $34.97986519\ldots>34.807$. Consequently

$$
 \Pr(\exists i\in[396,406]:g_i<34.807)
 \le 1-\Pr\{Z\ge11\}.
$$

The subtracted mass has base-ten logarithm in $(-15477.160,-15477.159)$. The term for exactly eleven successes gives the lower endpoint and the union over eleven-element subsets gives the upper endpoint. This actual-law estimate quantifies how little is obtained by using only compulsory zero-column visits. The probability of the other histories crossing remains undetermined.

## A tighter projected-ball bound

Let $d=505, B=d/2, R^2=\sqrt2\,(1352/\sqrt3)$. For any of the twelve horizontal radii $r=\sqrt{R^2-k^2}$ and every projected grid $K$ at entry,

$$
 \#(K\cap\overline B_r)\ <\ 1.664\,V_d r^d/\det K. \tag{3}
$$

This count includes both signs and the origin.

Set $\beta=B/r^2, X(y)=\beta\|y\|^2-B$. Give $X(y)$ mass $\det K\,(\beta/\pi)^B e^{-\beta\|y\|^2}$ for each $y\in K$, defining a finite measure $\mu$. Its continuum counterpart $\nu$ is the law of a rate-one gamma variable of shape $B$, shifted by $-B$. With the angular-frequency Fourier convention, complex Gaussian Poisson summation gives

$$
 |\widehat\mu(u)-\widehat\nu(u)|
 \le(1+u^2)^{-d/4}
 \left[\left(1+\frac{2e^{-v}}{1-e^{-3v}}\right)^d-1\right],
 \quad v=\frac{\pi^2}{\beta(1+u^2)}.
$$

Indeed $K^*$ is an integer section that restricts injectively to $d$ integer coordinates without increasing norms. Removing the dual origin gives the difference above. Taking the largest $\beta$, and separate monotone endpoints on each frequency bin of width 0.01, makes the bound less than $10^{-8}$ for $|u|\le10$. [Part 161, projected-grid Poisson estimate](wall1_band_plane_hits.md)

Let $H_0(x)=e^x\mathbf1_{x\le0}$ and use the probability density

$$
 J(y)=\frac5\pi\left(\frac{\sin(5(y-0.3))}{5(y-0.3)}\right)^2.
$$

Its Fourier transform vanishes outside $[-10,10]$ by the triangle transform. Set $m=\int_0^\infty e^{-y}J(y)\,dy$. Lower sums on $[0,0.9]$ already give $m>0.60229$. On $x\le0$, $(H_0*J)(x)=e^x\int_x^\infty e^{-y}J(y)\,dy\ge m H_0(x)$, including $x=0$. On $x>0$ the same majorization follows by positivity. [Osgood, *The Fourier Transform and Its Applications*, triangle transform](https://see.stanford.edu/materials/lsoftaee261/book-fall-07.pdf)

The convolution integrates to one and its transform has absolute value at most one. Fourier inversion bounds its two integrals against $\mu,\nu$ within $10^{-8}(10/\pi)$. Its integral against $\nu$ is at most the maximum gamma density $f_*=(B-1)^{B-1}e^{1-B}/\Gamma(B)$. Undoing the tilt for the closed ball yields the following full-ball coefficient.

$$
 \frac{\det K\,\#(K\cap\overline B_r)}{V_d r^d}
 =A\int H_0\,d\mu\le
 \frac{A(f_*+10^{-8}\,10/\pi)}{m}<1.664,
 \qquad A=e^B\Gamma(B+1)/B^B.
$$

In particular $Af_*=e(1-1/B)^{B-1}$. This proves (3).

## Charge over the eleven draws

At height $1\le k\le12$ each grid point selects one compatible mark, with probability $1/|H|$. Equation (3), $D=|H|\det K$, and summation over the horizontal radii give the per-entry charge

$$
 w(g)=0.608(R/g)^{506},
 \qquad
 1.664\sum_{k=1}^{12}\frac{V_{505}(R^2-k^2)^{505/2}}{V_{506}R^{506}}<0.608.
$$

Selection, the open lower cutoff, and the plane and gate tests can only decrease the joint hit mass.

Fix a threshold $t$ from the table below, let $c=0.945t>30.5$ and $T=R/0.945$. A potentially contributing entry has $t\le g<T$ and old minimum $>c$, since the residual winner is longer than $0.945g$. Use exactly these predictable entry tests. Register such an entry when its realized winner exceeds $c$. Its conditional registration probability $p$ is at least $1-C(0.945)^{506}$, $C=1.422743743939$, by the Part 193 short positive-height bound at $c\ge52/\sqrt3$. This use of the short-winner tail only corrects the registration probability.

Between successive registered entries the incoming determinant decreases by a factor greater than $c$. The Part 215 separation proof applies to this $c$. If the height kernel of the intervening lifted winners has positive rank $e\le 10$, its covolume is greater than $c$ in rank one and at least $(\lambda_1(M)/\sqrt e)^e>c$ otherwise. The integer height image has covolume at least one. With trivial kernel the triangular height matrix forces every subsequent winner length to be at least one and the first exceeds $c$. This proves the separation for arbitrary intermediate draws. Since $(T/t)^{506}<c^2$ in the table, at most **two** entries can register on one path. Their reciprocal determinants sum to at most $(1+1/c)/(V_{506}t^{506})$. [Part 215, separation and predictable weighting](wall1_fresh_mark_extension.md)

Conditional expectation equates the expected sum of $w(g)$ on the tested entries with the expected sum of $w(g)/p$ on the registered entries. It follows under the original chain law that the joint vertical residual charge at $g\ge t$ is at most

$$
 U(t)=\frac{(1+1/c)\,0.608(R/t)^{506}}{1-C(0.945)^{506}}.
$$

Each row uses the full budget for its own split. Upper bounds round up and available allowances round down.

| $t$ | Upper bound on high-$g$ charge | Available for smaller $g$, at least |
|---:|---:|---:|
| 34.875 | $1.40040\cdot10^{-11}$ | $5.08460\cdot10^{-11}$ |
| 34.807 | $3.75987\cdot10^{-11}$ | $2.72513\cdot10^{-11}$ |
| 34.8 | $4.16270\cdot10^{-11}$ | $2.32230\cdot10^{-11}$ |
| 34.77 | $6.44035\cdot10^{-11}$ | $4.4655\cdot10^{-13}$ |

The crossing $U(t)=6.485\cdot10^{-11}$ lies between 34.7695 and 34.7696. Decreasing the split to the certified floor cannot make this majorant close the budget. At $t=34.807$ the conditional 0.126 criterion above would suffice. The distribution of the visited states and their void probabilities in (1) still limit the small-scale estimate.

## Reproduction

Run the embedded verifier from the existing scripts directory. The finite-state law above is specified symbolically. The verifier checks the scalar extremal schedules, exact binomial tails, Fourier error, ball coefficient and actual-law high-$g$ majorants.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_small_g_frequency.md | python -B -)
```

```python
from fractions import Fraction
from math import comb
from mpmath import iv

iv.dps = 65
I = iv.mpf
n, d = 506, 505
B, a = I(d)/2, I(d)/n
qlog, target = iv.ln(3329), I("34.807")
vol = [I(1), I(2)]
for j in range(2, n+1):
    vol.append(2*iv.pi*vol[j-2]/j)
lv = iv.ln(vol[n])
x1 = (400*qlog-lv)/n
logh = (iv.ln(I("56.2142"))/2 + lv/n)
logb = iv.ln(I("1.10"))
assert I("1.36748103") < iv.exp(logh) < I("1.36748104")
drop = 400*qlog-lv-n*iv.ln(target)
assert I("2308.9795681") < drop < I("2308.9795682")
assert n*(a**405*x1-iv.ln(target)) > I("46.18298")

def schedule(steps, exceptions, low=logb):
    x = x1
    for j in range(steps):
        cap = low if j < steps-exceptions else logh
        period, hermite = x-qlog/n, a*x-cap/n
        assert period > hermite or hermite > period
        x = max(period, hermite)
    return iv.exp(x)

counts = [369,334,302,272,243,216,191,167,144,122,100]
for j, k in enumerate(counts, 395):
    assert schedule(j, k-1) > target > schedule(j, k)
for j, low, gap in [(395,"34.71350","1.3610"),
                    (400,"33.41938","20.5853"),
                    (405,"32.18553","39.6205")]:
    g = schedule(j, j)
    assert I(low) < g < I(low)+I("0.00001")
    assert abs(n*iv.ln(target/g)-I(gap)) < I("0.00005")
for k, low in [(99,"34.81859499"),(100,"34.80628356")]:
    assert I(low) < schedule(405,k) < I(low)+I("1e-8")
assert schedule(405,0,iv.ln(I("1.18197"))) > target
for gamma, above in [("41.9969",True),("41.9970",False)]:
    floor = schedule(405,0,iv.ln(I(gamma))/2+lv/n)
    assert (floor > target if above else floor < target)

assert I("34.97986519") < schedule(394,394) < I("34.97986520")
# The floor map is increasing and its first update decreases the initial value.
assert schedule(1,1) < iv.exp(x1)
log10 = iv.ln(10)
pz = iv.exp(-400*qlog)
eleven_upper = (iv.ln(comb(405,11))-4400*qlog)/log10
# (1-pz)^394 >= 1-394*pz > 1/2.  Use log(1-x) >= -2x for x <= 1/2.
assert 394*pz < I(1)/2
eleven_lower = eleven_upper - 2*394*pz/log10
assert I("-15477.160") < eleven_lower and eleven_upper < I("-15477.159")

for p, cap in [("0.117","3.35783e-13"),("0.126","2.58815e-11")]:
    p = Fraction(p)
    prob = sum(comb(405,k)*p**k*(1-p)**(405-k) for k in range(100,406))
    assert prob < Fraction(cap)

R2 = iv.sqrt(2)*1352/iv.sqrt(3)
R = iv.sqrt(R2)
beta_max = B/(R2-144)
eps = I("1e-8")
for j in range(1000):
    left, right = I(j)/100, I(j+1)/100
    v = iv.pi**2/(beta_max*(1+right**2))
    theta = 1+2*iv.exp(-v)/(1-iv.exp(-3*v))
    assert (1+left**2)**(-B/2)*(theta**d-1) < eps

mass = I(0)
for j in range(900):
    # Absolute argument furthest from the sinc peak, in the first lobe.
    z = I(max(abs(j-300),abs(j+1-300)))/200
    assert 0 < z < iv.pi
    mass += iv.exp(-I(j+1)/1000)*5/iv.pi*(iv.sin(z)/z)**2/1000
assert mass > I("0.60229")
A = iv.exp(B)*iv.gamma(B+1)/B**B
assert (iv.exp(1)*(1-1/B)**(B-1)+A*10/iv.pi*eps)/I("0.60229") < I("1.664")
layers = sum(vol[d]*(R2-k*k)**B for k in range(1,13))/(vol[n]*R**n)
assert I("1.664")*layers < I("0.608")

budget, ratio = I("6.485e-11"), I(".945")
failure = I("1.422743743939")*ratio**n
assert failure < 1

def charge(threshold):
    t = I(threshold)
    c = ratio*t
    assert c > I("30.5") > 52/iv.sqrt(3)
    assert (R/(ratio*t))**n < c**2
    return (1+1/c)*I(".608")*(R/t)**n/(1-failure)

for t, cap, spare in [
    ("34.875","1.40040e-11","5.08460e-11"),
    ("34.807","3.75987e-11","2.72513e-11"),
    ("34.8","4.16270e-11","2.32230e-11"),
    ("34.77","6.44035e-11","4.4655e-13"),
]:
    value = charge(t)
    assert value < I(cap) and budget-value > I(spare)
assert charge("34.7695") > budget > charge("34.7696")
print("Verified the determinant schedules, binomial tails, full-ball bound and four budget splits.")
```

## Audit

**Verdict.** Both high-$g$ charge bounds and the 100-winner necessity hold for the original finite chain. The binomial bound holds under the stated conditional ceiling. The frequency of small-$g$ entries at the required scale remains open. No numerical correction is needed.

**High-$g$ charge.** The closed-ball majorant covers points at the boundary because $(H_0*J)(0)=m$. The translated sinc-squared density has angular-frequency support in $[-10,10]$, and integrating the transform error over that interval gives the factor $20/(2\pi)$. An independent 80-digit interval evaluation on frequency bins of width $0.005$ bounded the error by $6.228\cdot10^{-9}$. The stated lower sum for $m$ exceeds $0.60229943$. With the note's rounded inputs, the full-ball coefficient is below $1.663628$ and the twelve-layer coefficient is below $0.607169$. Each height $1$ through $12$ is invertible on $K/M$, so counting a point costs $1/|H|$ even when several points use the same mark. The Part 193 short positive-height coefficient at $52/\sqrt3$ is below $1.422743743939$ on independently summing its 4096 bins.

On a residual hit, $\lambda_1(M)\ge s>0.945g\ge c$. The entry tests therefore retain the hit and are measurable before the mark is drawn. The lifted intervening winners have GS lengths $s_i$, so their covolume is the ratio of the two incoming determinants. For two registered draws at most ten freezes apart, a nontrivial height kernel gives this ratio $>c$ by the old minimum and the rank-$e$ covolume bound. With trivial kernel the triangular height matrix has nonzero diagonal, giving the same strict ratio since the first winner exceeds $c$. Three registrations would require a ratio $>c^2$ within a determinant range of ratio $(T/t)^{506}<c^2$. Weighting the at most two registered entries by the reciprocal of their conditional registration probabilities is thus valid before imposing the gates. Direct evaluation gives $3.7598695607\cdot10^{-11}<U(34.807)<3.7598695609\cdot10^{-11}$ and $6.4403446844\cdot10^{-11}<U(34.77)<6.4403446845\cdot10^{-11}$.

**Crossing count.** The initial graph basis is block triangular with determinant $q^{400}$. A height-one append preserves covolume on passing from the rank-505 retained lattice to the rank-506 window. Removing a primitive shortest vector then divides covolume by its GS length $s_i$. Thus draw $i$ uses exactly $i-1$ factors, and the Hermite cap is $s_i\le\sqrt{56.2142}\,D_{i-1}^{1/506}$. The pure height-$q$ vector supplies the other cap. For an independent check of the ordering lemma, I minimized the log-determinant floor over both choices of the last cap at every step and exception count, starting at $400\log q$. The monotonicity of both updates makes this recursion exact for the scalar relaxation. Rounding its endpoints outward at each step on a $10^{-32}$ grid reproduced all eleven counts. At draw 406 the 99-exception floor is in $(34.8185949913,34.8185949914)$ and the 100-exception floor is in $(34.8062835689,34.8062835690)$. A crossing at any of the eleven draws therefore implies at least 100 long winners in the first 405 draws.

**Conditional probability.** For each incoming history let $p_i$ be the probability of a long winner. A fresh independent uniform $U_i$ realizes its indicator as $\mathbf1_{U_i\le p_i}$, after which the transition can be sampled from its original conditional law given that indicator. If $p_i\le0.126$ almost surely at each of the first 405 draws, this gives pathwise domination by $\sum_{i=1}^{405}\mathbf1_{U_i\le0.126}$. One tail covers all eleven crossing times. Exact rational summation gives $2.5881467825\cdot10^{-11}<\Pr(\mathrm{Bin}(405,0.126)\ge100)<2.5881467826\cdot10^{-11}$. The ceiling on $p_i$ remains a hypothesis.

The embedded verifiers for this note, Part 212 and Part 215, and the vertical flag-moment reference script all passed on rerun.
