# Long winners and earlier column constraints for the last horizontal cases

**Draw 406 requires at least 305 long winners to enter the remaining mixed range.** A uniform conditional long-winner ceiling of $0.5$ would give a crossing probability below $9.850\cdot10^{-28}$. Even $0.75$ on draws 11–405 would cover the mixed piece for $2.215\cdot10^{-12}$ when the fresh-mark probability on draw 406 is retained. Neither ceiling is proved. Unconditionally one can extend R87's paid mixed range down to $g=32.75$, leaving more than $4.0214\cdot10^{-12}$ for the narrower mixed range and the wholly old remainder.

**A wholly old hit on draw 406 forces earlier modular constraints.** Its full raw lift has suffix-coordinate rank at least 36 modulo 3329. At least five independent coordinates occur after draw 50, and its last used draw is at least 57. These constraints use the dual gate on the *earlier* raw graphs. A fixed lift with 36 independent pivots costs at most $3329^{-14400}$ conditional on the initial columns. The selected lift varies with the columns. For either survival or replacement, terminal hits whose full lift has fewer than 45 suffix pivots have joint mass below $2.200\cdot10^{-21}$. Four such rank restrictions together cost less than $6.227\cdot10^{-16}$. The mass on the remaining selected lifts is open. [R87 and audit](wall1_z1_remainder.md#audit) · [Parts 205–217](../PROOF_GAP.md)

## The count at 32.8

Let $n=506, q=3329, V_j=\pi^{j/2}/\Gamma(1+j/2)$. In this note $D_i=V_ng_i^n$ is the determinant **incoming** to draw $i$, so $D_1=q^{400}$ and $D_{i+1}=D_i/s_i$. Write $x_i=\log g_i, A=505/506, h=\sqrt{56.2142}\,V_n^{1/n}$. A long winner satisfies $s_i>1.10g_i$. For cap $b\in\{1.10,h\}$ put
$$
 F_b(x)=\max\{x-\log(q)/n,\ Ax-\log(b)/n\}.
$$
With at most $k$ long winners, the Part 216 ordering lemma gives $g_{406}\ge\exp(F_h^kF_{1.10}^{405-k}(x_1))$. The increasing maps use the period as well as the Hermite bound. Moving an exceptional cap later weakens the floor. The two adjacent values are

| Long winners allowed | Draw-406 scalar floor |
|---:|---:|
| 304 | $(32.80214011,32.80214012)$ |
| 305 | $(32.79440794,32.79440795)$ |

Thus 305 is necessary and sharp for these two scalar caps. The available 398 draws after the seven compulsory short draws suffice in the scalar relaxation. Attainment by a sequence of lattices is open. [Part 216](wall1_small_g_frequency.md) · [Part 217](wall1_long_winner_ceiling.md)

For $N$ tested draws with conditional long probability at most $p$ before each mark, let $B(N,p)=\sum_{k=305}^N {N\choose k}p^k(1-p)^{N-k}$. Coupling each indicator with a fresh uniform bounds the crossing probability by $B(405,p)$, or $B(398,p)$ after using the seven period tests. At $p=1/2$ the respective values lie in $(1.67229,1.67230)10^{-25}$ and $(9.84943,9.84944)10^{-28}$. Against the full conservative balance $7.0139\cdot10^{-12}$, the break-even $p$ lies in $(0.59180,0.59181)$ and $(0.60510,0.60511)$, respectively. Part 217's proved uniform ceiling $p_*=1-6.33\cdot10^{-65}$ gives a binomial **majorant** greater than $1-10^{-5941}$, since its complement requires at least 94 failures. This evaluates the certificate only.

### Retaining the fresh-mark weight

Let $W_1$ be R87's all-height mixed numerator. At any eligible entry $g>32.32$, the conditional mixed charge is at most $C=W_1/(V_n32.32^n)<4.62329\cdot10^{-9}$. Indeed R87's separated majorant $U$ at 32.8 satisfies
$$
 W_1/(V_n32.8^n)\le(25/26)U,\qquad U<2.769\cdot10^{-12}.
$$
The crossing is known before drawing the last mark, so its probability can be multiplied by $C$ in a joint upper bound. The future gates are imposed only after taking this bound. [R87, averaging and summing](wall1_z1_remainder.md#averaging-and-summing-the-late-draws)

For comparison let $x_{11}^*=F_h^{10}(x_1),\ w_i=A^{405-i},\ b=\log(1.10),\ \delta=\log h-b$. Iterating $x_{i+1}\ge A x_i-(b+\delta I_i)/n$ with long indicators $I_i$ shows that a crossing requires
$$
 \sum_{i=11}^{405}w_i I_i>T=
 \frac{n(A^{395}x_{11}^*-\log32.8)-b\sum_{i=11}^{405}w_i}{\delta}
 \in(228.64623,228.64624).
$$
Under a conditional ceiling $p$ on these draws, the crossing costs at most $E_p(z)=e^{-zT}\prod_i(1+p(e^{zw_i}-1))$ for $z>0$, by iterated conditional expectation. At $p=0.75,z=0.706$, this gives $E_p(z)<0.00047903$ and $CE_p(z)<2.215\cdot10^{-12}$. At $p=0.7,z=1.057$ the joint charge is below $7.591\cdot10^{-17}$. The first hypothesis alone would leave more than $4.7989\cdot10^{-12}$ of R87's original balance for the wholly old cases. For $p=0.75$, a sufficient missing estimate on each unresolved entry is coverage of at least one quarter of the marks at radius $1.10g_i$. In Part 217's collision notation a height-one certificate $|H| B/A_1^2\le4$ suffices, where $A_1$ is the total label count and $B$ the sum of squared multiplicities. The available large mean does not establish this collision estimate. [Part 217, exact prefix moments](wall1_long_winner_ceiling.md#exact-first-and-second-moments-on-one-prefix)

**Unconditional budget option.** R87 already pays for draws 403–405 at every scale. Replace its single charge $U$ by $W_1/(V_n32.75^n)$ for all draw-406 mixed hits with $g\ge32.75$. The increase is at most $[(25/26)(32.8/32.75)^{506}-1]U<2.99249\cdot10^{-12}$. This leaves the open mixed interval $32.32<g<32.75$, with height 1–4 and inherited minimum in $(28.22,29.2)$, and more than $4.0214\cdot10^{-12}$ for it and the old terms together. This allocation and the hypothetical $p=0.75$ allocation use the same original balance.

## The raw lift on a coordinate prefix

Suppose the first hit is wholly old at $i$. Write $a=1352/\sqrt3, R=(\sqrt2a)^{1/2}$, and $L_t$ for the raw graph through draw $t$, of rank $505+t$ and determinant $q^{400}$. The winner and the plane lift to a saturated triple in the incoming retained lattice. Take its full inverse image $J\subset L_{i-1}$, including all $i-1$ frozen directions. Then $k=\operatorname{rank}J=i+2$. Removing the frozen directions in order divides its covolume by their length product $q^{400}/D_i$. The remaining triple has determinant $s_i\det P\le Ra$. Thus
$$
 \det J\le q^{400}Ra/D_i. \tag{1}
$$
In particular the raw primal gate implies $\det J>(250/\sqrt{\gamma_k})^k$. With Blichfeldt's cap at rank 408 this gives $g_{406}<191.992$. This necessary test admits values far above 32.8. [Part 194, old triple](wall1_z1_horizontal.md#the-horizontal-quotient-and-its-two-kinds-of-planes) · [Blichfeldt bound, equation (22)](https://www.dpmms.cam.ac.uk/~taf1000/papers/n-descent-III.pdf)

For $0\le t<i$, map $J$ onto its coordinate image $Y\subset\mathbb Z^{i-1-t}$ on the suffix **after** $t$, through $i-1$. Let $r=\operatorname{rank}Y$, and $u=\dim_{\mathbb F_q}(Y\bmod q)$. The raw kernel $J_t$ is a section of $L_t$ of rank $k-r$, by zero extension and saturation. The projected quotient of $J$ perpendicular to the kernel maps to $Y$ by an injective contraction. Hence
$$
 \det J_t\le\det J/\det Y,\qquad \det Y\ge q^{r-u}.
$$
The latter inequality follows by Smith normal form inside the primitive saturation of $Y$ in the integer grid. Exactly $r-u$ invariant factors are divisible by $q$. The saturation has covolume at least one. The formulas also hold for the empty coordinate image.

**Prefix rank test.** Put $c=503+t-i+r$, $H(c)=\log[(2/\pi)^{c/2}\Gamma(2+c/2)]$. The complement of $J_t$ in $L_t^*$, meaning the section perpendicular to its real span, has rank $c$ and determinant $\det J_t/q^{400}$. This follows by dualizing the projected quotient. Its minimum is at least the raw-prefix floor $R_0(t)$. Hermite, (1), and the image-index bound give
$$
 \boxed{\ \log D_i\le \log(Ra)+H(c)-c\log R_0(t)-(r-u)\log q.\ } \tag{2}
$$
All floors appearing here hold on the specified gate, and no new exit probability is charged. The verifier checks the standard Blichfeldt cap directly through $H(c)$. [Part 172, raw dual gates and complementary sections](wall1_transference.md) · [Part 205, both raw gates](wall1_doubly_gated.md)

For fixed $t,i,u$, maximize the right side over $u\le r\le i-1-t$, and compare it with the pathwise floor on $\log D_i$. The following entries are the least modular ranks allowed by this test. The last column bounds the last used draw $j$ of R87 by taking a cut with zero suffix rank. The verifier treats every cut directly for this column.

| Wholly old first hit $i$ | Rank after 0 | Rank after 25 | Rank after 50 | Lower bound on $j$ |
|---:|---:|---:|---:|---:|
| 350 | 12 | 0 | 0 | 21 |
| 380 | 24 | 10 | 0 | 41 |
| 395 | 31 | 16 | 0 | 50 |
| 405 | 36 | 20 | 4 | 56 |
| 406 | 36 | 21 | 5 | 57 |

For example at 406, cut 0, the best $g$ allowed with $u=35$ is below 31.84338. At cut 50, $u=4$ gives $g<32.08191$. Both lie below the pathwise floor $32.18553$. At fixed $g\ge32.8$ the three required ranks on draw 406 increase to 38, 22 and 6. With all 405 suffix coordinates independent, (2) at $t=405$ gives only $g<212.190$. More generally, with full suffix rank at every cut $(r=u=405-t)$, **every** inequality (2) allows $g=34$. The raw primal bound following (1) also allows it. This is a check on the scalar inequalities. Attainment of those data by a gated history is unknown.

**Which marks are counted?** Fix an integer generating matrix for $J$ in advance. Condition on the raw columns through cut $t$. In each horizontal row the congruences for membership of these generators have coefficient rank $u$ in the unread columns through $i-1$. They have probability either zero or $q^{-u}$. The rows are independent, so membership costs at most $q^{-400u}$. Echelon elimination with the pivots taken from the right gives $u$ distinct earlier columns whose values are prescribed once preceding columns have been read, for this fixed matrix. In particular these are genuine modular restrictions even when some integer heights exceed $q$. The pivots may belong to previously frozen winners. Equation (2) gives neither a bounded-length candidate list for every pivot nor a bound on the number of lifts selected across histories. A union over the fixed lifts must retain its multiplicity or impose selection. The mark at the wholly old hit itself remains free until the horizontal comparison. [R87, last used coordinate](wall1_z1_remainder.md#which-earlier-mark-a-wholly-old-hit-can-charge) · [Part 211, cost of dropping selection](wall1_history_free_compression.md)

For comparison, on draw 172 the floor-based test (2) at *every cut* permits an entirely initial lift $(r=u=0)$. Thus the late rank lower bounds give no universal paid earlier-mark event for the whole 172–406 interval. On uncharged first hits, both $\Pr(B_o\cap S)$ and $\Pr(B_o\cap S^c\cap A_{406})$ still require selected-history bounds. Equation (2) restricts the creation history of either term, also when the eventual replacement has another origin. R87's example fails the raw minimum gate at draw zero. None of the scalar feasibility checks supply a gated replacement example. [Part 208, survival and replacement](wall1_z1_terminal_law.md) · [R87, terminal accounting](wall1_z1_remainder.md#terminal-accounting)

## A charge that also covers terminal replacements

Let $P_*$ be **any** hit plane in the retained lattice after draw 406, allowing the first plane to have disappeared. Its full inverse image $J_*$ in the 911-dimensional raw graph has rank 408. The 406 frozen lengths have product $q^{400}s_{406}/D_{406}$, and hence
$$
 \det J_*/q^{400}\le a s_{406}/D_{406}
 \le a\sqrt{56.2142}\,(D_{406}^*)^{-505/506}=e^{-K}.
$$
Here $D_{406}^*$ is the pathwise determinant floor. The last bound uses the global Hermite cap and the negative exponent. It holds for every final winner. At the floor the winning-length cap is below 44.01312. The section argument above now applies to the suffix from $t+1$ **through 406**, with the same $c=97+t+r$ and with $r\le406-t$. In particular on a raw-prefix dual floor $\rho_t$ it requires
$$
 K\le H(c)-c\log\rho_t-(r-u)\log q. \tag{3}
$$
At the original gate radii this already forces ranks $36,21,5$ after cuts $0,25,50$ for every terminal hit. The same argument applies to the creation at draw 406 of a wholly old plane using its shorter list of 405 suffix coordinates and the stronger bound (1).

We can afford to raise four of the dual floors. At cut $t$, take $m=505+t$, $b=m/[2(q\rho_t)^2]$. For $\rho_t<1$, any nonzero raw dual vector through this radius has a representation $(z,w)/q$ with $z\not\equiv0\pmod q$. A fixed such pair requires $105+t$ uniform scalar congruences. Both signs give the same event. Summing the Gaussian majorant for the integer ball and applying one-dimensional Poisson summation gives
$$
 \Pr(\lambda_1(L_t^*)\le\rho_t)\le
 \frac{e^{m/2}(\pi/b)^{m/2}}{2q^{105+t}}
 \left(1+\frac{2e^{-\pi^2/b}}{1-e^{-3\pi^2/b}}\right)^m.
$$
The geometric series bounds the nonzero dual Gaussian terms since $j^2\ge1+3(j-1)$ for $j\ge1$. Enlarging the integer count to include the origin preserves the upper bound. The four raw events depend only on their respective prefixes and can be charged before any selection. [Part 172, raw dual first moment](wall1_transference.md#audit)

| Cut $t$ | Raised floor $\rho_t$ | Necessary terminal modular rank after $t$ | Joint mass of any terminal hit violating this row |
|---:|---:|---:|---:|
| 0 | 0.00803798 | 45 | $<2.200\cdot10^{-21}$ |
| 25 | 0.01106009 | 27 | $<3.085\cdot10^{-24}$ |
| 50 | 0.01539900 | 10 | $<1.423\cdot10^{-17}$ |
| 63 | 0.01795461 | 1 | $<6.085\cdot10^{-16}$ |

For each row, (3) fails for every smaller $u$, including all possibilities $r>u$. The four unrounded raw exit bounds sum to less than $6.227\cdot10^{-16}$. In particular we can charge all terminal hits whose full raw lift uses no column after 63, and all histories with a rank-deficient lift in any of the other indicated senses, **once** across both old terminal terms. These ranks constrain the full lift. Adding a plane to the frozen section increases the modular image rank by at most two, since the saturated kernel admits two basis lifts. Applying the same calculation to the frozen section alone gives ranks at least **43, 26, 9 and 0** at the four cuts. Indeed its determinant bound drops the factor $a$, and its complementary rank increases from $c$ to $c+2$. This quantifies how much of the terminal rank test can already be explained by the frozen winners. For an earlier first hit, a pivot of the terminal lift can also occur after that first hit.

Combined with the unconditional mixed allocation at 32.75, this leaves **more than $4.0207\cdot10^{-12}$** for the narrower mixed piece and the old terms whose terminal lifts meet every row. Using R87's original 32.8 allocation leaves more than $7.0132\cdot10^{-12}$ after the four exits. Neither balance is an upper bound on the outstanding mass.

## Reproduction

Run the embedded Python verifier from the research scripts directory to keep the single-file scope. It uses outward intervals for the schedules, the budget inequalities and all prefix-rank comparisons, and exact rational binomial tails.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_z1_last_pieces.md | python -B -)
```

```python
from fractions import Fraction as Fr
from math import comb
from mpmath import iv

iv.dps = 65
I = iv.mpf
n, q = 506, 3329
log = iv.ln
exp = iv.exp
Q = log(q)
A = I(505)/506
V = [I(1), I(2)]
for d in range(2, 912):
    V.append(2*iv.pi*V[d-2]/d)
lv = log(V[n])
x1 = (400*Q-lv)/n
b = log(I('1.10'))
h = log(I('56.2142'))/2 + lv/n

def step(x, cap):
    period, hermite = x-Q/n, A*x-cap/n
    assert period < hermite or hermite < period
    return max(period, hermite)

def schedule(k):
    x = x1
    for j in range(405):
        x = step(x, b if j < 405-k else h)
    return exp(x)

assert I('32.80214011') < schedule(304) < I('32.80214012')
assert I('32.79440794') < schedule(305) < I('32.79440795')

def tail(N, p):
    p = Fr(p)
    return sum(comb(N,k)*p**k*(1-p)**(N-k) for k in range(305,N+1))

budget = Fr('7.0139e-12')
for N, lo, hi, p0, p1 in (
        (405, '1.67229e-25','1.67230e-25','.59180','.59181'),
        (398, '9.84943e-28','9.84944e-28','.60510','.60511')):
    assert Fr(lo) < tail(N,'0.5') < Fr(hi)
    assert tail(N,p0) < budget < tail(N,p1)
assert comb(398,94)*Fr('6.33e-65')**94 < Fr('1e-5941')

floor = [None, x1]
for i in range(1,406):
    floor.append(step(floor[-1],h))
w = [A**j for j in range(395)]
T = (n*(A**395*floor[11]-log(I('32.8')))-b*sum(w))/(h-b)
assert I('228.64623') < T < I('228.64624')
U = I('2.769e-12')
def ratio(t):
    return I(25)/26*(I('32.8')/I(t))**n
C = U*ratio('32.32')
assert C < I('4.62329e-9')
for p, z, bound in [('.75','.706','2.215e-12'), ('.7','1.057','7.591e-17')]:
    p, z = I(p), I(z)
    E = exp(-z*T + sum(log(1+p*(exp(z*y)-1)) for y in w))
    assert E < I('.00047903') and C*E < I(bound)
extra = U*(ratio('32.75')-1)
assert extra < I('2.99249e-12') and I('7.0139e-12')-extra > I('4.0214e-12')

a = I(1352)/iv.sqrt(3)
logRa = log(a*iv.sqrt(iv.sqrt(2)*a))
H = [I(c)/2*log(2/iv.pi)+iv.loggamma(2+I(c)/2) for c in range(506)]
R0 = []
for t in range(406):
    m = 505+t
    R0.append((exp(((105+t)*Q+log(I('.001')/408)-log(V[m]))/m)-iv.sqrt(m)/2)/q)
assert all(r >= R0[0].a for r in R0)
# For fixed u, each unit increment of r loses more from q than it gains
# in the Blichfeldt term. Thus the maximum in (2) is attained at r=u.
assert all(H[c+1]-H[c] < Q+log(R0[0]) for c in range(97,502))
LR = [log(r) for r in R0]

def upper(i,t,u):
    c = 503+t-i+u
    assert 97 <= c <= 502 and 0 <= u <= i-1-t
    return logRa+H[c]-c*LR[t]

def least_rank(i,t,logD):
    for u in range(i-t):
        bound = upper(i,t,u)
        assert bound < logD or bound > logD
        if bound > logD:
            return u
    raise AssertionError("no rank survives")

rows = [(350,[12,0,0],21),(380,[24,10,0],41),(395,[31,16,0],50),
        (405,[36,20,4],56),(406,[36,21,5],57)]
for i, ranks, first in rows:
    Dlog = lv+n*floor[i]
    assert [least_rank(i,t,Dlog) for t in (0,25,50)] == ranks
    for t in range(i):
        assert upper(i,t,0) < Dlog if t < first else upper(i,t,0) > Dlog

def gcap(i,t,u):
    return exp((upper(i,t,u)-lv)/n)

assert I('32.18553') < exp(floor[406])
assert gcap(406,0,35) < I('31.84338') and gcap(406,50,4) < I('32.08191')
assert [least_rank(406,t,lv+n*log(I('32.8'))) for t in (0,25,50)] == [38,22,6]
raw = exp((400*Q+logRa+H[408]-408*log(250)-lv)/n)
assert 34 < raw < I('191.992') and gcap(406,405,0) < I('212.190')
assert all(upper(406,t,405-t) > lv+n*log(34) for t in range(406))
assert all(upper(172,t,0) > lv+n*floor[172] for t in range(172))
# General terminal plane, including replacement by another plane.
dmin = lv+n*floor[406]
smax_at_floor = exp(log(I('56.2142'))/2+dmin/n)
K = dmin-log(a*smax_at_floor)
assert smax_at_floor < I('44.01312')
def terminal_rhs(t,r,u,logrho):
    c = 97+t+r
    return H[c]-c*logrho-(r-u)*Q

def terminal_test(t,rho,needed):
    # For fixed r the expression increases with u. One test per r
    # covers every feasible u below needed.
    logrho = log(rho)
    for r in range(407-t):
        assert terminal_rhs(t,r,min(r,needed-1),logrho) < K
    assert terminal_rhs(t,needed,needed,logrho) > K

for cut, needed in [(0,36),(25,21),(50,5)]:
    terminal_test(cut,R0[cut],needed)
exits = I(0)
for t, radius, needed, cap in [
    (0,'.00803798',45,'2.200e-21'),(25,'.01106009',27,'3.085e-24'),
    (50,'.01539900',10,'1.423e-17'),(63,'.01795461',1,'6.085e-16')]:
    rho = I(radius)
    assert R0[t] < rho < 1
    terminal_test(t,rho,needed)
    frozen_rank = {0:43,25:26,50:9,63:0}[t]
    log_rho = log(rho)
    def frozen_rhs(r,u):
        c = 99+t+r
        return H[c]-c*log_rho-(r-u)*Q
    if frozen_rank:
        assert all(frozen_rhs(r,min(r,frozen_rank-1)) < K+log(a)
                   for r in range(407-t))
    assert frozen_rhs(frozen_rank,frozen_rank) > K+log(a)
    m = 505+t
    beta = I(m)/(2*(q*rho)**2)
    f = iv.pi**2/beta
    theta = 1+2*exp(-f)/(1-exp(-3*f))
    charge = exp(I(m)/2*(1+log(iv.pi/beta))+m*log(theta)-log(2)-(105+t)*Q)
    assert charge < I(cap)
    exits += charge
assert exits < I('6.227e-16')
assert I('7.0139e-12')-exits > I('7.0132e-12')
assert I('7.0139e-12')-extra-exits > I('4.0207e-12')
print("Verified 305 winners, exact tails, mixed allocations and raw-prefix rank bounds.")
```

## Audit

**Verdict.** All four claims hold with their stated hypotheses. The extension to $g=32.75$ and the four terminal rank charges hold under the original chain law. The two proposed long-winner ceilings remain hypotheses.

**Crossing on draw 406.** A dynamic program minimized the scalar floor over both choices at each draw, allowing an exceptional cap only after draw 7. With at most 304 and 305 exceptions it gave $32.80214011668\ldots$ and $32.79440794776\ldots$, respectively. Thus $g_{406}<32.8$ requires at least 305 long winners. Under the conditional ceiling $1/2$, the exact binomial majorant is $2^{-398}\sum_{j=0}^{93}\binom{398}{j}=9.84943837145\ldots\cdot10^{-28}$. Under the $0.75$ ceiling on draws 11–405, the weighted crossing majorant is $0.00047902197453\ldots$. The crossing is known before mark 406 is read. Multiplying by the conditional mixed charge gives a joint majorant of $2.21465360286\ldots\cdot10^{-12}$.

**Wholly old creation and terminal replacement.** At each integer suffix rank $r$, I solved (2) and (3) for the least feasible integer $u$ and minimized over $r$. For wholly old creation on draw 406 the ranks after cuts 0, 25 and 50 are at least 36, 21 and 5. Cut 56 still excludes $r=u=0$, so the last used draw is at least 57. The 36 pivots constrain the earlier columns for each fixed lift. Bounding the probability for the selected lift still requires accounting for its dependence on those columns.

For the terminal test the suffix includes draw 406. Every terminal hit plane has a rank-408 inverse image satisfying (3), regardless of when its plane first qualified. The four raised floors therefore force ranks at least 45, 27, 10 and 1 for both surviving and replacement planes. An independent sum of the one-dimensional Gaussian on the integer grid, with a geometric bound on its tail, gave a combined exit majorant of $6.22688908\cdot10^{-16}$ rounded upwards. A single union over the four raw prefix events covers both terminal cases.

**Unconditional balance.** R87 pays draws 403–405 in full. Replacing its scale charge on draw 406 pays the endpoint $32.75$ and increases the ledger by less than $2.99248645\cdot10^{-12}$. Subtracting this increase and the four exits once from the conservative $7.0139\cdot10^{-12}$ balance leaves more than $4.02079\cdot10^{-12}$. The outstanding mass consists of the residual mixed hits with $32.32<g<32.75$ and the remaining wholly old terminal cases. An upper bound on their probability within this balance remains open.

The embedded interval and exact binomial verifier and the verifiers for Parts 216–218 all passed. No correction is required.
