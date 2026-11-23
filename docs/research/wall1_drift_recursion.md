# The projected void kernel and its draw-129 initialization

The full radial void profile does not determine its next value under the marked transition of Part 108. Two rank-505 marked lattices below have the same profile at **every** radius, the same determinant and the same selected winner. At the next threshold $1.10g'$, one exceeds the 0.18 void ceiling for every mark and the other satisfies it for every mark. This example concerns the abstract transition. Their scale lies below the deterministic floor on draws 129–405 of the width-506 graph process.

For the actual graph process, the proposed raw-witness initialization fails already at draw 129. On the crossing corridor of Part 225 the appended radius is at most 641.60283. At the deterministic corridor endpoint the unconditional probability of a raw height-one witness is below $1.630\cdot10^{-130}$. Projected witnesses at this draw may be frequent. The proof below quantifies how much projection they already require at initialization. The 0.18 ceiling on draws 129–405 and the consequent bound on $Z_{\rm rem}$ remain open.

## A transition that retains the projection

Condition on the incoming history, including the tie rule. Let $M\subset K$ have mark group $H=K/M$, let $U,V$ be independent uniform marks, and write $D(x)=\min_{y\in x+M}\|y\|$ for a coset distance, using any lift of $x$. The incoming profile is $p(b)=\Pr(D(V)>b)$. For $U=u$, let $w=(a,k)$ be the primitive winner in $W_u=(M,0)+\mathbb Z(\tilde u,1)$, $s=\|w\|$, and $Q$ the projection off $w$. Distinguish the incoming GH scale $g$, the outgoing scale $g'=g s^{-1/506}$, and the *horizontal* test radius $b(u)=\sqrt{(1.10g')^2-1}$. All moving radii used below are real.

**Lemma 1 (conditional projected void).** Define $d_u(v)$ as the distance from $Q(\tilde v,0)$ to $QW_u$. For each $u$, the entire outgoing profile satisfies
\[
 p'_u(b)=|H|^{-1}\sum_{v\in H}\mathbf1_{d_u(v)>b}.
 \tag{1}
\]
For a nonhorizontal winner let $m_w=a-k\tilde u\in M$ and
\[
 M_u^+=M+\mathbb Z(m_w/k),\qquad T_u=I-aa^{\mathsf T}/s^2.
\]
Then
\[
 d_u(v)^2=\min_{y\in\tilde v+M_u^+}y^{\mathsf T}T_u y. \tag{2}
\]
Indeed a lift $z=(\tilde v+m+j\tilde u,j)$ has the same projection as $z-(j/k)w=(\tilde v+m-jm_w/k,0)$. All such $m,j$ occur. The class of $m_w/k$ has order $|k|$ modulo $M$, by primitivity of $w$ in a basis of $M$ extended by $(\tilde u,1)$. The eigenvalue in direction $a\ne0$ is $k^2/s^2$ and every perpendicular eigenvalue is one. For $a=0$, $T_u=I$. The ellipsoid at radius $b$ thus has volume $V_{505}b^{505}s/|k|$, and the extension has index $|k|$. The two factors reproduce the change of covolume. Counting distinct cosets hit by the ellipsoid still requires its orientation and overlaps. [Inverse-branch formula](wall1_inverse_branch.md#the-inverse-on-embedded-lattices)

For a horizontal winner $k=0$ one instead has
\[
 d_u(v)^2=\min_{j\in\mathbb Z}\big[j^2+
 \operatorname{dist}(P_{a^\perp}(\tilde v+j\tilde u),P_{a^\perp}M)^2\big]. \tag{3}
\]
Equation (1) follows because $V\mapsto Q_*V$ has equal fibers, also for a nontrivial kernel. Averaging (1) over $u$ gives the exact expected transition at fixed $b$ or at $b(u)$. This representation uses one horizontal ellipsoid per nonhorizontal branch and only $|j|\le b$ for a hit on a horizontal branch. [Part 108](wall1_first_tour.md) · [R100](wall1_inductive_typicality.md)

**A two-radius bound with an explicit projection term.** For any deterministic $B\ge1$ with $B\le b(u)$ for all branches, choose a nearest representative $y_j$ of $v+ju$, $j=0,1$, using a fixed tie rule. Set $z_j=(y_j,j)$, $h_j=\langle z_j,w/s\rangle$, and $E=\{\|z_0\|>B,\ \|z_1\|>B\}$. Then
\[
 \mathbb E_U p'_U(b(U))
 \le p(B)p(\sqrt{B^2-1})-
 \Pr_{U,V}\left(E,\ \exists j\in\{0,1\}: h_j^2\ge\|z_j\|^2-b(U)^2\right). \tag{4}
\]
The old marks $V,V+U$ are independent, giving the product for $\Pr(E)$. Outside $E$ there is a hit even at $B$. Within $E$, each indicated inequality certifies a hit by projection at the branch radius. This subtracts each recovered mark pair only once and credits the branch-specific threshold as well as the length removed. Additional lifts can only improve the bound. An exact finite hit test at $b(u)$ can use all lifts of norm at most $\sqrt{b(u)^2+s^2/4}$, since subtracting a nearest multiple of $w$ centers the parallel component without changing the projection.

In particular, for any set of pairs of real numbers $A$, the law of $(\|z_j\|,h_j)$ in (4) assigns it mass $|H|^{-2}\sum_{u,v}\mathbf1_{(\|z_j(u,v)\|,h_j(u,v))\in A}$. The uniform input gives this pushforward jointly for both $j$. A radial Laplace transform specifies the norm distribution of a nearest representative but supplies neither its angle with the selected winner nor the joint hit test.

## A radial recursion using the mean winner projector

There is a lower-dimensional alternative to evaluating the joint law in (4). On the incoming history put
\[
 A=\mathbb E_U[aa^{\mathsf T}/s^2],\qquad \eta=\lambda_{\min}(A),\qquad
 C_B=B/\sqrt{1-\eta}.
\]
This statistic averages the horizontal part of the selected unit winner over the exact uniform mark. It is valid with ties and with arbitrary dependence between the winning height and direction. For the deterministic physical radius $B>0$ (also for a moving radius $b(U)\ge B$), the following whole-profile recursion holds:
\[
 \mathbb E_U p'_U(b(U))\le
 F_{\eta,B}(p):=(1-\eta)p(B)
       +\frac{2(1-\eta)}{B^2}\int_B^{C_B} x\,p(x)\,dx . \tag{6}
\]
It can be intersected with (4) by taking the smaller right side. Formula (6) applies simultaneously as an inequality of expected profiles for all fixed $B$ with $b(U)=B$.

To prove this, fix the old second mark $v$ and its nearest representative $y$. It is independent of the first mark used to choose the winner. The projected zero-layer candidate has mean squared length $y^{\mathsf T}(I-A)y\le(1-\eta)\|y\|^2$. For $x=\|y\|\le B$ it is always a hit. For $x>B$, Markov and the probability bound one give miss probability at most $\min(1,(1-\eta)x^2/B^2)$. Integrate against the distance distribution of $v$. On $(B,\infty)$ the weight starts at $1-\eta$ and has derivative $2(1-\eta)x/B^2$ up to $C_B$, then zero. Layer integration gives (6), including distance atoms at either endpoint.

**Limit of this recursion at the first step.** Since $\operatorname{tr} A=\mathbb E[\|a\|^2/s^2]\le1$, necessarily $0\le\eta\le1/505$. Thus even the most favorable value in (6) assigns unit miss weight to **all** old distances $x\ge B\sqrt{505/504}$. At the lower and upper draw-129 scale endpoints computed below, those cutoffs are $553.67653\ldots$ and $633.81333\ldots$. They fall short of the respective reference radii by $6.65393\ldots$ and $7.78870\ldots$. This holds throughout the corridor as well: $B/b_*<S^{-1/506}$ when $S>1$, and $S^{-1/506}<\sqrt{504/505}$ already at the lower endpoint and thereafter by monotonicity of $S$. Consequently this radial estimate cannot credit any capture at the old reference sphere there, even if the actual mean projector attains the optimal minimum eigenvalue. Shell mass in $(C_B,b_*]$ remains uncontrolled by a bound at $b_*$ alone. Directions of the actual shell representatives could have substantially greater capture than this worst-direction second-moment estimate.

## Equal incoming profiles on opposite sides of the next ceiling

Set $q=3329$, $L=2443/1000$, $s=25L/313$, $C=312L/313$. Thus $s^2+C^2=L^2$. Use the *same* rectangular $M\subset\mathbb R^{505}$ with side lengths $s,C,L,c,\ldots,c$, where there are 502 remaining sides and
\[
 c^{502}=V_{506}(\sqrt2/1.10)^{506}/(CL).
\]
Here $0.19512<s<0.19513<0.23097<c<0.23098$. In case A take the subgroup generated by $Le_3/q$ modulo $M$. In case B use $(s e_1+C e_2)/q$. In either case take $K$ to be the full preimage of this order-$q$ subgroup. Writing $|v|_q$ for the centered absolute residue of its cyclic label, both incoming distance functions are exactly $L|v|_q/q$, even label by label. Coordinatewise nearest representatives prove this for B by the Pythagorean identity. On every branch the unique shortest line is horizontal along $e_1$, since its length $s<1$ beats all nonzero heights and every other horizontal axis.

The outgoing scale satisfies $g'=\sqrt2/1.10$, so its horizontal test radius is exactly one. Write $l=L$ in A and $l=C$ in B. At $j=0$ the residual distance is $l|v|_q/q$. At $j=\pm1$ a hit is possible exactly when $v=\mp u$, and larger heights cannot hit. For
\[
 \delta_l=(q-1-2\lfloor q/l\rfloor)/q
\]
the exact profile value on branch $u$ is
\[
 p'_u(1)=\delta_l-\tfrac2q\mathbf1_{l|u|_q/q>1}.
\]
Indeed the two extra residues are distinct whenever they were missed by the zero layer. In A, $\lfloor q/L\rfloor=1362$, hence $p'_u(1)\ge602/3329>0.18083$. In B, $\lfloor q/C\rfloor=1367$, hence $p'_u(1)\le594/3329<0.17844$. Even their conditional means differ, being $(1-2/q)\delta_l$. For the centered representative at $j=0$ the removed component has absolute value zero in A and $s|v|_q/q$ in B.

Thus an exact update based only on $p(\cdot),g,s$, even with the winner line specified, fails on the abstract marked state space. A universal upper bound from those data must cover case A at this input. This does not decide stability on reachable prefixes with a suitable initial profile. In particular the example is outside the actual scale corridor and does not witness an exit there.

## The raw initialization at draw 129

Use Part 225's envelope for histories capable of crossing below 34.807 on draws 396–406. Put $Q_0=\log q$, $H_0=\log(\sqrt{56.2142}V_{506}^{1/506})$, $u_{406}=\log34.807$, and
\[
 u_i=\min\{u_{i+1}+Q_0/506,(506u_{i+1}+H_0)/505\},\qquad r_i=1.10e^{u_i}.
\]
The entry at draw 129 on such a path satisfies $g_{129}\le e^{u_{129}}<583.27530$. The appended radius is at most $r_{129}<641.60283$, and its corresponding horizontal endpoint lies in $(641.60204,641.60205)$. The endpoint is deterministic. No probabilities below condition on the future crossing. [Part 225, raw sections](wall1_raw_graph_winner_cap.md#why-counting-raw-sections-stops-helping)

**Lemma 2 (raw height-one seed).** Let $m=504+i$. For any fixed $R\ge1$ the unconditional probability of a height-one raw graph point of norm at most $R$ on draw $i$ is at most
\[
 J_i(R)=2q^{-400}V_m(R^2-1+m/4)^{m/2}. \tag{5}
\]
Fix the last coordinate to $+1$, which also handles negative height by negation. For every choice of the other $m$ integer coordinates the graph condition specifies the fresh column exactly after the old columns are fixed. Its probability is $q^{-400}$. To count the possible old coordinates $z$, take the half of the centered unit cube where $\langle z,x-z\rangle\le0$. This lies in the ball of squared radius $R^2-1+m/4$. The cubes have disjoint interiors, and the origin contributes at least a half cube as well. Summing the incidence bounds proves (5). **The bound also holds conditional on every old raw prefix** because the specified last coefficient is one. No independence between witnesses is used.

| Draw | Appended corridor endpoint $r_i$ | $\log_{10} J_i(r_i)$ |
|---:|---:|---:|
| 48 | $2049.12228\ldots$ | $(1.1329,1.1330)$ |
| 49 | $2017.60646\ldots$ | $(-0.2503,-0.2502)$ |
| 129 | $641.60282\ldots$ | $(-129.7880,-129.7879)$ |
| 405 | $38.58168\ldots$ | $(-724.9105,-724.9104)$ |

Draw 49 is the first draw where this majorant falls below the needed coverage of 0.82, and it stays below through draw 405. At the requested starting draw 129 the raw test can certify at most $1.630\cdot10^{-130}$ coverage on *each* prefix with $g_{129}\le e^{u_{129}}$. Here coverage means probability over the fresh raw column, whose projected mark is uniform. This estimates the hit probability for the *sampled column*. Crediting a whole fiber whenever any of its raw columns passes the test gives a different certificate. If the kernel of the raw-column map has size $q^e$, the resulting fraction of distinct marks is at most $\min(1,q^e J_i(r_i))$ by counting raw columns and then their images. At draw 129 even this enlarged bound is less than 0.00104 for $e\le36$. Larger kernels require separate accounting. A projected hit can have a long raw lift. A raw hit implies a projected hit, so the tiny upper bound limits the raw test alone.

More quantitatively, $J_{129}(970)<10^{-16.19}$. Outside this conditional exception, every raw height-one lift of a projected witness at the corridor threshold loses a fraction of squared norm greater than $1-(641.60283/970)^2>0.56248$ to the 128 frozen directions. Thus the need for projection savings begins *before* the proposed initial profile. Parts 222 and 225 supply early all-height winner bounds and determinant moments. Draw 129 in Part 225 is where a sufficient **hypothesis** starts. Establishing the projected height-one profile there requires another argument. [Part 222](wall1_long_winner_handle.md) · [Part 225, direct charge](wall1_raw_graph_winner_cap.md#audit)

## Stability and exception accounting

On draw 129 the deterministic lower comparison for $g$ gives $509.39214\ldots$. At this lower endpoint the current horizontal threshold is $560.33046\ldots$. Using the winner cap $S=\min(q,e^{H_0}g)$, (4) for draw 130 takes $B=\sqrt{(1.10gS^{-1/506})^2-1}=553.12806\ldots$, with second radius $553.12716\ldots$. At the upper corridor endpoint the three thresholds are respectively $641.60204\ldots,633.18548\ldots,633.18469\ldots$. These endpoint calculations locate where the two-radius estimate needs its first inputs even if a seed at the reference radius is granted. Both endpoint volume ratios for the second ball relative to the reference ball are below 0.00146. They are not estimates of distinct-mark coverage.

A pathwise criterion makes the stability issue independent of a choice of concentration inequality. Write $b_*=\sqrt{(1.10g)^2-1}$, let $y(v)$ be the old nearest lift, and set $D_Q(v)=\|Q(y(v),0)\|$. On each branch define the fractions of lost and gained marks by
\[
 L_u=\Pr_V(D(V)\le b_*,\ D_Q(V)>b(u)),\qquad
 G_u=\Pr_V(D(V)>b_*,\ D_Q(V)\le b(u)).
\]
Then $p'_u(b(u))\le p(b_*)+L_u-G_u$. Indeed the right side is precisely the miss probability for the projected zero layer with these chosen representatives. If $b(u)\ge b_*$, then $L_u=0$. For a shorter test radius, the required squared parallel fraction for a representative *on* the reference sphere is $1-(b(u)/b_*)^2$. With the cap comparison radius at the two draw-129 endpoints this fraction lies in $(0.02554,0.02555)$ and $(0.02606,0.02607)$, respectively. The whole radial profile supplies the number of distances in the shell. Example A versus B shows why credit for the removed component requires more information.

In particular, $p(b_*)\le0.18$ propagates on any branch with $L_u-G_u\le0.18-p(b_*)$. Even the simpler condition $p(B)\le0.18$ gives the ceiling on **every** branch by the zero layer. For a probabilistic version, stop before the first exit. A draw-129 seed exception $\varepsilon_{129}$ and conditional probabilities at most $\varepsilon_i$ of violating the sufficient branch criterion on surviving transitions into draws $i=130,\ldots,405$ give total exception at most $\sum_{i=129}^{405}\varepsilon_i$, by partitioning according to the first exit.

Using only a first moment would demand much stronger numerical input. For example a bound of 0.0324 on the conditional mean gives just 0.18 from Markov at threshold 0.18. Equal allocation of $10^{-12}$ to 277 entries by this method would require stopped first moments at most $0.18\cdot10^{-12}/277<6.499\cdot10^{-16}$ per entry. A logarithmic supermartingale would need a separate conditional increment or maximal bound. The first unsupported entry is 129, and the first unsupported propagation is $129\to130$. There is no demonstrated draw at which the *actual* void crosses 0.18. R100's $Z_{\rm rem}<5.339\cdot10^{-11}$ implication retains its exception hypothesis. [R100, exception and budget calculations](wall1_inductive_typicality.md)


## Reproduce the enclosures

Run this verifier from the existing scripts directory. It is embedded to keep the deliverable to one new file.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_drift_recursion.md | python -B -)
```

```python
from fractions import Fraction
from mpmath import iv

iv.dps = 65
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
q, n = 3329, 506
t = I('1.10')
V = [I(1), I(2)]
for j in range(2, 911):
    V.append(2*iv.pi*V[j-2]/j)

L = Fraction(2443, 1000)
C = 312*L/313
s = 25*L/313
assert C*C + s*s == L*L
assert q//L == 1362 and q//C == 1367
assert Fraction(q-1-2*1362-2, q) > Fraction(18083, 100000)
assert Fraction(q-1-2*1367, q) < Fraction(17844, 100000)
def interval(f):
    return I(f.numerator)/f.denominator
c = exp((log(V[n])+n*log(sqrt(2)/t)-log(interval(C*L)))/502)
assert I('.19512') < interval(s) < I('.19513')
assert I('.23097') < c < I('.23098')

Q = log(q)
H = log(I('56.2142'))/2+log(V[n])/n
def smaller(x, y):
    assert x < y or y < x
    return min(x, y)
def log_seed(i, R):
    m = 504+i
    return (log(2)-400*Q+log(V[m])+I(m)/2*log(R**2-1+I(m)/4))/log(10)
def check(x, lo, hi):
    assert I(lo) < x < I(hi), (x, lo, hi)

u = log(I('34.807'))
bounds = {48: ('1.1329','1.1330'), 49: ('-.2503','-.2502'),
          129: ('-129.7880','-129.7879'), 405: ('-724.9105','-724.9104')}
for i in range(405, 0, -1):
    u = smaller(u+Q/n, (n*u+H)/(n-1))
    R = t*exp(u)
    jlog = log_seed(i, R)
    if i in bounds:
        check(jlog, *bounds[i])
    threshold = log(I('.82'))/log(10)
    assert jlog < threshold if i >= 49 else jlog > threshold
    if i == 129:
        upper = exp(u)
        check(R, '641.60282','641.60283')
        assert exp(jlog*log(10)) < I('1.630e-130')
        assert q**36 * exp(jlog*log(10)) < I('.00104')
assert log_seed(129, I(970)) < I('-16.19')
assert 1-(I('641.60283')/970)**2 > I('.56248')

x = (400*Q-log(V[n]))/n
for i in range(1, 129):
    x -= smaller(Q, x+H)/n
check(exp(x), '509.39214','509.39215')
check(upper, '583.27529','583.27530')
assert exp(-smaller(Q,x+H)/n) < sqrt(I(504)/505)
for g, lows in [(exp(x), ('560.33046','553.12806','553.12716')),
                (upper, ('641.60204','633.18548','633.18469'))]:
    R = t*g*exp(-smaller(Q,log(g)+H)/n)
    radii = [sqrt((t*g)**2-1), sqrt(R**2-1), sqrt(R**2-2)]
    for radius, lo in zip(radii, lows):
        assert I(lo) < radius < I(lo)+I('.00001')
    assert (radii[2]/radii[0])**505 < I('.00146')
    trace_cutoff = radii[1]*sqrt(I(505)/504)
    cutoff_lo, gap_lo = (('553.67653','6.65393') if g < I(510)
                         else ('633.81333','7.78870'))
    for value, lo in [(trace_cutoff, cutoff_lo), (radii[0]-trace_cutoff, gap_lo)]:
        assert I(lo) < value < I(lo)+I('.00001')
    angular = 1-(radii[1]/radii[0])**2
    check(angular, *(('.02554','.02555') if g < I(510) else ('.02606','.02607')))
assert I('.18e-12')/277 < I('6.499e-16')
print('Verified the marked example, raw seed cutoffs, and first transition radii.')
```

## Audit

**Verdict. Confirmed on all three checks.** The embedded 65-digit interval verifier passed. An independent calculation using the gamma-function formula for ball volumes reproduced both draw-129 endpoints.

1. **Initialization.** The backward envelope gives $r_{129}=641.6028228267\ldots$. At this fixed radius, $J_{129}(r_{129})=1.6293773294\ldots\times10^{-130}$. This bounds the raw hit probability on every incoming raw prefix because each candidate with last coordinate $+1$ specifies exactly one fresh column. Negation covers height $-1$. Also, $\log_{10}J_{129}(970)=-16.1905433594\ldots$. Outside that conditional exception every raw height-one lift has norm greater than 970. If its projection meets the corridor threshold, orthogonality gives a squared-norm loss fraction greater than $1-(641.60283/970)^2>0.56248$ across the 128 frozen directions. Both probability bounds use the fresh-column law before conditioning on any future crossing.

2. **First transition.** At the lower draw-129 endpoint, the reference radius is $560.3304676119\ldots$ and the cap comparison gives $B=553.1280651119\ldots$. Even at $\eta=1/505$, the miss weight in (6) reaches one at $B\sqrt{505/504}=553.6765313498\ldots$, leaving a shell of width $6.6539362620\ldots$. At the upper endpoint the corresponding width is $7.7887077690\ldots$. These cutoffs describe the gain certified by (6) at the cap comparison radius. An individual branch can still capture marks in the shell.

3. **Abstract examples and reachability.** The identity $s^2+C^2=L^2$ gives identical incoming distances for every label. Both lattices select the same shortest line because $s$ is smaller than every other side and every nonzero height has length at least one. Counting the zero-layer misses and then removing any missed labels among $\{u,-u\}$ gives 602 or 604 misses in A and 592 or 594 in B. Thus every branch in A has void at least $602/3329>0.18083$, and every branch in B has void at most $594/3329<0.17844$. Their common incoming scale is $(\sqrt{2}/1.10)s^{1/506}=1.2815034547\ldots$. Iterating the deterministic lower comparison through draw 405 gives $g_i>32.42764$ on every draw from 129 to 405. The examples therefore establish a limitation of an exact update from the incoming radial data and winner. The reachable-window ceiling of 0.18 remains open.
