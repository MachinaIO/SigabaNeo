# Raw witness directions and the retained determinant

**Draw 396 can be removed from the small-scale crossing problem for less than
\(3.855\cdot10^{-19}\) of unconditional probability.** On the original
width-506 chain, the probability that the conditional fourth-moment test (B)
fails on any entry through draw 21 is below \(1.083\cdot10^{-11}\). This
second result certifies the conditional moment itself. R92 gives the stronger
every-next-mark statement on draws 11–19.

The following are alternative sufficient hypotheses. Each is tested under the
original transition law given the incoming history. Write \(s_i\) for the
winner length and \(g_i\) for its incoming GH length.

| Hypothesis | Draws needed for a crossing bound | Upper probability of any crossing on 396–406 | Draws needed for a direct vertical-hit bound | Upper bound on all of \(Z_{\rm rem}\) |
|---|---:|---:|---:|---:|
| (A) Tail probabilities above \(1.05g_i,1.15g_i\) at most \(.60,.15\) | 71–405 | \(2.108\cdot10^{-11}\) | 156–405 | \(6.011\cdot10^{-11}\) |
| (B) \(\mathbb E[(s_i/g_i)^4\mid\mathcal H_{i-1}]\le1.7860\) | 60–405 | \(2.259\cdot10^{-11}\) | 132–405 | \(6.355\cdot10^{-11}\) |
| (C) Tail probability above \(1.10g_i\) at most \(.126\) | 52–380 | \(2.605\cdot10^{-11}\) | 129–380 | \(6.296\cdot10^{-11}\) |

The shorter windows in the last two columns suffice because a small determinant
and a compatible fresh mark must occur together. The eleven-draw crossing
target \(2.72513\cdot10^{-11}\) and the vertical target
\(6.485\cdot10^{-11}\) remain open unconditionally. After the draw-396 charge,
the unresolved crossing entries are **397–406**. The conditional windows above
are sufficient ranges for this proof. No necessity claim about the actual
chain follows from their endpoints. [R92 and audit](wall1_long_winner_handle.md#audit) ·
[Part 193, definition of the vertical residual](wall1_z2_vertical.md) ·
[Part 216, hit charge](wall1_small_g_frequency.md#charge-over-the-eleven-draws)

## A bound uniform over the selected frozen space

On draw \(i\) the appended raw graph has dimension \(N=505+i\) and fixed
covolume \(q^{400}\), with \(q=3329\). The frozen space \(F\) has dimension
\(f=i-1\) and zero newest coordinate. Its orthogonal complement has dimension
\(n=506\) throughout. Put \(V_N=\pi^{N/2}/\Gamma(1+N/2)\) and
\(G_N=(q^{400}/V_N)^{1/N}\).

Use the centered, alias-free projective family of R92 in a raw ball of radius
\(R\), with nonzero newest coordinate and one sign retained per pair. Here a two-dimensional
slicing argument improves its mean to \(\mu\ge(R/G_N)^N/2.09\) throughout
\(506\le N\le573\), \(1600\le R\le3600\).

**Integer-ball lower bound.** Put \(c=1/\sqrt2\),
\(A^2=R^2-(N-2)/4\). The last two integer coordinates provide at least
\(\pi(\sqrt{y_+}-c)_+^2\) completions at remaining squared radius \(y\),
by the covering radius of the unit square. This function is increasing and
convex in \(y\), including across \(y=c^2\). At \(x\in\mathbb R^{N-2}\),
independently round each coordinate to the two adjacent integers preserving
its mean. The mean squared norm of the result is at most
\(\|x\|^2+(N-2)/4\), and integration gives unit mass to each integer output.
Jensen therefore bounds the full ball count below by the integral of the
completion bound at \(y=A^2-\|x\|^2\). Using
\((\sqrt{y_+}-c)_+^2\ge y_+-2c\sqrt{y_+}\) and integrating disk and interval
slices gives
\[
 \#(\mathbb Z^N\cap B_R)\ge V_N A^N-\pi c V_{N-1} A^{N-1}.
\]
To remove noncentered vectors, enclose their unit cubes in the ball of radius
\(R+\sqrt N/2\) and the union of the coordinate caps \(|x_j|\ge1664\).
The verifier subtracts this cap-volume bound, R92's half-cube bound for the
zero newest coordinate, and its four-endpoint bound for nontrivial projective
aliases. Identifying opposite signs leaves more than \(V_NR^N/2.09\) points.
The centered lift restriction ensures unique representatives even for
Euclidean radius above \(q\). Incidence indicators \(I_z\) have equal mean
\(q^{-400}\) and pairwise nonpositive covariances by R92.

For \(u_z=z/\|z\|\), form the positive semidefinite matrix
\[
 C=\sum_z I_z u_z u_z^\top,\qquad Z=\operatorname{tr}C.
\]
Then
\[
 \operatorname{Var} Z\le\mu,\qquad
 \mathbb E\|C-\mathbb EC\|_{\mathrm F}^2\le\mu .
 \tag{1}
\]
The off-diagonal covariance terms in the expansion of the second moment have
coefficient \((u_z^\top u_w)^2\ge0\). Each diagonal coefficient is one.
Before removing the last-coordinate-zero slice, the deterministic dyads are
invariant as a set under signed permutations. The slice has fewer members than
the surviving family by the same counting estimates. Hence the average
newest-coordinate squared direction after removal is at most \(2/N\).
The old coordinate directions have equal diagonal entries, with zero
off-diagonals by sign symmetry. This argument uses the symmetry of the
candidate set. The graph distinguishes its input and output coordinates.

Write \(P_F\) for projection onto \(F\) and put
\(\eta=f(1-2/N)/(N-1)\). For every such \(F\),
\(\operatorname{tr}(P_F\mathbb EC)\ge\eta\mu\).
Fix \(0<b<\eta\). If \(s_i>R\sqrt{1-b}\), then every incident witness has
\(\|P_Fu_z\|^2<b\), since it has a nonzero projection off \(F\) and its
projected length bounds the winner. This implies
\[
 (\eta-b)\mu\le
 \sqrt f\,\|C-\mathbb EC\|_{\mathrm F}+b|Z-\mu|.
\]
The implication also holds for \(Z=0\). Squaring, taking expectations using
the triangle inequality in \(L^2\), and applying (1) gives
\[
 \Pr\{s_i>R\sqrt{1-b}\}\le
 \frac{(\sqrt f+b)^2}{(\eta-b)^2\mu}.
 \tag{2}
\]
The norm on the right of the preceding pathwise inequality controls all
projections simultaneously. Consequently no distributional assumption on
\(F\) given the graph, or union over frozen spaces, enters (2).

Set \(b=\eta-4/N\) when positive, \(D_b=(\sqrt f+b)^2/(\eta-b)^2\), and take
\[
 T_i=2.09^{1/N}G_N\min\{1,\sqrt{1-b}\,D_b^{1/N}\},
 \tag{3}
\]
omitting the second choice for \(b\le0\). The directional choice improves
the radius from draw 31 through the tested endpoint 68. Throughout that prefix,
\(\Pr(s_i>r)\le (T_i/r)^N\) for \(T_i\le r\le q\). For the directional
choice evaluate the raw count at \(R=r/\sqrt{1-b}\). The verifier checks
both ends of its validity interval. With \(s_i\le q\), integration gives,
for \(0<p<N\),
\[
 \mathbb E s_i^p\le\min\{q^p,T_i^p/(1-p/N)\}.                 \tag{4}
\]

## Determinant moments and the two probability budgets

Write \(x_i=\log g_i\), \(a=505/506\), \(Q=\log q\),
\(h=\sqrt{56.2142}\,V_n^{1/n}\), \(H=\log h\),
\(X=\log 34.807\), and \(Y_i=\log(s_i/g_i)\). Thus
\(x_1=\log G_n\), \(s_i\le\min(q,hg_i)\), and
\(x_{i+1}=x_i-\log(s_i)/n=ax_i-Y_i/n\).

Use (4) through draw \(B\ge3\), deterministic bounds through \(m\ge B\), a
conditional hypothesis on \(m<i\le e\), and deterministic bounds thereafter.
For a terminal index \(j\ge m\) let \(u_i=\lambda a^{j-i}\), \(v=u_B\) and
\(p=(B-2)v\). The following bound \(L_j(\lambda)\) on
\(\log\mathbb E\exp(-\lambda n x_{j+1})\) applies to both calculations.
\[
 -nvx_1+2vQ+
 \sum_{i=3}^{B}\min\{vQ,\ v\log T_i-\log(1-p/(505+i))/(B-2)\}
 +\sum_{i=B+1}^{j}\log K_i(u_i).                              \tag{5}
\]
Indeed the first two lengths are at most \(q\). Hölder with exponent \(B-2\)
handles each remaining prefix factor. Conditioning backward one step at a
time handles the suffix. On unrestricted draws use \(K_i(u)=h^u\). The three
conditional majorants are
\[
 K_A(u)=.40(1.05)^u+.45(1.15)^u+.15h^u,\qquad
 K_C(u)=.874(1.10)^u+.126h^u,
\]
and \(K_B(u)=1.7860^{u/4}\) for \(u\le4\),
\(K_B(u)=1.7860h^{u-4}\) for \(u>4\). The latter branch follows by bounding
the excess power pointwise.

For a crossing, stop \(Y_i\) after the first tested entry below \(X\), using
zero for subsequent increments. From below \(X>0\) this extension ends below
\(X\). Every \(K_i\ge1\), so (5) applies to the stopped comparison as well.
Markov gives \(\exp(\lambda n X+L_{405}(\lambda))\). The crossing rows use
\((B,m,e,\lambda)=(68,70,405,5.24),(59,59,405,4.28),(51,51,380,6.02)\).
Increasing \(m\) by one with the other parameters fixed puts each majorant
above the budget. If the last draws are harder to control, a different
allocation gives crossing bounds \(2.190,1.931,2.400\) times \(10^{-11}\)
under A on **36–394**, B on **36–400**, or C on **36–377**, respectively.
These use \(B=m=35\) and \(\lambda=5.3,4.3,6\).

For the direct residual estimate use the actual, unstopped determinant.
With \(R_*^2=\sqrt{2}\,1352/\sqrt{3}\), Part 216 bounds the conditional
fresh-mark hit charge on every entry by \(.608(R_*/g_i)^n\). Summation over
the eleven entries now gives
\[
 Z_{\rm rem}\le .608\,R_*^n\sum_{j=395}^{405}\exp L_j(1).       \tag{6}
\]
This integrates the inverse determinant at each entry and includes both
sides of \(g_i=34.807\). Only prefix-measurable gates may enter a conditional
transition. Later gates can be imposed on the joint event and dropped in an
upper bound. The direct rows use \(B=68\), with \((m,e)=(155,405),(131,405),
(128,380)\). Each next \(m\) fails (6) at the same settings. On draw 396
alone, using only deterministic bounds after 68 gives an unconditional
vertical charge below \(4.072\cdot10^{-12}\).
[Part 216, twelve heights and the grid bound](wall1_small_g_frequency.md#a-tighter-projected-ball-bound)

An exceptional set can be charged explicitly. If a hypothesis is certified
at all tested entries up to the first predictable failure and the probability
of any such failure is at most \(\epsilon\), kill the moment calculation at
that failure and add \(\epsilon\) to the final bound. For example the direct
B row leaves more than \(1.30\cdot10^{-12}\) for exits. The table already
integrates the early raw graphs, including exceptional early histories.
There is no early exception to add unless an argument actually discards them.

## Unconditional entry and count certificates

Fix an event \(E\) with \(\Pr(E)\ge p>0\), and put \(\theta=1+\log(1/p)\).
Integration of the marginal tail conditional on this arbitrary event gives
\[
 \mathbb E[\log s_i\mid E]\le\log T_i+
 \int_0^\infty\min(1,e^{-Ny}/p)\,dy=\log T_i+\theta/N.
\]
The period and Hermite bounds also give an upper bound
\(\min(Q,H+\mathbb E[x_i\mid E])\) for the same conditional mean.
Starting at \(z_1=x_1\), subtract
\(\min(Q,H+z_i,\log T_i+\theta/N)/n\) from \(z_i\) on the tested prefix, omitting the last term outside it. Monotonicity of the resulting lower update
gives \(\mathbb E[x_j\mid E]\ge z_j\) at each entry. In particular for a
**fixed** \(j\), taking \(E=\{x_j<z_j\}\) proves
\(\Pr(x_j<z_j)<e^{1-\theta}\). This avoids a separate exception for each
of the earlier lengths. Simultaneously controlling several terminal entries
would require a further argument.

* With \(\theta=43.4\) the raw term improves the floor on draws 9–50.
  After ordinary updates through 395, \(34.80726<e^{z_{396}}<34.80727\).
  The total crossing charge on draw 396 is below
  \(e^{-42.4}<3.855\cdot10^{-19}\).
* With \(\theta=34\) through 54, the exception \(x_{55}<z_{55}\) has
  probability below \(e^{-33}<4.659\cdot10^{-15}\). On the complement a
  crossing requires at least **154, 87, or 36** strict exceedances on
  **55–405** at \(t=1.00,1.10,1.15\), respectively. Apply Part 216's exchange
  lemma to the remaining 351 steps, starting at \(z_{55}\). Its worst ordering
  places the exceptional \(h\)-steps last. The verifier checks both adjacent
  counts. For an earlier crossing, append ordinary comparison steps, which
  preserve a value below \(X\). A \(1.15g_i\) cap on all but 35 of these draws
  would thus suffice on the good event. Alternatively, the respective
  predictable ceilings \(.2739,.1195,.0276\) on the 351 draws each suffice by
  binomial domination **including the exception charge**. Existence of the
  requisite later caps remains open.
  [Part 216, ordering lemma](wall1_small_g_frequency.md#how-many-long-winners-does-a-crossing-require)

To certify (B) itself, take \(E_i\) to be the incoming histories on which
it fails. Suppose \(\Pr(E_i)\ge p_i\), and use
\(\theta_i=1+\log(1/p_i)\) through draw \(i-1\) to get the floor
\(z_i(\theta_i)\). Since \(E_i\) is measurable before the fresh draw, failure
and Jensen imply
\[
 \mathbb E[s_i^4\mid E_i]>1.7860\,\mathbb E[g_i^4\mid E_i]
 \ge 1.7860\,e^{4z_i(\theta_i)}.
\]
Integration of \(\min(1,(T_i/r)^N/p_i)\) against \(4r^3\,dr\), with the
period bound as an alternative, gives the upper bound
\[
 \mathbb E[s_i^4\mid E_i]\le
 \min\{q^4,\,T_i^4 p_i^{-4/N}/(1-4/N)\}.                      \tag{7}
\]
The verifier chooses explicit \(p_i\) for draws 11–21 that make these
inequalities incompatible, and sums them to less than
\(1.083\cdot10^{-11}\). Through draw 10 the period suffices deterministically.
The estimate allows a nonzero conditional chance of a longer next winner.
R92's nine-draw horizontal certificate controls every mark on its good event.

## Why counting raw sections stops helping

The raw scale falls too slowly relative to the retained scale on a crossing
path. The following first-moment calculation includes *every* raw line in the
ball, including lines that the frozen space would kill. Back-propagate the
latest possible crossing from \(u_{406}=X\) by
\[
 u_i=\min\{u_{i+1}+Q/n,(u_{i+1}+H/n)/a\}.
\]
At or before a tested future crossing, \(x_i\le u_i\), by the deterministic
updates and monotonicity (an earlier crossing has a smaller backward upper
endpoint). For \(r=t e^{u_i}<q\), the probability of any nonzero raw vector
of length at most \(r\) is at most
\[
 W_i(t)=q^{-400}V_N(r^2+N/4)^{N/2}.                            \tag{8}
\]
Every possible graph vector this short has nonzero input residue or is zero.
Each fixed vector with nonzero input belongs with probability \(q^{-400}\).
For the count of unoriented nonzero vectors, put the inward half of a unit
cube about each oriented vector inside the ball of squared radius
\(r^2+N/4\), then identify the signs. These cubes have disjoint interiors.

| \(t\) | First draw from which (8) stays below 1 through 405 | First draw from which (8) stays below \(2.72513\cdot10^{-11}/405\) through 405 |
|---:|---:|---:|
| 1.00 | 34 | 44 |
| 1.10 | 51 | 60 |
| 1.15 | 58 | 67 |

At draw 405 the raw GH length exceeds 259.09, the retained crossing corridor has
\(e^{u_i}<35.0743\), and \(W_i(1.15)<10^{-709}\).
The last column implies a simultaneous absence result within the budget by a
union bound at the deterministic corridor radii. A small first moment here
pays for *existence* of the raw witnesses that a cap would need. Projected
witnesses may still occur frequently. The cutoffs 49–67 in R92 were where its
prefix/suffix **moment majorants** exhausted the budget. The table explains
the geometric limitation without assigning a universal phase transition to
those particular indices.

**All ranks.** Use covolumes in intrinsic Euclidean measure. Let \(S\) be
any rank-\(k\) raw sublattice with injective projection \(P=P_{F^\perp}\) on
its span, and let \(c_k\) be any proved upper bound for \(\gamma_k\). Write
\(J_F(S)\) for the product of the singular values of this restricted
projection. Then \(\det PS=J_F(S)\det S\). A certificate
\(\det PS\le(r/\sqrt{c_k})^k\) implies a nonzero projected vector of length
at most \(r\) by Hermite. Using \(\det S\le(r/\sqrt{c_k})^k\) alone already
implies a **raw** vector of that length, for every \(k\) simultaneously. No
union over ranks or choice of sharper valid Hermite constants can avoid (8)
for that raw-volume test. A basis of a saturated projected section can also
be lifted and the same argument applied to those lifts.
[Li and Nguyen, Rankin invariants and intrinsic sublattice volume](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/CB62F4DF842A1A687A498FD5A4B38580/S1461157014000333a.pdf/approximating_the_densest_sublattice_from_rankins_inequality.pdf)

A raw Rankin lower tail **does** give a useful necessary compression. At final
raw dimension 910, (8) with radius 250 gives
\(\Pr(\lambda_1\le250)<4.01\cdot10^{-14}\). Zero extension covers every
previous raw prefix on the same gate. There every rank-\(k\) raw \(S\) has
\(\det S>(250/\sqrt{c_k})^k\), again by Hermite. Consequently any draw-405
section certifying \(s_i\le1.15g_i\) by the projected determinant test, on
the crossing corridor, must satisfy
\[
                   J_F(S)<(1.15\cdot35.0743/250)^k<0.16135^k.
\]
The respective upper bounds on the volume contraction are 0.02604 in rank 2,
\(4.594\cdot10^{-7}\) in rank 8, and \(9.694\cdot10^{-20}\) in rank 24.
This applies to sections in the incoming lattice as well, using their raw
lifts before the append. A union bound for rare *small* raw determinants
can enforce the lower bound in this argument. To certify a cap one still
needs an upper bound on the probability that **all** projected determinants
exceed their thresholds. First moments for rare small determinants give the
other inequality. The raw gate leaves the selected angles free. For example,
for a fixed coordinate line \(S\), rational frozen lines orthogonal to it or
spanned by \(Le_1+e_2\) with \(S=\mathbb Ze_1\) can give Jacobians 1 or
\(1/\sqrt{1+L^2}\) at the same raw covolume. This example concerns the
information supplied by the determinant alone. Adding frozen vectors to a
lift can make its contraction arbitrarily strong without changing its
projection. Thus a probability estimate on the angles also needs to specify
the lifts it counts. [R92, saturated section
identity](wall1_long_winner_handle.md#deterministic-sublattices-and-the-sign-of-feedback)

Finally, grant the scalar recursion the optimistic deterministic cap
\(s_i\le G_N\sqrt{506/N}\) on **every** draw, in addition to the period and
Hermite caps. At equality in the smallest cap the draw-397 scale is already
below 34.807. The draw-406 scale lies in \((32.47290,32.47291)\). The extra
cap last binds on draw 76. This one scalar path has 404, 379 and 368
exceedances at the three thresholds, respectively, passing all the necessary
count tests for a crossing. Even multiplying that optimistic cap by **0.8**
on every draw leaves a terminal scale in \((33.29996,33.29997)\).
These are deterministic obstruction calculations for this scalar proof.
Reachability of either path by selected lattices is unknown.

## Interval verification

The verifier uses outward-rounded interval arithmetic at 65 decimal digits.
To keep the repository change to the requested single file, run the embedded
script from the existing scripts directory.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_raw_graph_winner_cap.md | python -B -)
```

```python
from mpmath import iv

iv.dps = 65
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
n, d, q = 506, 505, 3329
a, Q, X = I(d)/n, log(q), log(I('34.807'))
V = [I(1), I(2)]
for j in range(2, 911):
    V.append(2*iv.pi*V[j-2]/j)
G = [(400*Q-log(V[j]))/j if j else None for j in range(911)]  # logs
H = log(I('56.2142'))/2+log(V[n])/n
M, budget = I('1.7860'), I('2.72513e-11')
def small(x,y):
    assert x < y or y < x
    return min(x,y)

L = [None]  # log of the certified marginal length scale
for i in range(1,69):
    N, f = 505+i, i-1
    lo, hi = I(1600), I(3600)
    cut = (2*N*V[N-1]/V[N]*(1+sqrt(N)/(2*lo))**N
           *(1-(1664/(hi+sqrt(N)/2))**2)**(I(N-1)/2))
    center = ((1-(N-2)/(4*lo**2))**(I(N)/2)
              -iv.pi/sqrt(2)*V[N-1]/(V[N]*lo)-cut)
    sl = 2*V[N-1]/(V[N]*lo)*(1+(N-1)/(4*lo**2))**(I(N-1)/2)
    for R in (lo,hi):
        T = 2*sqrt(iv.pi)*R/sqrt(N)
        for ell in (sqrt(5),2*sqrt(q/iv.pi)):
            al = q*(exp(I(1)/2)*(1+T/ell)*(1+T*ell/q)/R)**N/V[N]
            assert center-sl-al > 2/I('2.09') and sl < I('.5')
    un = G[N]+log(I('2.09'))/N
    eta = f*(1-I(2)/N)/(N-1)
    b = eta-I(4)/N
    L.append(un)
    if b > 0:
        D = (sqrt(f)+b)**2/(eta-b)**2
        improved = un+log(D)/N+log(1-b)/2
        L[i] = small(un,improved)
        if improved < un:
            assert exp(L[i])/sqrt(1-b)>lo and q/sqrt(1-b)<hi
    assert exp(un)>lo and exp(L[i])>lo
    if i>=31:
        assert L[i]<un

def cumul(kind,u):
    if kind=='A':
        return log(I('.4')*I('1.05')**u+I('.45')*I('1.15')**u+I('.15')*exp(u*H))
    if kind=='C':
        return log(I('.874')*I('1.10')**u+I('.126')*exp(u*H))
    assert kind=='B'
    if u < 4:
        return u*log(M)/4
    assert u > 4
    return log(M)+(u-4)*H

def logmoment(kind,b,m,e,j,lam):
    v = lam*a**(j-b)
    p = (b-2)*v
    val = -n*v*G[n]+2*v*Q
    for i in range(3,b+1):
        N = 505+i
        assert 0<p<N
        val += small(v*Q,v*L[i]-log(1-p/N)/(b-2))
    for i in range(b+1,j+1):
        u = lam*a**(j-i)
        val += cumul(kind,u) if m<i<=e else u*H
    return val

for kind,b,m,e,l,up in [('A',68,70,405,'5.24','2.108e-11'),
                         ('B',59,59,405,'4.28','2.259e-11'),
                         ('C',51,51,380,'6.02','2.605e-11')]:
    lam = I(l)
    prob = exp(lam*n*X+logmoment(kind,b,m,e,405,lam))
    assert prob < I(up) < budget
    assert exp(lam*n*X+logmoment(kind,b,m+1,e,405,lam))>budget

Rhit = sqrt(sqrt(2)*1352/sqrt(3))
def hit(kind,b,m,e):
    return I('.608')*Rhit**n*sum(exp(logmoment(kind,b,m,e,j,I(1))) for j in range(395,406))
for kind,m,e,up in [('A',155,405,'6.011e-11'),('B',131,405,'6.355e-11'),
                     ('C',128,380,'6.296e-11')]:
    assert hit(kind,68,m,e)<I(up)<I('6.485e-11')<hit(kind,68,m+1,e)
for kind,e,up in [('A',394,'2.190e-11'),('B',400,'1.931e-11'),('C',377,'2.400e-11')]:
    lam = {'A':I('5.3'),'B':I('4.3'),'C':I(6)}[kind]
    assert exp(lam*n*X+logmoment(kind,35,35,e,405,lam))<I(up)<budget

def envelope(theta,stop):
    x, active = G[n], []
    for i in range(1,stop+1):
        step = small(Q,H+x)
        if i<=68:
            raw = L[i]+theta/(505+i)
            if raw<step:
                active.append(i)
                step=raw
            else:
                assert raw>step
        x -= step/n
    return x,active

x,active = envelope(I('43.4'),395)
assert active==list(range(9,51)) and exp(I('-42.4'))<I('3.855e-19')
assert I('34.80726')<exp(x)<I('34.80727')
bounds = list(map(I,['3.20e-22','3.43e-21','3.72e-20','4.07e-19','4.49e-18',
                     '5.01e-17','5.64e-16','6.41e-15','7.34e-14','8.49e-13','9.90e-12']))
for i,p in enumerate(bounds,11):
    N = 505+i
    x,_ = envelope(1-log(p),i-1)
    upper = small(4*Q,4*L[i]-4*log(p)/N-log(1-I(4)/N))
    assert upper<log(M)+4*x
assert sum(bounds)<I('1.083e-11')
assert Q<G[n]-9*Q/n+log(M)/4

from math import comb
x54,_ = envelope(I(34),54)
err = exp(I(-33))
assert err<I('4.659e-15')
for t,k,p in [('1',154,'.2739'),('1.10',87,'.1195'),('1.15',36,'.0276')]:
    for bad in (k-1,k):
        y = x54
        for step in range(351):
            cap = log(I(t)) if step<351-bad else H
            y -= small(Q,cap+y)/n
        assert (y>X if bad==k-1 else y<X)
    prob = I(p)
    bt = sum(comb(351,j)*prob**j*(1-prob)**(351-j) for j in range(k,352))
    assert err+bt<budget
assert I('.608')*Rhit**n*exp(logmoment('A',68,395,395,395,I(1)))<I('4.072e-12')

def raw_logmean(N,R):
    return log(V[N])+I(N)/2*log(R**2+I(N)/4)-400*Q

assert exp(G[910])>I('259.09')
for k,bound in [(2,'.02604'),(8,'4.594e-7'),(24,'9.694e-20')]:
    assert I('.16135')**k<I(bound)
assert exp(raw_logmean(910,I(250)))<I('4.01e-14')
x = X
starts = [[0,0] for _ in range(3)]
for i in range(405,0,-1):
    x = small(x+Q/n,(x+H/n)/a)
    N = 505+i
    for k,t in enumerate(map(I,['1','1.10','1.15'])):
        r = t*exp(x)
        for c,threshold in enumerate([I(0),log(budget/405)]):
            if starts[k][c]==0:
                if r<q and raw_logmean(N,r)<threshold:
                    continue
                assert r>q or raw_logmean(N,r)>threshold
                starts[k][c]=i+1
    if i==405:
        assert exp(x)<I('35.0743') and I('1.15')*exp(x)/250<I('.16135')
        assert raw_logmean(N,I('1.15')*exp(x)) < -709*log(10)
assert starts==[[34,44],[51,60],[58,67]]

for factor in [I(1),I('.8')]:
    x, last, counts = G[n], 0, [0,0,0]
    for i in range(1,406):
        N = 505+i
        raw = log(factor)+G[N]+log(I(n)/N)/2
        step = small(small(Q,H+x),raw)
        if raw < Q and raw < H+x:
            last = i
        for k,t in enumerate(map(I,['1','1.10','1.15'])):
            if step>x+log(t):
                counts[k]+=1
            else:
                assert step<x+log(t)
        x -= step/n
        if i==396 and factor==1:
            assert exp(x)<exp(X)
    if factor==1:
        assert last==76 and counts==[404,379,368] and I('32.47290')<exp(x)<I('32.47291')
    else:
        assert last==131 and I('33.29996')<exp(x)<I('33.29997')
print('Verified direction counts, crossing and vertical-hit windows, both exceptions, and raw obstructions.')
```

## Audit

**Confirmed for the original width-506 chain.** The embedded interval verifier and the verifiers for Parts 216 and 222 passed on rerun. An independent 70-digit calculation using \(\log\Gamma(1+N/2)\) for the ball volumes reproduced the values below. All six table entries retain their stated hypothesis windows. The unconditional crossing estimate covers draw 396 alone.

**Raw directions.** The two-dimensional completion bound is convex in the remaining squared radius. The integral of \(\sqrt{(A^2-\|x\|^2)_+}\) over the first \(N-2\) coordinates is \(V_{N-1}A^{N-1}/2\), giving the coefficient \(\pi c\) in the lower count. One can remove all centered nontrivial projective aliases before deleting the zero-newest-coordinate slice because multiplication by a nonzero field scalar preserves that slice. The dyads before slice deletion therefore have signed-permutation symmetry. The deleted slice is smaller than the survivors, so their mean newest-coordinate energy is at most \(2/N\). Distinct surviving projective points have independent or incompatible graph incidences. This gives both variance bounds in (1), and the Frobenius norm in (2) controls the graph-dependent choice of \(F\) pointwise.

**Draw 396 and the fourth moment.** Conditioning the marginal tail on any event of mass at least \(p\) costs at most a factor \(1/p\). The resulting lower update for the conditional mean of \(x_i\) is the maximum of increasing affine maps. At \(p=e^{-42.4}\) it gives \(e^{z_{396}}=34.80726594847\ldots\). If the event \(g_{396}<34.807\) had that mass, its conditional mean log scale would be strictly below \(\log 34.807\), contradicting the floor. For (B), the failure event at draw \(i\) is measurable before that draw, so multiplying the strict conditional failure inequality by \(g_i^4\) and averaging over the event is valid. On draws 11–21 the smallest gap between the log lower bound from failure and the log upper bound from (7) exceeds \(4.24\cdot10^{-6}\). The eleven \(p_i\) sum to \(1.082942903795\cdot10^{-11}\), and the period cap covers draws 1–10.

| Hypothesis | Crossing window | Crossing majorant \((10^{-11})\), approx. | Direct-hit window | \(Z_{\rm rem}\) majorant \((10^{-11})\), approx. |
|---|---:|---:|---:|---:|
| A | 71–405 | 2.10789608 | 156–405 | 6.01086423 |
| B | 60–405 | 2.25880072 | 132–405 | 6.35482313 |
| C | 52–380 | 2.60476486 | 129–380 | 6.29548346 |

**Direct vertical charge and exceptions.** A residual hit at draw \(i\) supplies a point at one of twelve positive heights. Each point determines one compatible fresh mark given the incoming history. Summing the point probabilities gives the Part 216 bound \(.608(R_*/g_i)^n\) even when points share a mark. Future gates can be dropped from the hit event before taking this conditional expectation. Averaging over the actual incoming histories uses the unstopped inverse moment \(\mathbb E[g_i^{-n}]\), with terminal index \(j=i-1\) in (5). Summing \(j=395,\ldots,405\) covers the entire residual. The direct column therefore requires no additional high-\(g\) charge or draw-396 crossing charge. Both columns average over the full early prefix, including the histories where (B) fails through draw 21. If a later window is proved only up to a predictable exit, restrict each calculation to surviving paths and add the probability of any exit once.

**Winner count and corridor.** Starting from \(e^{z_{55}}=1439.51352628\ldots\), an independent recursion minimized over both choices of the last cap at each step and exception count. With 35 and 36 exceedances of \(1.15g_i\), the draw-406 comparison floors are respectively \(34.81548229\ldots\) and \(34.80436365\ldots\). Padding an earlier crossing with ordinary comparison steps preserves a scale below 34.807. Thus every crossing on draws 396–406 requires at least 36 exceedances on draws 55–405 outside the single draw-55 exception of mass below \(e^{-33}\).

Draw 405 has raw dimension 910, raw GH \(259.09105218\ldots\), and backward corridor endpoint \(e^{u_{405}}=35.07426262\ldots\). The value \(\log_{10} W_{405}(1.15)=-709.20438345\ldots\) bounds the log probability of a raw witness at the deterministic radius \(1.15e^{u_{405}}\) under the original law. It therefore also bounds the joint event of a raw witness at radius \(1.15g_{405}\) and a crossing at or after that entry. Off the single raw-minimum exception at radius 250, Hermite gives \(\det S>(250/\sqrt{c_k})^k\) simultaneously for every eligible lift. Dividing the projected certificate by this floor gives \(J_F(S)<(0.16135)^k\) on the corridor.
