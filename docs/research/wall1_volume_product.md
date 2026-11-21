# Integrating the crossing-start exponential at rank 1023

Let $k=n-b$, $q=k+1$. In determinant-one units the table brackets the critical radius for the **sign-divided exponential majorant**. At the left endpoint its integral is strictly below 0.01 and at the right endpoint strictly above. The HKZ column is the best radius certified here for the actual Haar bad event, individually at each width.

| $b$ | Exponential, passes | Exponential, fails | Certified with HKZ | GSA terminal | Linear target |
|---:|---:|---:|---:|---:|---:|
|406|.005272503|.005378647|.005832182|.434|.859|
|506|.012846861|.013155883|.015428901|.960|.959|
|647|.029833670|.030823616|.039230827|2.143|1.084|
|800|.077676505|.082061318|.139940142|4.015|1.206|

Here are rigorous enclosures of $S_q=\log\prod_{l<q}g_l$ for **every full-profile maximizer of the crossing exponential density** on the closed bad polytope. Each column uses the radius indicated in the first table. Exponentiating the endpoints gives the corresponding covolume enclosure. GSA comparisons are rounded.

| $b$ | Mode prefix at exponential pass radius | Mode prefix at HKZ radius | GSA log prefix |
|---:|---:|---:|---:|
|406|[357.34,358.17]|[419.68,420.52]|984.502|
|506|[449.76,450.40]|[544.63,545.27]|881.436|
|647|[405.31,405.80]|[508.54,509.04]|687.317|
|800|[245.56,245.95]|[370.94,371.32]|431.930|

## The crossing integral and its limited penalty

Use the deterministic profile inequalities, Haar normalization $K_n$, $x_i=\log g_i$, and prefix coordinates of [Part 50](wall1_volume_method.md). Denote the closed capped polytope by $D$. Closing the cap leaves its integral unchanged. For $i=\max(0,j-b+1),\ldots,j-1$, put $d=j-i$ and
$$
r_{ij}=\min\{g_i/2,\sqrt{(g_i^2-g_j^2)_+}\},\qquad
p_j=\min\{1,\max_i V_d r_{ij}^d e^{S_i-S_j}\}.
$$
The conditional torus argument in [Part 57](wall1_volume_suppression.md) uses the projected rank $d$ lattice. Its embedded-ball volume gives a lower bound for a hit. The capped expression also defines the majorant on impossible profiles. The sign-divided upper integral for existence is
$$
J_b(\rho)=2^{1-n}K_n\int_D \exp(2\textstyle\sum S_j-\sum p_j)\,dS.
$$
Pointwise its density is between $e^{1-n}$ and 1 times the unweighted density. In particular no optimization of this integral could offset the 34,000 log units of excess mass in the Part 50 witnesses. This obstruction concerns the specified exponential relaxation. The sharper product of $1-p_j$ can vanish.

## Upper integration certificate

Use the integer supersolution $U$ of Part 50, with its dent chosen so $U_q-U_k\ge\log\rho$. Every feasible $S$ satisfies $S\le U$ by leftward propagation of a positive maximum of $S-U$. On the enlarged orthant the normalized unweighted deficits $Z_j=U_j-S_j$ are independent exponentials of rate two. For $2\le j\le n-2$, the adjacent start alone gives $p_j=1$ when
$$
Z_{j-1}+Z_{j+1}-2Z_j\ge a_j,
\quad a_j=\max(0,\tfrac12\log(4/3)-2U_j+U_{j-1}+U_{j+1}).
$$
Indeed $x_{j-1}-x_j\ge\tfrac12\log(4/3)$ there. We use this implication inside $D$ and integrate its simpler majorant throughout the orthant. Conditional on $Z_j=t$, the sum of its neighbors has tail $e^{-2(a_j+2t)}(1+2a_j+4t)$. Averaging gives $h_j=e^{-2a_j}(5/9+2a_j/3)$. Within each residue class modulo three the triples are disjoint. Hölder with exponents $(3,3,3)$ bounds the log integral by
$$
\log K_n-2(n-1)\log2+2\sum U_j+
\tfrac13\sum_{j=2}^{n-2}\log(1-(1-e^{-3})h_j).
$$
This analytic majorant retains a subset of the hits in the all-start maximum. The lower certificate below applies to the entire maximum.

For the HKZ certificate take the smaller of separately valid integral upper bounds. Use the cuts of [Parts 55](wall1_volume_svp_weights.md) and [57](wall1_volume_suppression.md), adjusting the dents to the individual 0.01 criterion. With endpoints $e_0=0,\ldots,e_h=n$ and ranks $d_s=e_s-e_{s-1}$ the log bound is
$$
\log K_n-\sum_s\log K_{d_s}-(h-1)\log2+
\sum_s d_s(U_{e_{s-1}}+U_{e_s})-
\sum_{s<h}\log(d_s+d_{s+1}),
$$
where rank sums start at $s=1$. The conditional coefficient laws used in the two bounds overlap, so multiplying the weights would require a new conditional estimate.

## Lower integration certificate and modal localization

For the lower integral compute an inward prefix witness $X$ with each block row tightened by $d\delta$, $\delta=5000/10^9$. All interior prefixes may independently decrease by up to $\delta$: the residual $dS_{i+1}-(d-1)S_i-S_{i+d}$ increases by at most $d\delta$. The terminal log length increases by at most $\delta$. On this box use $\sum p_j\le n-1$, volume $\delta^{n-1}$, and $2\sum S_j\ge 2\sum X_j-2(n-1)\delta$. The resulting lower bound proves the fail column for $J_b$ alone. Continuity in the radius follows by dominated convergence on any larger capped orthant. Under a strict integral threshold the transition radius is a supremum.

For localization take a separate feasible witness $X$ without tightening and with a slightly deeper dent. At any maximum $S^*$, comparison to $X$ gives
$$
\sum_j(U_j-S^*_j)\le \sum_j(U_j-X_j)+\tfrac12\sum_j p_j(X).
$$
The certificate evaluates the all-start penalty at this feasible profile. At the exponential pass caps its totals lie in $(331.759,331.760)$, $(315.839,315.840)$, $(311.465,311.466)$ and $(300.167,300.168)$ respectively. For $d\ge33$ the block inequality gives $P_{ij}\le V_d e^{H_d}/2^d=(1+d/2)2^{-d/2}$, decreasing in $d$. Thus evaluating dimensions through 32 and enclosing the remaining maximum by the dimension-33 bound suffices for the displayed precision.

A maximum exists because the penalty is continuous and $2\sum S_j$ tends to minus infinity along escaping sequences in the dominated orthant. For each $i\ge q$ select a supersolution row $d$ such that $dU_{i+1}-(d-1)U_i-U_{i+d}\ge H_d$. Feasibility then gives $U_{i+1}-S^*_{i+1}\ge (1-1/d)(U_i-S^*_i)$. Summing the propagated lower bounds from $q$ onwards proves the displayed mode enclosures. Thus even the full crossing exponential mode stays close in this coordinate to the capped LP envelope. The comparison uses an unconditioned GSA profile.

These certificates bracket the exponential transition and localize one coordinate of its optimizer. The exact transition, all maximizing coordinates, and the optimal radius obtainable by integrating the pointwise minimum with HKZ weights remain unresolved. No heuristic distribution of reduced bases or finite-ensemble transfer is used.

## Reproduction

Run the Python block with mpmath. All assertions use integer or outward interval comparisons. The dents and cuts are fixed witnesses selected by numerical search. The array $A$ drops the zeta denominators from $\log K_d$; the omitted sum is between zero and 1.5 by the Part 57 bound.

```python
from fractions import Fraction as Q
from mpmath import iv as I
I.dps=40
n=1023
M=10**9
C=[0,0]
A=[I.mpf(0)]*2
for d in range(2,n+1):
    u=I.mpf(d)/2
    small=[0,0,Q(4,3),2,4,8,Q(64,3),64,256]
    if d<len(small):
        z=Q(small[d])
        H=I.ln(I.mpf(z.numerator)/z.denominator)/2
    else:
        H=u*I.ln(2/I.pi)+I.loggamma(2+u)
    C.append(int((M*H).a)+1)
    assert C[d]-1<=M*H and M*H<C[d]
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u))
def envelope(b,t):
    k=n-b
    T=[0]*(n+1)
    for i in reversed(range(n-1)):
        T[i]=T[i+1]+min((C[d]+T[i+1]-T[i+d]+d-2)//(d-1)
                        for d in range(2,min(b,n-i)+1))-(t if i==k else 0)
    return T,[I.mpf((n-i)*T[0]-n*T[i])/(n*M) for i in range(n+1)]
def product(U):
    # Use the adjacent crossing and three residue classes.
    L=A[n]-2*(n-1)*I.ln(2)+2*sum(U)
    for j in range(2,n-1):
        a=I.ln(I.mpf(4)/3)/2-(2*U[j]-U[j-1]-U[j+1])
        a=I.mpf(max(0,a.b))
        tail=I.exp(-2*a)*(I.mpf(5)/9+2*a/3)
        L+=I.ln(1-tail*(1-I.exp(-3)))/3
    return L
def partition(U,e):
    L=A[n]-(len(e)-2)*I.ln(2)
    for i,j in zip(e,e[1:]):
        d=j-i
        L+=d*(U[i]+U[j])-A[d]+I.mpf('1.5')
    return L-sum(I.ln(z-x) for x,z in zip(e,e[2:]))
cases=[(406,list(range(13,170,13))+[183,197,212,618]),
       (506,[12,518]),
       (647,[377]),
       (800,[224])]
FIX={406:(6318433421,6063603054),506:(5525994118,5154993652),647:(5065952109,4632324864),800:(4532568578,3786997637)}
def lower_box(b,t):
    k=n-b
    h=5000
    T=[0]*(n+1)
    for i in reversed(range(n-1)):
        v=min((C[d]-1-d*h+T[i+1]-T[i+d])//(d-1)
              for d in range(2,min(b,n-i)+1))
        T[i]=T[i+1]+v-(t if i==k else 0)
    X=[I.mpf((n-i)*T[0]-n*T[i])/(n*M) for i in range(n+1)]
    delta=I.mpf(h)/M
    r=I.exp(X[k+1]-X[k]+delta)
    L=A[n]-I.mpf('1.5')-(n-1)*I.ln(2)+2*sum(X)+(n-1)*(I.ln(delta)-2*delta-1)
    return L,r

def score(T,b):
    # Centering cancels in every ratio.
    v=[T[i]-T[i+1] for i in range(n)]
    limit=32
    V=[I.pi**(I.mpf(d)/2)/I.gamma(1+I.mpf(d)/2) for d in range(limit+1)]
    tail=(1+I.mpf(limit+1)/2)*2**(-I.mpf(limit+1)/2)
    total=I.mpf(0)
    for j in range(1,n):
        bounds=[I.mpf(0)]
        for d in range(1,min(j,b-1,limit)+1):
            i=j-d
            diff=v[i]-v[j]
            if diff<=0: continue
            u=1-I.exp(-2*I.mpf(diff)/M)
            frac=I.mpf([min(u.a,I.mpf('.25')),min(u.b,I.mpf('.25'))])
            ratio=I.exp(I.mpf(d*v[i]-T[i]+T[j])/M)
            bounds.append(V[d]*frac**(I.mpf(d)/2)*ratio)
        lo=min(1,max(z.a for z in bounds))
        hi=min(1,max([z.b for z in bounds]+[tail.b if j>limit else 0]))
        total+=I.mpf([lo,hi])
    return total

fails={406:(6268150948,5378647),506:(5477883622,13155883),
       647:(5014280187,30823616),800:(4462269387,82061318)}
labels={406:((5272503,"357.34","358.17"),(5832182,"419.68","420.52")),
        506:((12846861,"449.76","450.40"),(15428901,"544.63","545.27")),
        647:((29833670,"405.31","405.80"),(39230827,"508.54","509.04")),
        800:((77676505,"245.56","245.95"),(139940142,"370.94","371.32"))}
for b,cuts in cases:
    t,limit=fails[b]
    L,r=lower_box(b,t)
    assert r<I.mpf(limit)/M and L>-I.ln(100)
    k=n-b
    for name in ['product','HKZ']:
        def calc(t):
            raw,U=envelope(b,t)
            L=product(U) if name=='product' else partition(U,[0]+cuts+[n])
            return L,U,raw
        hi=FIX[b][name=='HKZ']
        L,U,raw=calc(hi)
        R=I.exp(U[k+1]-U[k])
        scaled=int((R*10**9).a)
        assert R>I.mpf(scaled)/10**9 and L<-I.ln(100)
        # Feasible witness and deficit propagation for the exponential mode.
        T=[0]*(n+1)
        w=I.mpf(1)
        total=I.mpf(1)
        for i in reversed(range(n-1)):
            v=min((C[d]-1+T[i+1]-T[i+d])//(d-1)
                  for d in range(2,min(b,n-i)+1))
            T[i]=T[i+1]+v-(hi+10000 if i==k else 0)
        X=[I.mpf((n-i)*T[0]-n*T[i])/(n*M) for i in range(n+1)]
        assert I.exp(X[k+1]-X[k])<I.mpf(scaled)/10**9
        for i in range(k+1,n-1):
            # Obtain an active supersolution row with maximum propagation.
            d=max(d for d in range(2,min(b,n-i)+1) if
                  (d-1)*raw[i]+raw[i+d]-d*raw[i+1]>=C[d])
            w=w*(d-1)/d
            total+=w
        penalty=score(T,b)
        lower=U[k+1]-(sum(U)-sum(X)+penalty/2)/total
        label,low,upp=labels[b][name=="HKZ"]
        assert label==scaled and lower>I.mpf(low) and U[k+1]<I.mpf(upp)
        print(b,name,hi,scaled,float(L.b),float(lower.a),float(U[k+1].b),float(penalty.a),float(penalty.b),flush=True)

```
