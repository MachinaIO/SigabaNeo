# Crossing SVP tests in the Haar volume bound

At rank 1023 the following are certified lower bounds for the terminal GS length of every fully BKZ-reduced basis of a Haar unimodular lattice, jointly except on a set of probability below $4e^{-61}$. The widths are horizontal and $k=n-b$ is zero-based. The last two columns compare log prefix covolumes at $k+1$. The certified mode is for the marginalized upper density defined below.

| Width | Certified radius | GSA radius | Linear target | Cut mode | GSA prefix |
|---:|---:|---:|---:|---:|---:|
|406|.00583166|.434|.859|420.456|984.502|
|506|.01542725|.960|.959|545.207|881.436|
|647|.03922507|2.143|1.084|508.975|687.317|
|800|.1398963|4.015|1.206|371.261|431.930|

The crossing correction proved in the integral is strictly positive but too small to account for a displayed digit. The numerical gain over the disjoint certificate comes from retaining normalization factors and adjusting the terminal cap. All four linear targets remain out of reach of these bounds. Only the GSA comparison assumes a geometric progression.

## An explicit variance bound at fixed profile

Use strict balls, count sign pairs, and reveal the triangular basis one column at a time. For a single block starting at zero write $R=g_0$, $D_j$ for the lattice of the first $j$ columns, $a_j=\prod_{l<j}g_l$. For $1\le m<R/g_j$ put $s_{jm}=(R^2-m^2g_j^2)^{1/2}$ and $u_{jm}=V_j s_{jm}^j/a_j$. Conditional on the first $j$ columns the horizontal component of column $j$ is uniform modulo $D_j$ because its rectangular GS box tiles by $D_j$ by backward rounding. Multiplication by $m$ preserves Haar measure on that torus. Thus the count $Y_{jm}$ of competitors ending in coefficient $m$ has conditional mean $u_{jm}$ for **every** history. In particular the centered totals for different last indices are orthogonal martingale differences. This gives a variance bound even when their hit indicators are dependent.

Here is a deterministic recipe eliminating the random earlier lattice from the second moment. For any compactly supported radial function $f$ write
$$
 B_j(f)=\sum_{z\in\mathbb Z} f(|z|g_0)
 +2\sum_{h=1}^{j-1}\sum_{t\ge1}\frac{1}{a_h}
 \int_{\mathbb R^h} f\big((|y|^2+t^2g_h^2)^{1/2}\big)\,dy .
$$
It equals the expected sum over $D_j$ by classifying vectors by last index, applying uniform translation modulo the earlier lattice and unfolding. The integral is radial and the sums truncate at the support radius. Take $f_{jm}(v)$ to be the volume of intersection of two $j$-balls of radius $s_{jm}$ at separation $v$. Integrating the square of a periodized ball over one cell groups the two points by their lattice difference. Consequently $v_{jm}=B_j(f_{jm})/a_j-u_{jm}^2$ is the exact unconditional variance of $Y_{jm}$. With $E=\sum_{jm}u_{jm}>0$ define
$$
 T=\sum_j\left(\sum_m\sqrt{v_{jm}}\right)^2.
 \qquad \Pr(\mathrm{pass})\le \frac{T}{E^2+T}.
$$
Indeed the triangle inequality in centered $L^2$ bounds the variance within a column, orthogonality adds the variances across columns, and Cauchy–Schwarz applied to the total count on its positive set gives the claim. For $E=0$ the pass probability is one. This uses the expected count of **all** short pairs, including multiples.

## A product for all crossing starts

For a column $j$ use every $i$ with $\max(0,j-b+1)\le i<j$. Put $d=j-i$, $R_i=g_i$, $s_i=\sqrt{(R_i^2-g_j^2)_+}$. Given survival through column $j-1$, the projected preceding lattice on $[i,j)$ has minimum $R_i$. On its torus the ball of radius $\min(s_i,R_i/2)$ embeds up to a null boundary. Its relative volume
$$
 P_{ij}=V_d\min(s_i,R_i/2)^d/\prod_{i\le l<j}g_l
$$
therefore lower bounds the chance that some lift with last coefficient one is short. The exact hit probability for that start and coefficient is the relative volume of the image of the entire $s_i$-ball on the same torus. It can depend on the preceding lattice. Indices before $j$ enter through that lattice.

There is a second lower bound capturing the union over starts with no lattice enumeration. For independent $X_l$ uniform on $[-1/2,1/2]$, let $Q_j$ be the probability that some eligible $i$ has $\sum_{l=i}^{j-1}g_l^2 X_l^2<s_i^2$. This finite box integral is exact for the projected column itself. It can be computed by accumulating the squared coordinates from right to left and deleting mass below each threshold. The independent summands have distribution function $\min(1,2\sqrt{x}/g_l)$ for $x\ge0$. All starts use the same column. Set $p_j=\min(1,\max(Q_j,\max_i P_{ij}))$. By successive conditioning,
$$
 W_{\rm BKZ}(g)\le\prod_{j=1}^{n-1}(1-p_j)
 \le \exp(-\textstyle\sum_j p_j).
$$
Null surviving histories contribute zero. The single-block version restricts $i$ to its first index. Including every start maximizes this union and maximum among subsets of eligible starts, without any scheduling loss. It gives no uniform comparison of $\sum p_j$ to $E$. The variance result above supplies the alternative bound in terms of $E$.

## Integrating a crossing test

Use the partition and log prefix coordinates of the [disjoint integral](wall1_volume_svp_weights.md). At fixed cuts the internal normalized profiles have independent Haar-HKZ laws under the disjoint weighted integral. This follows by factoring the triangular coefficient cube and normalizing each interval by its covolume. The cross-interval coefficients remain independent uniforms. One may thus multiply the disjoint integrand by the conditional probability of the crossing column tests: given **all internal coefficients**, use the box union defining $Q_j$ with those coordinates fixed and the cross coordinates fresh, then multiply the avoidance probabilities over $j$. This bounds the full weight since those column competitors are necessary tests. Multiplying the preceding unconditional product into the disjoint weight would count some tests twice.

Here is a closed upper integral that keeps one such crossing and needs no high-dimensional quadrature. Let $p,q,n$ be the last three partition endpoints. At the cut $q$ use the column $q$ competitor at start $q-1$. Its squared projected length is $g_q^2+g_{q-1}^2 X_{q-1}^2$. If $g_q/g_{q-1}<\sqrt3/2$, crossing fails throughout the coefficient cell. This start also tests columns through the right endpoint since $q=k+1$.

Write $U$ for the cap supersolution from the script. In the cut orthant restrict temporarily to the top slab $U_i-.01\le S_i\le U_i$ at all interior cuts. There the left mean log length exceeds the right mean by more than .4, verified below. In each of the last two intervals of rank $d$, take the first $d-1$ centered log lengths within $1/(1000d^2)$ of $(l-(d-1)/2)/(100d)$ for $0\le l<d-1$, fixing the last by zero sum. All lengths are strictly increasing (the last error is below $1/(1000d)$), and centered logs have absolute value below .01. All within-interval HKZ tests pass for every coefficient choice by the last nonzero coordinate criterion. The ratio across the cut is at most $\exp(-.4+.02)<\sqrt3/2$. Under the normalized Haar-HKZ law each box has probability at least
$$
 (K_d/2^{d-1})e^{-d^2}(500d^2)^{-(d-1)} .
$$
Indeed the centered prefix Jacobian is one, and twice the sum of its internal prefixes exceeds $-d^2$. This excluded mass applies to the enlarged integral even when those profiles violate the original cap.

For cuts $i$ let $c_i$ be the sum of adjacent interval ranks. The disjoint upper integral is
$$
 B=2^{1-h}K_n\prod_d K_d^{-1}\prod_i e^{c_i U_i}/c_i
$$
where the rank product runs over the $h$ intervals with multiplicity. The normalized orthant has independent exponential deficits $U_i-S_i$ of rates $c_i$. The box product exceeds $e^{-9000000}$ and the slab probability exceeds $e^{-100}$. Hence the crossing-weighted bad-basis integral after sign division is bounded by $B(1-e^{-9000100})$. The script bounds $\log B$ directly to avoid subtractive cancellation. The corresponding dominating marginal density multiplies the disjoint density by $1-e^{-9000000}$ on the slab. Its unique maximum is still $S_i=U_i$ at every cut: leaving the slab costs at least $.01\min_i c_i$ in log density. The script defines all its modal coordinates. The full weighted profile mode remains undetermined; the unweighted LP mode has zero weight by its saturated last two-column constraint. These results neither evaluate the exact crossing integral at the targets nor transfer a Haar bound to the finite lattice ensemble of Parts 47–49.

### Coefficient-dependent loss inside the original bad domain

The slab estimate alone can remove profiles already excluded by the deterministic prefix inequalities. A separate witness shows strict loss even **inside** the original bad polytope. Take $q=k+1$, set $x_l=-6.5+l/10000$ for $l<q$, and set $x_q=x_{q-1}-.02$. On the remaining indices use an increasing progression of step $.0001$, centered at the unique mean restoring zero total. Perturb the first $n-1$ coordinates by at most $10^{-9}$ and correct the last by zero sum. All four cases have $|x_l|<20$ and $g_k$ below the certified radius. Each partition interval is strictly increasing, so the disjoint weight is one. For any start, later logs are at least the starting log minus $.03$. Since $H_d>.03(d-1)$ for all tested widths, every deterministic block inequality holds. The crossing at $q-1$ fails whenever $|X_{q-1}|<.18$, since $.18^2+exp(-.039)<1$. For this profile box the crossing thus removes at least $.36$ of the disjoint coefficient mass.

In the absolute sign-divided integral this removes more than $e^{-30000000}$: use $Fge-20n^2$, the unit log-length to prefix Jacobian, and box volume $(2\cdot10^{-9})^{n-1}$. Thus $B-e^{-30000000}$ is another rigorous upper bound. This witness isolates a coefficient-dependent loss on admissible bad profiles, although its magnitude again has no effect on the displayed radii.

## Interval certificate

Python 3 with mpmath. The backward integer supersolution and $K_d$ normalization are derived in the [volume method](wall1_volume_method.md) and the [disjoint integral](wall1_volume_svp_weights.md). The cut arrays and dents are fixed numerical witnesses. Upper bound each log zeta correction in a denominator product cumulatively by $1.5$ using $\log\zeta(s)\le 3\,2^{-s}$ for $s\ge2$. The cut mode comparison uses the GSA slope from the volume method.

```python
from fractions import Fraction as Q
from mpmath import iv as I
I.dps=45
n=1023
M=10**9
small=[0,0,Q(4,3),2,4,8,Q(64,3),64,256]
C=[0,0]
A=[I.mpf(0),I.mpf(0)]
for d in range(2,n+1):
    u=I.mpf(d)/2
    if d<len(small):
        z=Q(small[d])
        H=I.ln(I.mpf(z.numerator)/z.denominator)/2
    else:
        H=u*I.ln(2/I.pi)+I.loggamma(2+u)
    assert H>I.mpf(".03")*(d-1)
    c=int((M*H).a)
    assert c<=M*H and M*H<c+1
    C.append(c+1)
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u))
a=I.mpf(3329)**(I.mpf(511)/n)
rows=[
 (406,6063829,list(range(13,170,13))+[183,197,212,618],'.00583166'),
 (506,5155210,[12,518],'.01542725'),
 (647,4632557,[377],'.03922507'),
 (800,3787379,[224],'.1398963')]
for b,t,cuts,r in rows:
    k=n-b
    S=[0]*(n+1)
    for i in reversed(range(n-1)):
        v=min((C[d]+S[i+1]-S[i+d]+d-2)//(d-1)
              for d in range(2,min(b,n-i)+1))
        S[i]=S[i+1]+v-(1000*t if i==k else 0)
    U=[I.mpf((n-j)*S[0]-n*S[j])/(n*M) for j in range(n+1)]
    assert I.exp(U[k+1]-U[k])>I.mpf(r)
    L=A[n]
    for i,j in zip([0]+cuts,cuts+[n]):
        d=j-i
        assert 1<=d<=b
        # zeta(s) <= 1+2**(-s)*(1+2/(s-1)) for s>=2.
        # sum log zeta(s) <= 3*sum 2**(-s) <= 1.5.
        L+=d*(U[i]+U[j])-A[d]+I.mpf('1.5')
    e=[0]+cuts+[n]
    D=[y-x for x,y in zip(e,e[1:])]
    Ccut=[y-x for x,y in zip(e,e[2:])]
    L-=len(cuts)*I.ln(2)+sum(I.ln(c) for c in Ccut)
    p,q=e[-3:-1]
    gap=(U[q]-U[p]-I.mpf('.01'))/(q-p)+(U[q]-I.mpf('.01'))/(n-q)
    assert gap>I.mpf('.4')
    logeta=I.mpf(0)
    for d in D[-2:]:
        logeta+=A[d]-(d-1)*I.ln(2)-I.mpf('1.5')-d*d-(d-1)*I.ln(500*d*d)
    assert logeta>-9000000
    assert sum(I.ln(1-I.exp(-I.mpf('.01')*c)) for c in Ccut)>-100
    prefix=[-Q(13,2)+Q(i,10000) for i in range(q)]
    prefix.append(prefix[-1]-Q(1,50))
    m=n-len(prefix)
    tail=[-sum(prefix)/m+Q(2*i-m+1,20000) for i in range(m)]
    assert min(tail)>0 and max(map(abs,prefix+tail))<19
    assert I.exp(I.mpf(prefix[k].numerator)/prefix[k].denominator+I.mpf("1e-9"))<I.mpf(r)
    assert A[n]-I.mpf("1.5")-(n-1)*I.ln(2)-20*n*n+(n-1)*I.ln(I.mpf("2e-9"))+I.ln(I.mpf(".36"))>-30000000
    assert L<-61
    slope=(I.ln(I.pi*b)/b+I.ln(b/(2*I.pi*I.exp(1))))/(b-1)
    pos=[406,506,647,800].index(b)
    G=I.exp(slope*(2*b-n-1)/2)
    assert abs(G-I.mpf([".434",".960","2.143","4.015"][pos]))<I.mpf(".001")
    assert abs(I.sqrt(6*b)/a-I.mpf([".859",".959","1.084","1.206"][pos]))<I.mpf(".001")
    print("prefix",float(U[k+1].mid),float((slope*(k+1)*(n-k-1)/2).mid))
    print(b,float(L.b),float((I.sqrt(6*b)/a).mid),
          float(G.mid))
```
