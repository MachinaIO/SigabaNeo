# Integrating disjoint SVP tests in the Haar basis volume

For a determinant-one Haar lattice of rank 1023, the following terminal lower bounds hold simultaneously for **every** fully BKZ-reduced basis at the four horizontal widths, with failure probability below $4e^{-60}$. The terminal is $g_k$, indexed from zero with $k=n-b$. The integral retains all suffix SVP tests inside each member of a partition. No Poisson approximation enters the certificate.

|Horizontal $b$|Previous lower bound|Weighted lower bound|GSA terminal|Linear target|Quadratic target as requested|
|---:|---:|---:|---:|---:|---:|
|406|.00525|.00583|.434|.859|10.588|
|506|.01281|.01542|.960|.959|13.198|
|647|.02975|.03922|2.143|1.084|16.879|
|800|.07728|.13985|4.015|1.206|20.872|

The radii are one-sided certificates. The last three columns are rounded comparisons. Here $a=3329^{511/1023}$, and the targets displayed are $2\sqrt{1.5b}/a$ and $(1+1.5(b-1))/a$. When the Part 47 embedded width includes the height coordinate it equals $b+1$, so its mean squared plant length benchmark is $(1+1.5b)/a$, higher by $1.5/a$. The squared-length benchmark is formed in physical units **before** dividing by the lattice length unit. Neither convention gives a certified target crossing. The probability statement concerns Haar input only. [Unweighted comparison](wall1_volume_method.md) · [Part 47](wall1_decoupled.md)

## Conditional short-vector counts

Work in upper triangular column coordinates with diagonal $g_l$ and entries $g_l\mu_{jl}$ in column $j$, row $l<j$. Projection at $i$ deletes rows before $i$. Thus every test on $[i,h)$ depends only on $\mu_{jl}$ with $i\le l<j<h$, and disjoint intervals are independent at fixed profile under the size-reduced Haar chart.

In one interval renumber from zero. Let $R=g_0$. Count sign pairs by taking the last nonzero coefficient $m>0$, at position $j$. The exact expected count strictly inside the ball is
$$
 E=\sum_{j=1}^{d-1}\sum_{1\le m<R/g_j}
 \frac{V_j(R^2-m^2g_j^2)^{j/2}}{\prod_{l<j}g_l}.
$$
For any fixed later coefficients the phase in row $l$ contains $m\mu_{jl}$, uniform modulo one even for nonprimitive $m$. Sum over the integer coefficient in that row and integrate the phase, starting at row zero and proceeding upward in index. Each step replaces the sum and phase integral by a real integral of intensity $1/g_l$. Tonelli applies and the surviving slice has the displayed volume.

There is also a computable conditional second-moment bound. Fix $j$, keep only $m=1$, and condition on the preceding triangular lattice $D$ of rank $j$. The horizontal displacement of column $j$ modulo $D$ is Haar because the rectangular GS box tiles by $D$ (successive rounding from the last row). Put $B=B_j(\sqrt{R^2-g_j^2})$ for $g_j<R$. For the count $Y$ of this coset in $B$, torus unfolding gives
$$
 u=\mathbb E[Y\mid D]=|B|/\det D,\qquad
 v(D)=\mathbb E[Y^2\mid D]=\sum_{z\in D}|B\cap(B+z)|/\det D .
$$
Expand the square, group by the lattice difference and integrate one fundamental cell. Only $|z|<2\operatorname{rad}(B)$ contributes. Hence the pass probability is at most $1-u^2/v(D)$ conditionally and at most its average unconditionally. Summing the first moments across $m,j$ does not give an exponential void bound. Even a variance of order $E$ in a second-moment argument gives only order $1/E$. Overlapping cosets and multiples share phases. The fixed-profile exponential suppression suggested in the question remains unproved.

## Weighted integral bound

Let $S_j=\sum_{i<j}\log g_i$ and $K_n$ be the intensity constant in the unweighted note, with $K_1=1$. Write $W$ for the joint probability of all BKZ tests at a profile. The oriented bad basis count has mean $K_n\int_{\rm bad}e^{2\sum S_j}W\,dS$. Divide by $2^{n-1}$ for signs to bound existence.

Partition the index set into consecutive intervals of ranks $d\le b$. Every suffix of each interval is a truncation of a tested block. Its first vector remains shortest on restriction. Hence $W$ is at most the product of the probabilities of full HKZ in the intervals. This uses independence **between** intervals and retains the joint event inside each interval.

For cuts $p<q$ bounding one interval set $d=q-p$. Subtract the linear interpolant between $S_p,S_q$ to obtain internal centered prefix coordinates $T_1,\ldots,T_{d-1}$. This is translation by fixed offsets once the boundary values are fixed, and normalizes the interval to determinant one. Its contribution satisfies the exact identity
$$
 \int_{\mathbb R^{d-1}} e^{2\sum T_j} W_{\rm HKZ}(T)\,dT=2^{d-1}/K_d.
$$
Indeed unfolding counts oriented size-reduced HKZ bases. Almost surely every successive shortest pair is unique and each choice of signs determines the size-reduced lifts uniquely by triangular rounding. The exceptional ties and rounding boundaries are null by the primitive disintegrations, or by countably many equalities in the basis chart. Orientation fixes the last sign. This is also the normalization of the recursive HKZ density in [Part 46](wall1_haar_prefix_law.md).

Suppose the bad profile polytope implies $S_j\le U_j$ at the interior cuts. Enlarge to these half-lines and unrestricted internal coordinates. Summing the linear interpolants leaves exponent $\sum_j c_j S_j$ over interior cuts, where $c_j=d_{\rm left}+d_{\rm right}$. The weighted first moment **after division by signs** is therefore bounded by
$$
 2^{1-h}\frac{K_n}{\prod_{s=1}^h K_{d_s}}
 \prod_{j\text{ interior cut}}\frac{e^{c_j U_j}}{c_j},
$$
with $h$ intervals. This evaluates the enlarged integral exactly. The flag interpretation is consistent with the nested primitive sublattice approach in [Laarhoven](https://arxiv.org/abs/2610.15265). Crossing-block tests and internal prefix caps are the losses here.

## Maximizers and comparison with GSA

The marginalized weighted density on the enlarged cut domain has unique mode $S_j=U_j$ at every cut, since all $c_j>0$. The script specifies the entire cut profile for each row. At cut $k+1$ the modal log covolumes are respectively 420.366, 545.154, 508.929, and 371.215. The corresponding unconditioned GSA values are 984.502, 881.436, 687.317, and 431.930. This comparison reflects the imposed bad terminal cap as well as the enlargement of the domain.

For the **full** weighted density the old LP maximizer can be ruled out analytically. Its final pair saturates $g_{n-1}/g_{n-2}=\sqrt3/2$ even with any of the four terminal dents. The two-column test then requires $|\mu_{n-1,n-2}|=1/2$, giving weight zero. Positive density is possible in the bad domain, for example on strictly increasing profiles with a sufficiently small $g_k$ (take the first $k+1$ lengths small and choose the remaining lengths to restore determinant one). Every competing vector with a later last index is then longer. Locating the full weighted mode or evaluating the unrelaxed integral at the targets remains open here. The cut mode cannot supply the integrated-out coordinates. Large unweighted mass gives no lower bound on weighted mass.

## Interval certificate

The backward recurrence is the prefix supersolution of the [profile volume bound](wall1_volume_method.md). At each row it uses an outward-rounded tight-block upper envelope, except at the dent where the terminal cap dominates. More explicitly, at an ordinary row choose a minimizing width in the recurrence. Its supersolution prefix is at least the constraint's weighted average of its adjacent and end prefixes plus $H_d/d$. At the dent $U_{k+1}-U_k>\log r$ suffices instead. Any positive maximum of $S-U$ must propagate left through a tight or dominating row until an endpoint, a contradiction. The backward array in the script stores suffix sums in integer units $1/M$. The numerical partitions and dents were selected by exploratory optimization and are fixed witnesses in the proof. The script drops the favorable sign and denominator factors and bounds the log zeta corrections outward. Python 3 with mpmath suffices.

~~~python
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
    c=int((M*H).a)
    assert c<=M*H and M*H<c+1
    C.append(c+1)
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u))
a=I.mpf(3329)**(I.mpf(511)/n)
rows=[
 (406,6064200,list(range(13,170,13))+[183,197,212,618],'.00583'),
 (506,5155420,[12,518],'.01542'),
 (647,4632750,[377],'.03922'),
 (800,3787700,[224],'.13985')]
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
    assert L<-60
    slope=(I.ln(I.pi*b)/b+I.ln(b/(2*I.pi*I.exp(1))))/(b-1)
    print("prefix",float(U[k+1].mid),float((slope*(k+1)*(n-k-1)/2).mid))
    print(b,float(L.b),float((I.sqrt(6*b)/a).mid),
          float(((1+I.mpf('1.5')*(b-1))/a).mid))
~~~
