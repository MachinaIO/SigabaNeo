# Rankin minima of the horizontal graph lattice

**The full-shape Rankin quotient clears the linear benchmark at null width 1020 with probability at least 0.99. Width 1019 is the only remaining candidate for a smaller 99% certificate using the exact Rankin numerator and the Part 6 denominator.** Even an oracle for every Rankin minimum cannot certify the quadratic benchmark at 99% by this quotient, at any width. Per-index propagation already clears the linear benchmark at 1000. At that width the Rankin quotient itself is less than one with probability greater than 0.989, while every fully reduced basis has projected minimum above 79.04 with probability at least 0.99. The loss comes from dividing an unrestricted minimum by a worst-case prefix volume.

Here and below the lattice is the graph congruence $L=\{(x,y):x+Ay=0\pmod q\}$, with $r$ retained rows, 512 columns, $N=r+512$, $D=q^r$, and $q=3329$. Width $b$ counts **horizontal** dimensions, $k=N-b$. We test $\sqrt{6b}$ and $1+1.5(b-1)$ as requested. Part 47 calls the width **including height** $\beta$. For precisely this horizontal quotient its $\beta=b+1$ and its mean squared norm is $1+1.5b$. The quadratic impossibility below also covers this larger mean. Neither mean is an upper quantile. The GSA crossing at 506 and the rigorous propagation crossing at 1000 both use the fixed linear benchmark. [Parts 6, 39, 47, 48 and frontier](../PROOF_GAP.md) · [Propagation and GSA comparison](wall1_null_terminal.md) · [Projection and lifting](wall1_decoupled.md)

## The quotient and its dual

Write $W$ for the primitive prefix lattice and $P$ for projection perpendicular to its span. Extending a basis of $W$ by a lift $z$ of a shortest vector of $T=PL$ gives determinant $\det W\,\|Pz\|$. Therefore $\lambda_1(T)\ge\mu_{k+1}(L)/\det W\ge\mu_{k+1}(L)/X_k$. For any prefix index $i$, $g_i=\det W_{i+1}/\det W_i\ge\mu_{i+1}/X_i$, even if the window at $i$ does not reach the end. We use the overlapping exact BKZ envelope $X_i$ at the actual width. No near-optimality of a reduced prefix for the Rankin problem is assumed. [Part 6 envelope](wall1_prefix.md)

Saturation can only decrease a sublattice determinant. For primitive $S\subset L$, extend its basis to one of $L$. The reciprocal vectors corresponding to the extension form a basis of $L^*\cap S^\perp$, dual to the projected extension. Thus its determinant is $\det S/D$, and the annihilator correspondence is a bijection by double annihilation. In particular $\mu_j(L)=D\mu_{N-j}(L^*)$. Inside $T^*=L^*\cap W^\perp$ the same argument gives $\lambda_1(T)=\det T\,\mu_{b-1}(T^*)$. Replacing the latter minimum by the ambient dual minimum and $\det T$ by $D/X_k$ produces exactly the original quotient. Dual estimates are useful when complementary rank is small. [Hermite–Rankin invariants](https://www.numdam.org/item/10.5802/jtnb.712.pdf)

## A finite first moment with the modular defect included

For an integer basis matrix with columns $(E;F)$, membership has probability $q^{-r s}$ if $s=\operatorname{rank}_q F=\operatorname{rank}_q(E;F)$, and zero otherwise. This is the inhomogeneous row count for $AF=-E$, by the kernel-count argument of Q1. Summing these weights over unique column HNFs of rank $j$ and covolume at most $Y$ bounds $\Pr(\mu_j\le Y)$. Finiteness follows from the bounded integral Plücker coordinates of the saturated span and its bounded index. Every consistent tuple has total modular rank at most 512. Its index in the integral saturation is divisible by $q^{\max(0,j-512)}$ by Smith form. In particular $\mu_j\ge q^{\max(0,j-512)}$. Replacing modular rank by rational rank can discard every witness. [Q1, kernelCount and meanValue](../../SigabaNeo/Lib/Lattices/QAry.lean)

There is also an exact positive count with one term per rational plane. Let $S$ be its primitive integral lattice, $s$ the secret rank of $S\bmod q$, and $f=j-s$. The reduction of $S$ has dimension $j$. On the kernel of the secret projection the check $(I,A)$ has fixed image of dimension $f$. Values on $s$ complementary basis elements are independent uniform vectors after adding their fixed sample components. Modulo that fixed image they form a uniform $(r-f)\times s$ matrix $G$. Therefore
$$
\det(S\cap L)=\det S\,q^{f+\mathrm{rank}(G)}.
$$
Sum the probabilities that this expression is at most $Y$ over primitive integral planes of determinant at most $Y$. This gives the exact mean number of primitive-in-$L$ witnesses, with no choice of basis and no independence assumption between planes. Ordinary finite-field matrix enumeration gives each probability. The general sum is not evaluated here. We evaluate a two-dimensional upper bound and prove an obstruction to improving the resulting widths by evaluating even the exact sum.

### A numerical two-plane theorem

On the full shape, with probability greater than $1-0.000838$, simultaneously $\lambda_1(L)>442$ and $\mu_2(L)>193000$. All volumes here are unsquared. For a ball of radius $B$ at any real center use
$$
 C(B)=e^{tB^2}\left[\sqrt{\pi/t}\,(1+2z/(1-z))\right]^N,
 \qquad t=N/(2B^2),\quad z=e^{-\pi^2/t}.
$$
This bounds its integer population by Gaussian majorization and Poisson summation in each coordinate, bounding all shifted Fourier phases by one. For $B<q$, the line failure probability is at most $C(B)/(2D)$ by the graph check and sign symmetry.

Set $Y=193000$. A two-plane witness has a Gauss-reduced basis $v,w$, with $a=\|v\|\le\sqrt{2Y/\sqrt3}<474$, coefficient $|\langle w,v\rangle/a^2|\le1/2$, and transverse length at most $Y/a$. After discarding the line failure at 442, bin $a$ by integer lower endpoint $h=442,\ldots,473$. Round the coefficient to the nearest multiple of $1/20$ in the closed coefficient interval. There are 21 centers. The resulting count of ordered bases in the bin is at most
$$
 21 C(h+1) C\left(\sqrt{(Y/h)^2+((h+1)/40)^2}\right).
$$
For total modular rank two every basis has membership probability at most $D^{-2}$. A consistent basis of smaller modular rank has index divisible by $q$ in its integral saturation. The saturation has area at most $Y/q<58$ and a Gauss basis of lengths at most 9 and 59, since its shortest length is at least one. The check restricted to this primitive plane has rank at most one **if its intersection with $L$ has index at most $Y/\det S<q^2$**, as it must for a witness. Thus its kernel contains one of the $q+1$ field lines of this plane. Each fixed nonzero residue costs at most $1/D$, including when the secret residue vanishes. The defect contribution is at most $C(9)C(59)(q+1)/D$. The script sums the three positive bounds. This calculation uses ordinary integer bases only for upper bounds, so multiple Gauss bases cause no undercount.

### From lines and planes to all ranks

Write $C_j=(j/2)\log\bar\gamma_j$ for the proven Hermite upper constants in Part 6, with $C_0=C_1=0$. An ambient minimum $>R$ gives $\log\mu_j\ge j\log R-C_j$. Apply the same estimate to $qL^*$, which after swapping coordinates is the graph for the transposed matrix up to sign, with determinant $q^{512}$. The script caps its counting radius below $q$. Both line radii use the Part 48 Gaussian bound at 99%.

For any rank-$j$ lattice of covolume $V$, take its first two HKZ vectors. The first length is at most $\exp(C_j/j)V^{1/j}$ and the second projected length at most $\exp(C_{j-1}/(j-1))(V/g_0)^{1/(j-1)}$. Their product is at least $\mu_2(L)$ when this lattice lies in $L$. Thus for $j>2$ a further lower bound on $\log\mu_j$ is
$$
 [j\log Y-(j-2)C_j/(j-1)-j C_{j-1}/(j-1)]/2 .
$$
For $j=2$ use $\log Y$ directly. Maximize these lower bounds, the dual bound and the Smith bound before sampling. For any fixed row, choosing the strongest deterministic certificate in advance gives 99% without adding the error probabilities. A simultaneous event using several different probability inputs requires their union bound. The linear crossings at all four passing full-shape widths hold jointly on the single plane event. Its radius of 442 suffices at the empty prefix.

| Retained rows | Null rank | First passing BKZ width, linear | Exact slide, linear | BKZ, quadratic |
|---:|---:|---:|---:|---:|
| 511 | 1023 | 1020 | 1023 | none |
| 188 | 700 | none | none | none |
| 149 | 661 | none | none | none |
| 134 | 646 | none | none | none |

Selected full-shape lower certificates (rounded down) are $4.186\cdot10^{-490}$ at 506, $2.612\cdot10^{-9}$ at 1000, 18.979 at 1018, 42.234 at 1019, **88.984 at 1020**, 170.259 at 1021, 301.893 at 1022 and 443.0664 at 1023. Using just the line-based primal and dual Hermite estimates and the Smith bound first passes at 1021. At punctured width one below full the corresponding lower certificates exceed 33.500, 22.903 and 19.555 in decreasing rank order. The Part 39 dimension-647 and dimension-662 results concern a planted comparison after prescribed deletion, not this null-minimum threshold. [Part 39](wall1_projected_reference.md)

For slide use aligned equal blocks only. If $N=sb$, $w_i$ is the log determinant of block $i$, and $h_i$ its head, the Part 48 shifted dual inequality gives $e^{w_i}\le h_i h_{i+1}^{b-1}(\rho\bar\gamma_b)^{b/2}$. The primal bounds $h_i\le\sqrt{\bar\gamma_b}\,e^{w_i/b}$ then give $w_i-w_{i+1}\le b^2\log(\sqrt\rho\,\bar\gamma_b)/(b-1)$. Summing from the last block yields
$$
 \log X_{N-b}^{\rm slide}=(1-1/s)\log D+
 (s-1)b^2\log(\sqrt\rho\,\bar\gamma_b)/(2(b-1)).
$$
Use the same numerator and $\rho=1$ for the table. The aligned slide bound clears the quadratic benchmark at no divisor on any of these shapes. Increasing $\rho$ weakens the bound. The full-width single block has empty prefix. This argument gives no overlapping-window envelope for internal slide indices.

## Why a better global count cannot close the gap

The following are **upper bounds on $\mu_{k+1}/X_k$**, not on the actual projected minimum. They limit *every* numerator-only improvement with the stated denominator. First, a single ambient HKZ witness gives $\log\mu_j\le H_j$, where $H_0=0$ and $H_j=((h-1)H_{j-1}+\log D+C_h)/h$, $h=N-j+1$. This follows by applying Hermite in the remaining projection and multiplying by the prefix determinant. At width 506 this alone gives a quotient below $2^{-466}$.

A sharper witness for small ranks uses independent short vectors. For $2B<q$, let $Z$ count points in the radius-$B$ ball with nonzero secret residue that satisfy the graph check. Its expectation is the candidate count divided by $D$. Distinct independent secret residues have zero covariance. For a fixed candidate, a dependent secret residue with positive joint probability forces the entire residue vector to be the same scalar multiple. There are at most $q$ such candidates, including itself, by injectivity on the ball. Hence $\operatorname{Var} Z\le q\mathbb EZ$ and $\Pr(Z<\mathbb EZ/2)\le4q/\mathbb EZ$. On the event $\lambda_1>R$, at most $(1+2B/R)^d$ such points fit in a $d$-plane by disjoint radius-$R/2$ balls. Exceeding this number proves $\mu_{d+1}\le B^{d+1}$ by Hadamard.

Two elementary lower counts suffice. Write $V_h$ for unit ball volume. Unit cubes give at least $V_N(B-\sqrt N/2)^N$ integer points, and at most $V_r(B+\sqrt r/2)^r$ have zero secret. For smaller $B$ improve the first term to $V_N a^N/2$, with $a^2=B^2-N/4-B-\sqrt N$. To see this, independently round each coordinate of a real $x$ of norm at most $a$ to its two adjacent integers with mean $x_i$. The expected squared norm is at most $a^2+N/4$. Its variance is at most $\sum_i(2|x_i|+1)^2/4\le(a+\sqrt N/2)^2$, by the range of each rounded square. The one-sided variance inequality gives probability at least $1/2$ of landing in the ball of radius $B$. Integrate over $x$. Each integer point receives total weight one over all space, by the product of the linear interpolation kernels.

At $B=485$ the script certifies $\mu_j\le485^j$ for all $j\le32$ with failure below $0.01001$ on each shape. In particular at full-shape width 1000 the quotient is below $2^{-1.171}<1$ on this event. Smaller radii $452,61,44,38$ certify dimensions through $9,20,31,25$ respectively. Even allowing failure $0.8$ for the smaller-radius population, the combined witness event has probability greater than $0.189$ on each shape. This is enough to refute any proposed 99% lower certificate. The interval scan proves:

* For all full-shape widths $2\le b\le1018$, the quotient is below $\sqrt{6b}$ on the witness event. At 1018 its base-two logarithm is below 6.276. At 1019 the bounds leave room on both sides of the threshold. Thus the optimal 99% crossing of the quotient lies in **[1019, 1020]**, a gap of one width.
* At every full-shape width the quotient is below $1+1.5(b-1)$ on that event. On each punctured shape every width fails both comparisons on its witness event. These impossibility scans use the Part 6 BKZ denominator. They do not assume an HKZ prefix actually realizes it.

Per-index propagation retains the constraints linking $g_0$ and $g_k$ **in the same basis**. The numerator-minimizing sublattice and the denominator-maximizing prefix in the Rankin argument can come from different flags. At 1000 the probability bounds show that this loss occurs even if the numerator is known exactly. The one unresolved width cannot improve Part 48's first certified width, let alone the GSA crossing. A smaller upper bound on the volume of prefixes selected on typical inputs would change this conclusion's hypothesis.

The plane estimate can also strengthen propagation directly. Since $g_0g_1\ge\mu_2$ and Part 48 gives $g_i\le g_k\exp(P_{k-i})$ for $i\le k$, the plane event gives
$$
 g_k>\sqrt{193000}\,\exp[-(P_k+P_{k-1})/2]\qquad(k\ge1).
$$
This raises the certified radius at width 1000 to **80.2109**. At 999 it gives 76.6217 to four decimal places, below $\sqrt{5994}$. This use of the numerator keeps the two GS factors in the propagation inequality coupled to the same terminal length.

## Prefix GS lengths

Use the joint plane event ($R=442$, $Y=193000$) for every $i<k$ and apply the same primal Rankin bounds to $g_i$. On the full shape this certifies $\min_{i<k}g_i>41.256$ at 1018, $>87.424$ at 1019, and $>168.245$ at 1020. At 1000 the same minimum bound is only about $10^{-8}$. For comparison, at that width Part 48 propagation from the ambient line gives $g_i\ge R e^{-P_i}$ separately throughout the prefix. Adjacent-volume ratios lose much more than propagation over this longer prefix.

For independent CBD(3), insert the individual lower bounds into Part 47's conditional Babai-box union bound $\sum_{i<k}2\exp(-g_i^2/12)$. The first widths giving conditional bounds below $0.01$ and $2^{-64}$ are respectively **1017 and 1018** for this plane-event certificate. At 1016 its sum exceeds 0.0219. At 1017 it is below $10^{-12}$ and at 1018 below $5.1\cdot10^{-62}$. Monotonicity follows because increasing the width decreases each $X_i$ and removes prefix indices. These statements bound the probability of a box violation conditional on the null design, before observing the projected SVP outcome. Combining with a quotient-success event requires accounting for that event as well. The null-design failure bound of 0.000838 is separate from the CBD tails. No recovery or running-time claim follows from the linear comparison.

## Executable certificate

Python 3, NumPy and mpmath. Natural logs internally. The Part 6 recurrence is evaluated in first differences: if $s_h=-u_{N-h}$ then $s_0=s_1=0$ and the new increment is the minimum of $(C_l+s_{h-1}-s_{h-l})/(l-1)$. The difference in the numerator sums earlier increments, so rounding every increment consistently downward or upward encloses the exact result by induction. Bound $\log X_k=k\log D/N+(1-k/N)s_N-s_{N-k}$ with opposite endpoints at the subtraction. For a width interval the envelope at the largest width gives a common lower bound on the denominator. Subdivision in the upper-bound scan sharpens that bound where needed.

```python
from mpmath import iv as I
import numpy as np
from functools import lru_cache
I.dps=45
M=10**8
ln=I.ln
def low(x): return int(x.a)-1
def high(x): return int(x.b)+1
q=3329
C=[I.mpf(0)]*2
for h in range(2,1024):
    if h<=8:
        a,b=[(4,3),(2,1),(4,1),(8,1),(64,3),(64,1),(256,1)][h-2]
        C.append(ln(I.mpf(a)/b)/2)
    else: C.append(h*ln(2/I.pi)/2+I.loggamma(2+I.mpf(h)/2))
cl=np.array([low(v*M) for v in C],dtype='int64')
cu=np.array([high(v*M) for v in C],dtype='int64')
@lru_cache(None)
def sums(n,b,up):
    c=cu if up else cl
    s=np.zeros(n+1,dtype='int64')
    for h in range(2,n+1):
        l=np.arange(2,min(h,b)+1)
        a=c[l]+s[h-1]-s[h-l]
        s[h]=s[h-1]+min(-((-a)//(l-1)) if up else a//(l-1))
    assert max(abs(s))<10**13
    return s
def run(r,rows):
    n=r+512; D=r*ln(q)
    # Dual scaled by q is a graph with r free variables.
    def rad(D):
        t=I.pi*I.exp(1-2*D/n); z=I.exp(-I.pi**2/t)
        return I.sqrt((D+ln(I.mpf('.02'))-n*ln(I.sqrt(I.pi/t)*(1+2*z/(1-z))))/t)
    R=rad(D)
    Rd=min(rad(512*ln(q)),I.mpf(q-1))/q
    assert 0<R and R<q
    def vol(j,radius): return j*ln(radius)-C[j]
    def X(k,b):
        if k==0:return I.mpf(0)
        sl=sums(n,b,False); su=sums(n,b,True)
        # u_k=-s[n-k], u_0=-s[n]
        return k*D/n+I.mpf([int(sl[n])*(n-k)-int(su[n-k])*n,
                              int(su[n])*(n-k)-int(sl[n-k])*n])/(n*M)
    def planes():
        # Uniform bound on the number of integer points in any shifted ball.
        def count(B):
            t=I.mpf(n)/(2*B**2); z=I.exp(-I.pi**2/t)
            return I.exp(t*B**2)*(I.sqrt(I.pi/t)*(1+2*z/(1-z)))**n
        Y=193000
        e=count(I.mpf(442))/(2*I.exp(D))
        for a in range(442,474):
            e+=21*count(I.mpf(a+1))*count(I.sqrt((I.mpf(Y)/a)**2+
                                                (I.mpf(a+1)/40)**2))/I.exp(2*D)
        # Saturated integral two-plane, index divisible by q.
        # Gauss basis lengths <=9 and <=59 (first >=1).
        e+=count(I.mpf(9))*count(I.mpf(59))*(q+1)/I.exp(D)
        assert e<I.mpf('.000838')
        print('plane failure',float(e.b))
        return ln(Y)
    pair=planes() if r==511 else None
    def pairvol(j):
        # HKZ determinant bound for the first two vectors.
        v=pair
        if j==2:return v
        return (j*v-(j-2)*C[j]/(j-1)-j*C[j-1]/(j-1))/2
    def numerator(j):
        a=max(vol(j,R),D+vol(n-j,Rd),max(0,j-512)*ln(q))
        if pair is not None and j>=2: a=max(a,pairvol(j))
        return a
    def lb(k,b): return numerator(k+1)-X(k,b)
    winners=[]
    lines=[]
    for b in range(2,n+1):
        k=n-b
        if r==511:
            line=max(vol(k+1,R),D+vol(b-1,Rd),max(0,k+1-512)*ln(q))
            if line-X(k,n)>ln(6*b)/2 and line-X(k,b)>ln(6*b)/2:lines.append(b)
        if lb(k,n)>ln(6*b)/2: # smaller widths have larger cutoff
            v=lb(k,b)-ln(6*b)/2
            if v>0: winners.append(b)
            else: assert v<0
        else: assert lb(k,n)<ln(6*b)/2
    assert winners==([1020,1021,1022,1023] if r==511 else [])
    if r==511:assert lines==[1021,1022,1023]
    print(r,winners)
    slide=[]
    slide_quad=[]
    for b in range(2,n+1):
        if n%b:continue
        blocks=n//b
        xs=(blocks-1)*D/blocks+(blocks-1)*b*C[b]/(b-1)
        base=numerator(n-b+1)-xs
        quad=ln(1+I.mpf('1.5')*(b-1))
        if base>quad:slide_quad.append(b)
        else:assert base<quad
        v=base-ln(6*b)/2
        if v>0:slide.append(b)
        else:assert v<0
    print('slide',slide)
    assert not slide_quad
    assert slide==([1023] if r==511 else [])
    for b in rows:
        k=n-b; v=lb(k,b)
        print(b,I.nstr(v/ln(2),11),I.nstr(I.exp(v),11))

    if r==511:
        for b in (1000,1018,1019,1020):
            k=n-b
            # All prefix indices use just the single two-plane event,
            # which also certified lambda_1 > 442 outside its failure set.
            bounds=[max(vol(i+1,I.mpf(442)),pairvol(i+1)) if i else ln(I.mpf(442))
                    for i in range(k)]
            v=min(x-X(i,b) for i,x in enumerate(bounds))
            print('prefix',b,I.nstr(I.exp(v),10))
        for b in (999,1000):
            k=n-b
            su=sums(n,b,True)
            # Sum P[k]+P[k-1] is a sum of individually rounded increments.
            mixed=I.exp((pair-I.mpf(int(su[k+1]-su[k-1]))/M)/2)
            print('mixed',b,I.nstr(mixed,12))
        def babai(b):
            total=I.mpf(0)
            for i in range(n-b):
                j=i+1
                logv=vol(j,I.mpf(442))
                if j>=2:logv=max(logv,pairvol(j))
                g=I.exp(logv-X(i,b))
                total+=2*I.exp(-g*g/12)
                if total>1:break
            return total
        for target in (I.mpf('.01'),I.mpf(2)**-64):
            a,b=2,n
            while b-a>1:
                w=(a+b)//2
                if babai(w)<target:b=w
                else:
                    assert babai(w)>target
                    a=w
            print('Babai',b,I.nstr(babai(a),10),I.nstr(babai(b),10))
    # Deterministic numerator upper via a witness HKZ basis.
    H=[I.mpf(0)]
    for h in range(n,0,-1):
        H.append(((h-1)*H[-1]+D+C[h])/h)
    # Witness population, using B=485 for the first count.
    B=485
    logE=I.log(I.pi)*n/2-I.loggamma(1+I.mpf(n)/2)+n*ln(B-I.sqrt(n)/2)-D
    # Remove y=0 candidates using cubes in sample dimension.
    bad=I.pi**(I.mpf(r)/2)*(B+I.sqrt(r)/2)**r/I.gamma(1+I.mpf(r)/2)
    E=I.exp(logE)-bad/I.exp(D)
    print('E bits',float((ln(E)/ln(2)).mid))
    assert E/2>(1+2*B/R)**32 and 4*q/E<I.mpf('.00001')
    bsmall={511:452,188:61,149:44,134:38}[r]
    margin=bsmall+I.sqrt(n)
    a=I.sqrt(bsmall**2-I.mpf(n)/4-margin)
    # Stochastic rounding, all nonzero candidates with nonzero free part.
    V=I.pi**(I.mpf(n)/2)/I.gamma(1+I.mpf(n)/2)
    bad=I.pi**(I.mpf(r)/2)*(bsmall+I.sqrt(r)/2)**r/I.gamma(1+I.mpf(r)/2)
    E=(V*a**n/2-bad)/I.exp(D)
    jj=0
    while jj<n and E/2>(1+2*bsmall/R)**jj and 4*q/E<I.mpf('.8'):
        jj+=1
    print('small',bsmall,jj,I.nstr(E,8))
    def ceiling(k):
        return min([H[k+1]]+([(k+1)*ln(B)] if k<32 else [])+([(k+1)*ln(bsmall)] if k<jj else []))
    for b in rows:
        k=n-b
        print('upper',b,I.nstr((ceiling(k)-X(k,b))/ln(2),11))
    def scan(a,b,quad):
        missed=[]
        for w in range(a,b+1):
            cutoff=ln(1+I.mpf('1.5')*(w-1)) if quad else ln(6*w)/2
            if not ceiling(n-w)-X(n-w,b)<cutoff:missed.append(w)
        if not missed:return []
        if a==b:return missed
        mid=(a+b)//2
        return scan(a,mid,quad)+scan(mid+1,b,quad)
    weak,strong=scan(2,n,False),scan(2,n,True)
    assert weak==(list(range(1019,1024)) if r==511 else []) and not strong
    print('unexcluded',weak,strong)
for r,rows in [(511,[506,999,1000,1018,1019,1020,1021,1022,1023]),(188,[699,700]),(149,[660,661]),(134,[645,646])]:
    run(r,rows)
```

## Audit note (independent audit, Nov 2026)

Certificate reproduced exactly. Lifting is **not** the bottleneck: inserting the Part 48 propagation bound g_i ≥ 442·e^{−P_i}
(same plane event) into the Babai sum Σ 2exp(−g_i²/12) gives failure ≈ 2.6·10⁻²⁴⁷ at width 1000, ≈ 1.7·10⁻¹¹ at 950 and
≈ 0.0022 at 920, so Babai lifting is certified at 99% from ≈ 915 upward; the 1017/1018 figures above are specific to the
plane-event certificate. "Crossing stays 1000" refers to these certificates only.
