# Surviving profile mass at rank 1023

Even at one quarter of GSA, enforcing every Part 65 block inequality leaves at least 230166 nats of log Haar intensity at each width. Integrating the exact width-three acceptance still leaves at least 229742 nats. These are lower bounds on first moments of relaxed basis counts. The probability that a lattice admits a fully BKZ-reduced bad basis remains open.

Let $k=n-b$, $n=1023$, $x_i=\log g_i$, $S_j=\sum_{i<j}x_i$, and $S_0=S_n=0$. Use $D_b(\rho)$ given by $x_k<\log\rho$ and $d x_i-\sum_{j=i}^{i+d-1}x_j\le H_d$ for every start and $2\le d\le\min(b,n-i)$. Here $H_d$ is the minimum of the candidates used in the Part 65 certificate. The table gives $J=K_n\int_D e^F\,dS$, $F=2\sum_j S_j$, for positively oriented bases under the Part 50 Haar probability normalization. For the literal Lebesgue integral of $e^F$, add $-\log K_n\in[938544.39937,938544.39954]$ to the log results. Identifying oriented signs subtracts $1022\log 2$ from the log intensities. [Part 50](wall1_volume_method.md) · [Part 65](wall1_one_sided_terminal.md)

Each interval holds at the exact Part 65 value $\rho=cG_b$. At $c=.85$ it also covers the four literal rounded radii in the question. The width-three column bounds $\log W_3$ on the entire respective witness box. The weighted column bounds $\log J_3=\log(K_n\int_D e^F W_3\,dS)$ from below. The last column bounds the center's density deficit $\sup_D F-F(\mathrm{center})$ from above.

| Width | $c$ | $\log J$ | $\log W_3$ on box | $\log J_3$ lower | Density deficit upper |
|---:|---:|---:|---:|---:|---:|
| 406 | .25 | [812265, 834050] | [-490, -416] | 811777 | 9070 |
| 406 | .5 | [826956, 841105] | [-470, -401] | 826487 | 1435 |
| 406 | .85 | [829271, 842097] | [-459, -393] | 828813 | 112 |
| 506 | .25 | [573127, 596269] | [-461, -390] | 572667 | 10428 |
| 506 | .5 | [589837, 605090] | [-441, -375] | 589398 | 2538 |
| 506 | .85 | [594225, 607041] | [-425, -363] | 593801 | 102 |
| 647 | .25 | [373340, 395255] | [-440, -372] | 372901 | 9201 |
| 647 | .5 | [387960, 403615] | [-420, -357] | 387541 | 2941 |
| 647 | .85 | [392871, 405920] | [-405, -345] | 392467 | 336 |
| 800 | .25 | [230166, 253386] | [-425, -360] | 229742 | 10506 |
| 800 | .5 | [246740, 263398] | [-406, -345] | 246335 | 3944 |
| 800 | .85 | [252998, 266451] | [-390, -333] | 252609 | 739 |

The exponential relaxation retains log intensity at least the third column's lower endpoint minus 1022 (minus 511 with horizontal caps). Thus even its most favorable budget leaves at least 229144 nats, or 229655 with horizontal caps. The width-three result uses fresh feasible boxes and integrates the pass weight over them. In particular the exclusion of the older Part 50 witnesses has no bearing on these lower bounds. No tested radius follows from either first moment, even with the sign divisor. The existing Part 65 absolute radii are .00609055, .01588487, .03996130 and .14264140. The calculation gives no new certified radius. [Window asymptotics](wall1_window_asymptotics.md) · [Part 61](wall1_poisson_exponent.md) · [Frontier](../PROOF_GAP.md)

## Integral bounds as functions of the cap

Use Part 50's backward minimum recurrence in units $1/M$ with final entry zero. Subtract a nonnegative dent at $k$ and center the result by subtracting its mean. For the upper bound round each ordinary row upward. Write $U$ for the resulting prefix sums. Use the uncut envelope when it suffices, or choose a dent with $U_{k+1}-U_k\ge\log\rho$. At ordinary rows a minimizing block provides a reverse inequality. A positive maximum of $S-U$ would propagate to its left neighbor by the convex-average row (by the terminal cap at a dent), contradicting the endpoints. Integrating the dominating orthant gives
$$\log J\le\log K_n+2\sum_{j=1}^{n-1}U_j-(n-1)\log 2.$$

For a lower bound, round downward, reserve $4d\epsilon$ of slack per block, and cap each backward log drop at .055 before applying the dent, with $\epsilon=10^{-6}$. Each operation decreases the current row's head and all earlier rows are computed subsequently. Perturb the first $n-1$ entries independently within $\pm\epsilon$, fix the last, then recenter. Block residuals change by at most $2(d-1)\epsilon$ and the cut log by at most $2\epsilon$. Choose the lower dent so the whole box satisfies the strict cap. The Jacobian in the first $n-1$ centered logs is $\det(I-\mathbf1\mathbf1^T/n)=1/n$ and passage to prefixes has unit Jacobian. Centering cancels in $F$ and its perturbation costs less than $n^2\epsilon<2$. Thus
$$\log J\ge\log K_n+F(\mathrm{center})-2+(n-1)\log(2\epsilon)-\log n.$$
These formulas take a positive radius as input. Between tabulated radii monotonicity also gives immediate enclosures. Bisection selects witnesses, with the cap comparisons checked directly. An exact unrounded density maximizer has its final width-two inequality tight (the dent is earlier), hence $W_3=0$ there. Its value alone cannot estimate the integral.

## Width-three weight on a box

All adjacent ratios exceed or equal $m=\exp(-.055002)$. For two successive ratios $u,w$ one has $1-u^2w^2\le1-m^4<m^2/4$. Thus throughout the folded new-state interval $0\le v\le1/2$ the arc from the second lift is empty. The Part 69 kernel integrates independently of its old state. Its row sum is exactly
$$B(u,w)=2\int_{\sqrt{(1-w^2)_+}}^{1/2}
  [1-2\sqrt{(1-u^2w^2-u^2v^2)_+}]_+\,dv.$$
Multiply the first pair factor by these row sums in column order. In general Part 69 composes varying operators, and supplies no product bound from the spectral radii of frozen geometric profiles. Here the row sums give an exact product with two local ratios per factor. The integrand increases in $v,u,w$ and the integration domain increases in $w$. Shifting the center log ratios by $\pm2\epsilon$ and using endpoint sums on eight bins therefore encloses the full box. All numerical conclusions above are interval bounds. The sole use of the geometric-series model is to name the radii. [Part 69](wall1_joint_acceptance.md)

## Reproducible certificate

Run with Python 3, NumPy and mpmath. The first loop implements the same candidates and zeta enclosure as Part 65. Integer suffix sums drive both recurrences. Printed endpoints are rounded outward with checked slack.

```python


from math import comb
from fractions import Fraction
from mpmath import iv as I

I.dps = 45
n, M = 1023, 10**9
small = [0, 0, Fraction(4,3), 2, 4, 8, Fraction(64,3), 64, 256]
C, A = [0,0], [0,0]
for d in range(2,n+1):
    u = I.mpf(d)/2
    if d < len(small):
        z = Fraction(small[d])
        H = I.ln(I.mpf(z.numerator)/z.denominator)/2
    else:
        H = u*I.ln(2/I.pi)+I.loggamma(2+u)
    D = d+1
    s = 4/(5*I.sqrt(D))
    a = 1/(D*s)
    c = (2*a-s)/D-s*a*a
    assert c > 0 and 2*a-s > 0 and a*a-2*a*s+I.mpf(3)/(D+2)>0
    P = I.ln((1-s)*(1+a)**2/c)+u*I.ln(2*(1-s)/I.pi)+I.loggamma(1+u)
    def imin(x,y):
        return I.mpf([min(x.a,y.a),min(x.b,y.b)])
    bound = imin(P,H)
    for v in (1,2,3,4,5,6):
        # Scaled Gegenbauer recurrence for signs.
        prev, cur = 1,v*(D-2)
        j=1
        while cur>0 and j<150:
            prev,cur=cur,(2*j+D-2)*v*cur-100*j*(D+j-3)*prev
            j+=1
        if cur>0: continue
        deg=j-1
        dim=comb(D+deg-1,deg)+comb(D+deg-2,deg-1)
        t=I.mpf(v)/10
        s=t-2*(1-t)/d
        cand=I.ln((1-s)*dim/(t-s))+u*I.ln(2*(1-s)/I.pi)+I.loggamma(1+u)
        bound=imin(cand,bound)
    C.append(int((M*bound).b)+1)
    assert C[d]-2 <= M*bound < C[d]
    if d<=32:
        partial = sum(I.mpf(j)**(-d) for j in range(1,65))
        lo = partial+I.mpf(65)**(1-d)/(d-1)
        hi = partial+I.mpf(64)**(1-d)/(d-1)
        lz = I.mpf([I.ln(lo).a,I.ln(hi).b])
    else:
        lz = I.mpf([0,(3*I.mpf(2)**(-d)).b])
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u)-lz)


assert -A[n] > I.mpf('938544.39937') and -A[n] < I.mpf('938544.39954')
import numpy as np
def profile(b,t,upper):
    T=np.zeros(n+1,dtype=np.int64)
    ds=np.arange(2,b+1)
    c=np.array(C,dtype=np.int64)
    h=c[ds]+ds-2 if upper else c[ds]-2-4000*ds
    for i in reversed(range(n-1)):
        d=ds[:n-i-1]
        z=int(((h[:len(d)]+T[i+1]-T[i+d])//(d-1)).min())
        if not upper:
            z=min(z,int(T[i+1]-T[i+2])+55000000)
        assert abs(z)+abs(t)+abs(int(T[i+1])) < 10**14
        T[i]=T[i+1]+z-(t if i==n-b else 0)
    assert max(map(abs,map(int,T)))<10**14
    return [int(a)-int(b) for a,b in zip(T,T[1:])]
def coords(v,k):
    return I.mpf(n*v[k]-sum(v))/(n*M)
def score(v):
    return I.mpf(sum((n-1-2*i)*a for i,a in enumerate(v)))/M
def solve(b,target,upper):
    k=n-b
    def fits(v):
        z=coords(v,k)
        if not upper: z+=I.mpf(2)/10**6
        return I.exp(z)<target
    v=profile(b,0,upper)
    if fits(v): return v # uncut envelope or feasible center
    lo,hi=0,10*M
    while not fits(profile(b,hi,upper)): hi*=2
    while hi-lo>10000:
        t=(hi+lo)//2
        if fits(profile(b,t,upper)): hi=t
        else: lo=t
    v=profile(b,lo if upper else hi,upper)
    assert I.exp(coords(v,k))>target if upper else fits(v)
    return v
def ceiliv(x):
    z=int(float(x.b))+2
    assert x<z
    return z
def flooriv(x):
    z=int(float(x.a))-2
    assert x>z
    return z
for b,rounded in zip([406,506,647,800],['.369','.816','1.822','3.413']):
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    G=I.exp((2*b-n-1)*slope)
    for frac in ['.25','.5','.85']:
        R=I.mpf(frac)*G
        low=min(R,I.mpf(rounded)) if frac=='.85' else R
        high=max(R,I.mpf(rounded)) if frac=='.85' else R
        v=solve(b,low,False)
        U=solve(b,high,True)
        H=A[n]+score(U)-(n-1)*I.ln(2)
        L=A[n]+score(v)-2+(n-1)*I.ln(I.mpf(2)/10**6)-I.ln(n)
        # On the whole box integrate folded subdiagonals on [.49,.5].
        m=I.exp(-I.mpf('.055002'))
        assert 1-m**4<m*m*I.mpf('.49')**2 and 1-m*m<I.mpf('.49')**2
        def logpass(offset,upper):
            p=I.mpf(1)
            for j in range(1,n):
                w=I.exp(I.mpf(v[j]-v[j-1]+offset)/M)
                a=I.sqrt(max(0,1-w*w))
                if j==1: p*=1-2*a
                else:
                    q=I.mpf(0)
                    for h in range(8):
                        left=I.mpf(h)/16
                        right=I.mpf(h+1)/16
                        y=right if upper else left
                        width=max(0,right-max(a,left))
                        rad=I.sqrt(max(0,1-(u*w)**2-(u*y)**2))
                        q+=2*width*max(0,1-2*rad)
                    p*=q
                u=w
            return I.ln(p)
        wl=logpass(-2000,False)
        wh=logpass(2000,True)
        print(b,frac,flooriv(L),ceiliv(H),flooriv(wl),ceiliv(wh),
              flooriv(L+wl),ceiliv(score(U)-score(v)),flush=True)
```
