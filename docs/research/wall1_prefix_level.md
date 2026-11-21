# The terminal minimum from a count of distinct primitive prefixes

For a Haar lattice of determinant one in dimension $n=1023$, the following two inequalities hold **together with probability at least 0.99 per width**, simultaneously for all exact primal BKZ bases of that width. Put $b=\beta, k=n-b, W=L_k, T=\pi_{W^\perp}L, q=g_k=\lambda_1(T)$, using zero-based GS indices and truncated end windows. Write $h_d=V_d^{-1/d}$ and $R_T=h_b(\det W)^{-1/b}$. The absolute threshold is in ambient length units. The relative threshold multiplies the specific prefix's $R_T$.

| Width | $q\ge$ | $q/R_T\ge$ | Part 82 audited absolute / relative | $0.85G_b$ | Target / certified absolute |
|---:|---:|---:|---:|---:|---:|
| 406 | 0.00788035 | 0.00585276 | 0.00654258 / 0.00384694 | 0.36920 | 46.85 |
| 506 | 0.01754086 | 0.00948871 | 0.01696600 / 0.00916855 | 0.81632 | 46.54 |
| 647 | 0.04395095 | 0.01566672 | 0.04255794 / 0.01517094 | 1.82115 | 41.44 |
| 800 | 0.15576670 | 0.03611329 | 0.15090292 / 0.03498389 | 3.41291 | 21.91 |

The first two rows follow directly by integrating over the split at $W$. The last two improve on that integral by regrouping the *same* bad prefixes according to their extension by the shortest quotient line. The direct split alone gives 0.04383720 / 0.01560181 at 647 and 0.14931563 / 0.03459750 at 800. Each entry in the first two numerical columns bounds a distinct-prefix first moment by 0.005 at the stated cut. Markov and a union bound give the joint guarantee. The GSA column is a comparison scale from Part 71, with no GSA assumption in the proof. [Part 71](wall1_surviving_mass.md) · [Part 82 and its input audit](wall1_small_d_caps.md)

## Exact incidence integral

Set $s=\det W, H=s^{-1/k}W, J=s^{1/b}T, r=\lambda_1(J)$. Define
$$
 D_j=A_n-A_j-A_{n-j}-\log(2n),\qquad
 A_1=0,\quad A_d-A_{d-1}=\log(dV_d/\zeta(d)).
$$
For either badness indicator $I$, the exact count mean is
$$
 n e^{D_k}\int_0^\infty s^{n-1}\,ds\int I(s,r)\,
 \mathbf1\{\text{there exists a completion}\}\,d\mu_k(H)d\mu_b(J)du .
$$
Here $u$ is normalized Haar shear on the torus of lifts. Each unoriented primitive $W$ contributes one indicator. A completion has a reduced internal flag in $H$, the HKZ flag in $J$, and must satisfy every crossing shortest-head test on their lifts. All shapes in the unweighted split are independent at fixed $s$. Selection by the completion indicator couples them. Part 46 gives the exact normalized minimum density
$$
 dF_b(r)=\frac{bV_b}{2\zeta(b)}r^{b-1} Z_b(r)\,dr ,
$$
where $Z_b(r)$ is the Haar probability, on the marked primitive-line fiber, of having no shorter competitor. In particular $1-V_b r^b/2\le Z_b(r)\le1$. One may condition the completion integral on this exact minimum by retaining the conditional law of $J$ given $r$. [Part 46](wall1_haar_prefix_law.md) · [Part 67](wall1_completable_prefixes.md)

## An intrinsic necessary condition on the prefix shape

For a witnessing flag let $a_k=0$. Construct upper bounds $\log(g_i/q)\le a_i$ backwards. For each $2\le d\le\min(b,k+1-i)$, a projected block ending by the first quotient column is HKZ by truncation. Thus
$$
 a_i\ \leftarrow\ \min_d\frac{H_d+\sum_{i<l<i+d}a_l}{d-1},
$$
using Part 82's log Hermite caps. Also take the minimum with $a_{i+2}+\tfrac12\log(3/2)$ and $a_{i+4}+\tfrac12\log(32/15+0.00006)$ when the indicated endpoints are at most $k$. These are bounds on the ratio of the **squared** first and last GS lengths in HKZ blocks of ranks three and five, respectively. They constrain both the interior of $W$ and windows crossing into $T$. The numerical gains include this additional geometric input. [Pendavingh and van Zwam, equations (1.3) and (7.12)](https://www.matroidunion.org/stefan/pdf/065879.pdf)

When $k\le b$, $W$'s internal flag is its unique HKZ flag almost surely (modulo signs). The shortest pair in $J$ is also unique. Project the shear of that primitive line onto the last circle of the HKZ flag of $W$. Its centered coordinate has absolute value $u_0$ uniform on $[0,1/2]$, independently of the two shapes. The lift of minimal horizontal magnitude in this projected plane gives
$$
 g_{k-1}^2\le q^2+u_0^2g_{k-1}^2 .
$$
Use the resulting sharper cap in each shear bin. For $k>b$ use the worst endpoint $1/2$. Choosing the most favorable flag after inspecting the shear would invalidate a uniform-coordinate calculation in those widths. The deeper W2 tests are valid for a witnessing flag. Dropping them gives an upper bound and avoids assigning independent acceptance probabilities to overlapping windows. [Two-coset test](wall1_hole_filling2.md)

Within a bin write $B=\sum_{i<k}a_i$. For a unit-determinant $H$ let
$$
 M(H)=\sup_{f}\min_{i<k}(e^{a_i}/g_i(H,f))^k ,
$$
over its internal BKZ flags. This is an intrinsic shape function and $M\le e^B$ by the determinant identity. The necessary test is $s\le M q^k$. For $k\le b$ the supremum uses the canonical HKZ flag. For $k>b$ a canonical HKZ decomposition can parameterize Haar measure on $H$, but testing just that decomposition for completability could discard witnesses. The supremum keeps the existential test without adding any multiplicity. Internal reducedness alone is automatic since every shape admits HKZ.

Put $X=\lambda_1(H)$, $t=\exp(a_0-B/k)$. The first vector has length at least $X$, so $M/e^B\le\min(1,(t/X)^k)$. When the internal flag is HKZ, its first length equals $X$. Multiplying the remaining $k-1$ inequalities also gives $M/e^B\le (X/t)^{k/(k-1)}$. For any $0<f<1$, these imply
$$
 \mathbb E_H[(M/e^B)^m]\le
 \begin{cases}
 f^{km/(k-1)}+1/(1+(ft/h_k)^k/4),&k\le b,\\
 f^{km}+(t/(fh_k))^k/2,&k>b .
 \end{cases}
$$
Split at $X=ft$ in the first row and $X=t/f$ in the second. The Haar void bound in Part 46 and the primitive-pair mean, with $1\le\zeta(k)<2$, prove the respective probability bounds. Cap both at one. This integrates an upper bound on a function of the internal profile with Haar probability. The full profile law can equivalently be written in the HKZ coordinates of Part 46 with all its shortest-selection factors retained.

## Evaluating the quotient tail and radial integral

For the relative cut $q<cR_T$, integrate $s\le M s^{-k/b}r^k$ exactly. The relaxed mean in a bin equals
$$
 e^{D_k}\mathbb E_H[M^b]\int_0^{ch_b}r^{kb}\,dF_b(r).
$$
For the absolute cut $q<\rho$ the corresponding expression is
$$
 e^{D_k}\mathbb E_H\int_0^\infty
 \left[M^b r^{kb}-(r/\rho)^{bn}\right]_+\,dF_b(r).
$$
Both use the exact Haar law. For numerical upper endpoints replace $Z_b(r)/\zeta(b)$ by one in its density. Elementary integration yields powers $c^{b(k+1)}$ and $\rho^{n(k+1)}$, with coefficients, respectively,
$$
 e^{D_k}\frac{h_b^{kb}\mathbb E M^b}{2(k+1)},\qquad
 e^{D_k}\frac{b\,\mathbb E M^{n+1}}{2h_b^b(n+1)(k+1)} .
$$
Average over bin widths. These powers concern the evaluated upper bounds. The exact Part 67 completion mean has no proved power law of this form. The oft-quoted slope near $kb$ is a local numerical observation.

## A second bound with no internal flag count

At 647 and 800 let $P$ be the inverse image in $L$ of the shortest primitive line of $T$. This extension has rank $j=k+1\le b$ and determinant $s q$. Its entire induced flag is HKZ by truncation. The penultimate member recovers $W$ uniquely for almost every ambient lattice. Indeed ties for any two distinct projected primitive lines on any fixed integer flag form a null set of Gram matrices, and there are countably many flags. Thus the map from eligible $W$ to $P$ is injective. Integrating the HKZ shape of $P$ with total probability one gives the primitive mean $e^{D_j+n y}$ at log determinant cap $y$.

Use the worst shear endpoint in $B$. For an absolute cut $y=B+j\log\rho$ suffices. For a relative cut one may take $ny=(b-1)B+bj\log(ch_b)$, by substituting $s=\det(P)/q$. These prove the 647 row. At 800 the rest of the quotient improves the bound. Start with a Part 82 supersolution $U_i$ for prefix log determinants $S_i$. In the absolute case set $x=U_j-U_k$, and in the relative case set $x=U_j-(1-1/b)U_k$. Badness at threshold $e^x$ or $e^x/h_b$, respectively, implies $S\le U$ by the Part 82 maximum principle. For every $0\le p\le k$ put $m=j-p$ and $w=U_p+\sum_{p\le i<k}a_i$. The tail test gives $S_j\le w+m\log q$. In the absolute case cap $S_j$ by $w+mx$. In the relative case $(b-1)\log q\le bx-S_j$, giving the cap $((b-1)w+bmx)/(b-1+m)$. Integrate up to the smallest of these caps and $U_j$. This uses windows extending past the first quotient line through the original supersolution.

## Where the bound loses mass

At the certified absolute thresholds the largest possible normalized quotient radius in the direct relaxation is $r_0=\rho^{n/b}e^{B/b}$, using the worst shear bin. The certificate checks $V_b r_0^b/2<e^{-2000}$ at all four widths. Thus the replacement of the exact shortest-line selector $Z_b$ by one has relative error at most $e^{-2000}/(1-e^{-2000})$ in these integrals. Dropping the primitive factor costs at most $\zeta(b)-1$ separately. In relative units the analogous error uses $c^b/2$. A Poisson assumption is unnecessary.

The large contribution in the **upper integral** comes from prefixes near their maximum allowed determinant. At widths 406 and 506, at the worst allowed determinant $s_0=\rho^k e^B$, the log means of all prefixes up to $s_0$ are approximately 2090 and 2359 nats, respectively. The log short-line factors there are approximately −2088 and −2357. For the extension integral at 647 and 800 the top $(\log 100)/1023$ of the retained log-determinant interval contributes exactly 99% of its mass. Neither calculation identifies a typical truly completable shape. At $0.85G_b$ the earlier single-prefix relaxation already gave log-mean upper bounds of 725613, 564759, 359418 and 169535. At quarter GSA the width-800 upper bound was 152955. These are bounds on a relaxation, not lower bounds on genuine bad prefixes. The remaining unknown is the joint Haar mass of shapes and shears admitting at least one crossing-compatible flag near the relevant determinants. The fixed-width asymptotic for exact basis multiplicity cannot determine it. The results here concern Haar input. Transfer to the planted discrete ensemble remains open. [Basis multiplicity](wall1_basis_multiplicity.md) · [Wall 1 frontier](../PROOF_GAP.md)

## Interval certificate

Run the Python block from the repository root with mpmath and NumPy. The Part 82 cap construction verifies the LCZ witnesses and the outward rounding. For ranks 4–16 this version uses Table 1.1 density bounds wherever that table gives a three-point bound. The two integer dents are witnesses. Their search has no role in the verification. [Cohn, de Laat and Salmon, Table 1.1](https://arxiv.org/pdf/2206.15373)

```python
from pathlib import Path
def block(name):
    path = Path("docs/research/wall1_" + name + ".md")
    return path.read_text().split("\n```python\n", 1)[1].split("\n```", 1)[0]
src82 = block("small_d_caps").split("lattice = C.copy()")[0]
small_rows = ".636108 .512646 .410304 .321148 - .191121 .143411 .106726 .079712 .060165 .045062 .033757 .024995"
exec(src82.replace('for d,s in dens.items():',
                   'dens.update(dict(enumerate(small_rows.split(),4)))\nfor d,s in dens.items():'))
def gh(d):
    return I.exp(I.loggamma(1+I.mpf(d)/2)/d)/I.sqrt(I.pi)
def upward(x):
    return int((M*x).b)+1
kz = {2:upward(I.ln(I.mpf(3)/2)/2),
      4:upward(I.ln(I.mpf(32)/15+I.mpf(".00006"))/2)}
def tail(b, u):
    k=n-b
    S=[0]*(k+2)
    for i in reversed(range(k)):
        a=min((C[d]+S[i+1]-S[i+d]+d-2)//(d-1)
              for d in range(2,min(b,k+1-i)+1))
        for j,v in kz.items():
            if i+j<=k: a=min(a,v+S[i+j]-S[i+j+1])
        if i==k-1: a=min(a,upward(-I.ln(1-u*u)/2))
        S[i]=S[i+1]+a
    return S
def smaller(x,y):
    return I.mpf([min(x.a,y.a),min(x.b,y.b)])
def split_mean(b):
    k=n-b
    D=A[n]-A[k]-A[b]-I.ln(2*n)
    bins=[0,9900,9990,9999,10000] if k<=b else [0,10000]
    K=[I.mpf(0),I.mpf(0)]
    for lo,hi in zip(bins,bins[1:]):
        S=tail(b,I.mpf(hi)/20000)
        B=I.mpf(S[0])/M
        t=I.exp(I.mpf(S[0]-S[1])/M-B/k)
        for rel,m in enumerate((n+1,b)):
            cost=I.mpf(1)
            if k<=b:
                # Integrate a necessary condition on the canonical first GS length.
                for j in range(1,100):
                    f=I.mpf(j)/100
                    cost=smaller(cost,f**(I.mpf(k)*m/(k-1))
                                 +1/(1+(f*t/gh(k))**k/4))
            else:
                for j in range(1,100):
                    f=I.mpf(j)/100
                    cost=smaller(cost,f**(k*m)+(t/(f*gh(k)))**k/2)
            L=D+m*B-I.ln(2)
            if rel: L+=k*b*I.ln(gh(b))-I.ln(k+1)
            else: L+=-b*I.ln(gh(b))+I.ln(I.mpf(b)/((n+1)*(k+1)))
            K[rel]+=I.mpf(hi-lo)/10000*cost*I.exp(L)
    return K
def extension(b,rel,dent=None):
    k=n-b
    assert k+1<=b
    S=tail(b,I.mpf(1)/2)
    B=I.mpf(S[0])/M
    D=A[n]-A[k+1]-A[b-1]-I.ln(2*n)
    if dent is None:
        if rel: return D+(b-1)*B+b*(k+1)*I.ln(gh(b))
        return D+n*B
    v=profile(b,dent,True)
    T=[0]
    for g in v: T.append(T[-1]+g)
    U=[I.mpf(n*z-j*T[-1])/(n*M) for j,z in enumerate(T)]
    x=U[k+1]-U[k]+(U[k]/b if rel else 0)
    y=U[k+1]
    for p in range(k+1):
        m=k+1-p
        w=U[p]+I.mpf(S[p])/M
        z=((b-1)*w+b*m*x)/(b-1+m) if rel else w+m*x
        y=smaller(y,z)
    assert D+n*y < -I.ln(200)
    return I.exp(x)/(gh(b) if rel else 1)
rows={406:(".00788035",".00585276"),506:(".01754086",".00948871"),
      647:(".04395095",".01566672"),800:(".15576670",".03611329")}
for b,(absolute,relative) in rows.items():
    k=n-b
    K=split_mean(b)
    for rel,s in enumerate((absolute,relative)):
        power=(b if rel else n)*(k+1)
        l=I.ln(K[rel])
        direct=I.exp((-I.ln(200)-l)/power)
        if k+1<=b: l=smaller(l,extension(b,rel))
        ok=l+power*I.ln(I.mpf(s)) < -I.ln(200)
        if b==800:
            val=extension(b,rel,(3624519108,3630984424)[rel])
            ok=ok or val>I.mpf(s)
        assert ok
        print(b,rel,direct,s)
    B=I.mpf(tail(b,I.mpf(1)/2)[0])/M
    rho=I.mpf(absolute)
    x=k*I.ln(rho)+B
    pair=x+b*I.ln(rho/gh(b))-I.ln(2)
    assert pair < -2000
    if b in (406,506):
        mass=A[n]-A[k]-A[b]-I.ln(2*n)+n*x
        assert abs(mass-(2090 if b==406 else 2359))<1
        assert abs(pair+(2088 if b==406 else 2357))<1
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    target=I.mpf(".85")*I.exp((2*b-n-1)*slope)
    print("GSA comparison",b,target,target/rho)
```
