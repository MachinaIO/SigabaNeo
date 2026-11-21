# Hole filling on the relocated prefix boxes


The two-coset argument gives a covering bound on a surviving prefix when its packing density exceeds half an upper bound for arbitrary packings. Shrinking the balls makes this a quantitative test at the actual column radius. It certifies **zero hard exclusions on all twelve Part 77 boxes**. The closest effective log gap on each box lies between 1.0297 and 1.031 nats, against a threshold of $\log 2=0.693147\ldots$.

## Packing a geodesic to a deep hole

Let $D$ be a full lattice in dimension $j$, $R=\lambda_1(D)$, $d=\det D$, and $\Delta=V_j(R/2)^j/d$. Take an upper bound $U$ for densities of periodic equal-ball packings and set $F=U/\Delta$. On the flat torus choose a farthest point with shortest lift $h$, of length $\mu=\mu(D)$. Every subsegment of $[0,h]$ realizes torus distance between its endpoints. Otherwise a shorter path on that subsegment shortens the path to $h$.

For each integer $q\ge2$, the $q$ equally spaced points including both endpoints give distinct translates of $D$ with mutual distances at least $\mu/(q-1)$. Within each translate the separation is $R$. Consequently
$$
 q\min\{1,\mu/((q-1)R)\}^{j}\le F.
$$
For $q>F$ this gives $\mu/R\le(q-1)(F/q)^{1/j}$. The right side increases with real $q>1$, so the best such integer is $\lfloor F\rfloor+1$. In particular $F<2$ gives $\mu/R\le(F/2)^{1/j}$. If $F\ge2$, the bound from the first admissible $q\ge3$ exceeds one. Even at $F=1$ the two-coset bound on the covering-to-packing ratio is $2^{1-1/j}$. A hypothesis $F\le e^{\delta j}$ gives the factor-two regime only when $\delta j<\log 2$ or an independently tighter gap is available.

In fact the proposed ratio $1+o(1)$ is geometrically impossible in growing dimension. At a Voronoi vertex there are $j+1$ affinely independent equidistant centers $x_i$ (the active bisectors span rank $j$). Their pairwise distances are at least $R$. With $c$ the vertex and $\bar x$ their centroid,
$$
 \binom{j+1}{2}R^2\le\sum_{i<k}\|x_i-x_k\|^2
 =(j+1)\sum_i\|x_i-\bar x\|^2
 \le(j+1)\sum_i\|x_i-c\|^2\le(j+1)^2\mu^2.
$$
Hence $2\mu/R\ge\sqrt{2j/(j+1)}$ for every lattice. At cross-separation $R/\sqrt2$, using balls of radius $R/(2\sqrt2)$ on both cosets gives total density $2^{1-j/2}\Delta$. Adjoining $h$ as a generator gives an index-two extension exactly when its torus class has order two. For order $m$, every nonzero multiple modulo $m$ needs the requisite separation. A single deep hole supplies no such guarantee. The periodic union proof avoids this requirement. Additional separated holes could improve the bound if their existence were proved.

## The fresh-column test

Use local head $R=g_i$. Prefix survival gives $\lambda_1=R$ because the head attains the tested minimum. For a positive section radius $r_m=(R^2-m^2g_{i+j}^2)^{1/2}$ at integer height $m\ge1$, define
$$
 B_m=\log F-j\log(r_m/R).
$$
If $B_m<\log 2$, a hole at distance $\ge r_m$ would violate the two-coset density bound. Equality still gives coverage up to a Haar-null boundary since $r_m<R$. For $q\ge3$ the geodesic construction requires $F\le q(r_m/((q-1)R))^j$, strictly weaker than the two-coset test for $j\ge2$. Since $r_m\le r_1$, checking height one rules out every height for this sufficient test. The [affine successive-minima estimate](wall1_void_affine.md) and the [dual Gaussian test](wall1_dual_coverage.md) use different upper bounds on $\mu$.

For $H_j$ in the normalization of Part 77, $\log F=H_j-j\log R+\log d$. We use the published LCZ certificate in dimensions through eight to avoid applying a lattice-only Hermite constant to a periodic union. From dimension nine the older candidates used here are Blichfeldt's general packing bound and spherical-code bounds, so the smaller certified cap applies. These are attained upper-bound certificates. The uncomputed optimum of an LP hierarchy could be smaller. [Part 77 cap construction and box definition](wall1_lcz_all_widths.md) · [Cohn–Zhao packing inequalities](https://arxiv.org/abs/1212.5966)

The three entries in each cell follow cut order .25, .5, .85. Counts enumerate start-depth pairs whose full-box ratio enclosure reaches $e^{-.32}$ or lower, including all deep columns with ratio below $1/\sqrt2$. The adjacent-ratio bound $e^{-.055002}$ excludes depths below six. Repeated endpoints from different starts are counted separately.

|Width|Candidate pairs checked|Hard hits|Part 77 residual log lower (nats)|
|---:|---:|---:|---:|
|406|298198 / 299980 / 300224|0 / 0 / 0|796562 / 811370 / 813763|
|506|348508 / 351057 / 351693|0 / 0 / 0|559914 / 576648 / 581065|
|647|403671 / 406927 / 407958|0 / 0 / 0|361765 / 376362 / 381267|
|800|441599 / 445679 / 447204|0 / 0 / 0|219222 / 235721 / 241940|

The certificate proves $B_1>1.0297$ at each candidate throughout its box. Each box center has a genuinely deep rank-33 example with $B_1<1.031$. Thus the minimum misses the threshold by over 0.3365 nat. The additional hard-exclusion exponent is zero. The residual bounds concern the log of the Part 77 upper-bound integral. No lower bound on actual survival follows. A stronger cap, additional torus points with controlled mutual distances, or a conditional estimate of the uncovered volume would supply information absent here. No heuristic shape assumption or independence estimate is used.

## Reproduction

Run this block at the repository root with NumPy and mpmath. It reuses the integer profile recurrence and bisection of Part 77. The arrays store billionths of a nat. Changing each log length by at most 1000 units before common centering changes a difference by at most 2000 and a rank-$j$ log slack by at most $2000(j-1)$. For lower slack $a/M$ and lower log ratio $t/M$, the comparison inverts $a/M-(j/2)\log(1-e^{2t/M})>1.0297$ monotonically. The sentinel handles slack already above threshold (all stored differences exceed the sentinel by the profile recurrence's integer bounds). Sorting only groups independent certified comparisons.

```python
from pathlib import Path
from mpmath import iv as I
import numpy as np
from functools import lru_cache
I.dps=40
root=Path("docs/research")
def read(stem):
    return (root/("wall1_"+stem+".md")).read_text()
base=read("surviving_mass")
M,n=10**9,1023
C=[0,0]
P=[0,0]
rows=read("lcz_all_widths").split("## All dimensions")[1].split("```text")[1]
for row in rows.split("```")[0].strip().splitlines()[1:]:
    j,_,_,lc,old=map(int,row.split())
    assert len(C)==j
    C.append(min(lc,old))
    P.append(lc if j<=8 else min(lc,old))
exec(base[base.index("def profile"):base.index("def ceiliv")])
# B = cap slack - j log(r_1/R). Prove B > 1.0297 on each box.
@lru_cache(None)
def threshold(j,a):
    x=(I.mpf(a)/M-I.mpf("1.0297"))*2/j
    if x>=0: return -10**18
    return int((M*I.ln(1-I.exp(x))/2).b)+2

def verify(j,a,t):
    # B increases with both a and t. The limiting t decreases with a.
    order=np.argsort(a)
    a,t=a[order],t[order]
    def visit(l,h):
        if t[l:h].min()>threshold(j,int(a[l])): return
        assert h-l>1
        k=(l+h)//2
        visit(l,k)
        visit(k,h)
    visit(0,len(a))

for b in (406,506,647,800):
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    for f in (".25",".5",".85"):
        v=np.array(solve(b,I.mpf(f)*I.exp((2*b-n-1)*slope),False),dtype=np.int64)
        T=np.r_[0,v.cumsum()]
        count=0
        upper_witness=False
        for j in range(6,b):
            a=P[j]-j*v[:-j]+T[j:-1]-T[:-j-1]
            t=v[j:]-v[:-j]
            mask=t-2000 <= -320000000
            count+=int(mask.sum())
            if mask.any():
                verify(j,a[mask]-2000*(j-1),t[mask]-2000)
            if j==33:
                for ai,ti in zip(a[mask],t[mask]):
                    z=I.mpf(int(ti))/M
                    B=I.mpf(int(ai))/M-j*I.ln(1-I.exp(2*z))/2
                    if B<I.mpf("1.031") and 2*z < -I.ln(2):
                        upper_witness=True
                        break
        assert upper_witness
        print(b,f,count)
```
