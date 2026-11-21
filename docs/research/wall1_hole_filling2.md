# A rank-33 packing certificate excludes all twelve Part 77 boxes

**Theorem.** On every profile in each of the twelve Part 77 boxes, the rank-33 projected prefix starting at index 989 (zero-based) contains a nonzero vector strictly shorter than its head. The next column, at index 1022, is deep. The joint window acceptance probability on each box is zero for every law of the size-reduction coefficients. Thus the accepted contribution of each box is exactly zero, including the box responsible for the 219222-nat residual lower bound. The integral over the complement and the global terminal radius remain open. [Part 77 boxes](wall1_lcz_all_widths.md)

## The cap that closes the gap

Cohn and Elkies, Appendix C, Table 3, give **52.90924** as their dimension-33 upper bound on *center density*. We round outward to 53. Their proof covers general sphere packings and uses exact rational polynomial sign checks. For minimum separation $s$ and $q$ translates of a lattice of determinant $d$, center density is $q(s/2)^{33}/d$. In particular the log cap on $s^{33}/d$ for one translate is $H=33\log 2+\log 53=26.844148873$ (rounded up). The Part 77 dimension-33 row uses $27.492201140$, the smaller of its two candidates. Replacing just that cap gains more than **0.64805 nat**. The calculation keeps the original box centers. A lattice-specific upper bound would suffice for the one-prefix contradiction, while the two-coset argument requires a periodic-packing bound. [Cohn–Elkies, §6 and Table 3](https://annals.math.princeton.edu/wp-content/uploads/annals-v157-n2-p09.pdf) · [Earlier two-coset test](wall1_hole_filling.md)

Put $j=33$, $R=g_i$, $d=\prod_{l=i}^{i+j-1}g_l$, $h=g_{i+j}/R$, and $r=R\sqrt{1-h^2}$. Orthogonality of the last GS coordinate gives this exact height-one section. The horizontal forbidden set is the projection of the open $r$-ball to the prefix torus. Write $A=H+\log d-j\log R$ and $B=A-j\log(r/R)$. At the common start the full-box enclosures are

$$
0.1742575<h<0.1742584,\qquad
-0.12710<A<-0.12697,\qquad 0.38169<B<0.38184.
$$

Prefix survival would pack one translate at separation $R$ and require $A\ge0$. This already contradicts the bounds. Independently, survival plus a missed shift would pack two translates at separation $r$ and require $B\ge\log 2$. The improved test clears that threshold by more than **0.31130 nat**. The first contradiction matters for interpretation of the second: there is no passing prefix history at this start on which to condition. The fixed-profile negative log joint acceptance is infinite.

## What uncovered volume alone gives

Let $T=\mathbb R^j/D$ have Haar probability, $\lambda_1(D)\ge R$, $0<r\le R$, and let $p$ be the fraction of shifts at torus distance at least $r$ from zero. Let $k$ be the maximum size of an $r$-separated subset of $T$. Compactness bounds $k$. An extremal set gives a periodic packing, so $k\le K=\lfloor e^B\rfloor$ in the corresponding dimension and cap normalization. For every shift $x$, at least one of the $k$ points has distance strictly below $r$ from $x$ by maximality. Averaging the number of such neighbors gives $k(1-p)\ge1$. Hence

$$
 p\le 1-1/k\le 1-1/K.
$$

For $K=1$ this is hard coverage. For $K=2$ it gives at least $\log 2$ nats of suppression. More generally the per-column guaranteed penalty is $\log(K/(K-1))$. Equivalently, a sufficiently large measured uncovered fraction forces additional cosets. A lower bound from a deepest hole gives only a projected ball of radius $\mu-r$ for $\mu>r$, which can have arbitrarily small volume. Even its Euclidean volume requires injectivity (one may truncate the radius at $R/2$). Greedy selection removes neighborhoods of radius $r$, whereas disjoint packing balls have radius $r/2$.

For a concrete obstruction take $D=\mathbb Z^4$, $R=\mu=1$. The unique deepest class is $(1/2,1/2,1/2,1/2)$. By compactness its superlevel sets for $r\uparrow1$ shrink inside any neighborhood of that class. For $r<1$ sufficiently close to one they have positive volume and diameter below $r$. There cannot be two separated extra cosets, even though the section is deep. The deepest class also has order two. For a hole of higher order, a subgroup construction requires distance at least $r$ for every nonzero multiple. Positive uncovered volume alone therefore supplies no general $\log 3$ hard threshold.

## Chain calculation

The table compares two computations on the **same** twelve boxes. Entries follow cut order .25, .5, .85. The middle column counts rank-33 starts certified uniformly deep and hard by the improved height-one comparison. One such start suffices. The last column encloses the total **finite** penalty from the uncovered-volume bound with the original periodic caps, before installing the rank-33 improvement.

| Width | Certified rank-33 hits | Original-cap deep chain penalty (nats) |
|---:|---:|---|
|406|1 / 1 / 1|[167,169] / [156,158] / [156,158]|
|506|1 / 1 / 1|[120,122] / [117,118] / [116,118]|
|647|2 / 1 / 1|[73,75] / [69,71] / [68,70]|
|800|2 / 1 / 1|[23,24] / [21,22] / [20,22]|

For each endpoint take the strongest penalty over deep starts ($h<1/\sqrt2$) of admissible width, then sum over endpoints. On earlier passing histories the fresh column projects uniformly onto each candidate torus. Iterated conditioning justifies charging one start at a time at each endpoint, including overlapping windows. Even giving the entire 24 nats as an additional credit leaves at least 219198 nats at the closest target with the old caps. The sharpened cap eliminates these boxes without any probabilistic credit. It gives no uniform finite law in the mean short-vector count on other profiles. Multiple-height correlations are analyzed separately. [Joint coverage](wall1_multiheight_coverage.md)

## Interval certificate

Run this Python block from the repository root with NumPy and mpmath. The integer profile recurrence and cap rows come from the Part 77 construction. Common centering cancels. In billionths, a log difference changes by at most 2000 and the prefix log slack changes by at most $2000(j-1)$. For the chain, a monotone grid encloses the section correction. The integer log thresholds enclose the floor of the multiplicity ratio up to 1001, beyond which zero and the weight at 1001 bound the penalty. The interval tests below use no sampled coefficients or heuristic packing densities.

```python

from pathlib import Path
from mpmath import iv as I
import numpy as np
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
# Integer enclosures for the section correction at a grid of log drops.
def ends(x):
    return int((M*x).a)-1, int((M*x).b)+1
grid=np.array([ends(-I.ln(1-I.exp(-2*I.mpf(k)/1000))/2)
               for k in range(345,20001)])
logs=np.array([ends(I.ln(k)) for k in range(1,1002)])
weights=np.array([ends(I.ln(I.mpf(k)/(k-1))) for k in range(2,1002)])
deep=ends(I.ln(2)/2)
for b in (406,506,647,800):
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    for f in (".25",".5",".85"):
        v=np.array(solve(b,I.mpf(f)*I.exp((2*b-n-1)*slope),False),dtype=np.int64)

        j=33
        H=j*I.ln(2)+I.ln(53)
        i=989
        z=(int(v[i+j]-v[i])+I.mpf([-2000,2000]))/M
        A=H+(int(sum(v[i:i+j])-j*v[i])+I.mpf([-64000,64000]))/M
        B=A-j*I.ln(1-I.exp(2*z))/2
        assert I.mpf("-.12710")<A and A<I.mpf("-.12697")
        assert I.mpf(".38169")<B and B<I.mpf(".38184")
        assert I.mpf(".1742575")<I.exp(z) and I.exp(z)<I.mpf(".1742584")
        hits=0
        for i in range(n-j):
            z=I.mpf(int(v[i+j]-v[i])+2000)/M
            if 2*z>=-I.ln(2): continue
            A=H+I.mpf(int(sum(v[i:i+j])-j*v[i])+64000)/M
            hits+=int(A-j*I.ln(1-I.exp(2*z))/2<I.ln(2))
        T=np.r_[0,v.cumsum()]
        low=np.zeros(n,dtype=np.int64)
        high=low.copy()
        for j in range(1,b):
            d=v[:-j]-v[j:]
            a=P[j]-j*v[:-j]+T[j:-1]-T[:-j-1]
            # Grid index k denotes drop k/1000. The correction decreases.
            kl=(d-2000)//10**6
            ku=(d+2000+10**6-1)//10**6
            possible=d+2000>=deep[0]
            certain=d-2000>deep[1]
            if not possible.any(): continue
            hi=a+2000*(j-1)+j*grid[np.clip(kl,345,20000)-345,1]
            lo=a-2000*(j-1)+j*np.where(ku>20000,0,grid[np.clip(ku,345,20000)-345,0])
            # At a possible deep pair use drop >= log(2)/2 > .345.
            kmin=np.searchsorted(logs[:,1],lo,side='right')
            kmax=np.searchsorted(logs[:,0],hi,side='right')
            assert (kmin[possible]>=2).all()
            low[j:]=np.maximum(low[j:],np.where(certain & (kmax<1001),
                        weights[np.clip(kmax,2,1001)-2,0],0))
            high[j:]=np.maximum(high[j:],np.where(possible,
                        weights[np.clip(kmin,2,1001)-2,1],0))
        print(b,f,hits,int(low.sum()//M),int(-(-high.sum()//M)))
 ```
