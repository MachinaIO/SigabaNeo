# Joint window acceptance at fixed Gram–Schmidt lengths

At width three, a single real state suffices to integrate all overlapping shortest-vector tests. For the eight-dimensional profile $g_i=0.92^i$, the joint probability lies between $4.45\cdot10^{-11}$ and $7.49\cdot10^{-11}$. The fresh-column box product gives about $2.70\cdot10^{-8}$. A second lift of the same column accounts for the difference. At rank 1023, a separate calculation verifies enormous single-window expected counts on the old Part 50 witness boxes. Those boxes already have zero weight by Part 61. The calculation gives no new terminal radius.

## A finite-memory integral

Fix positive $g_i$, independent centered unit-uniform upper triangular coefficients, and open competitor balls. At column $j$ keep the triangular submatrix $H$ on the previous $h=\min(j,\beta-1)$ indices, in their projected GS coordinates. Append the fresh column with horizontal coordinates $g_l u_l$ for these indices and vertical coordinate $g_j$, obtaining $H'$. Let $C_j(H,u)$ indicate that every trailing principal submatrix of $H'$ has no vector shorter than its head with positive last integer coefficient. Define
$$
 (K_j f)(H)=\int_{[-1/2,1/2]^h} C_j(H,u) f(\operatorname{tail}_{\min(j+1,\beta-1)}H')\,du .
$$
Then $W=(K_0\cdots K_{n-1}1)(\varnothing)$. Every strict competitor has a unique last index, up to changing sign, and projecting at its start discards all older coordinates. This proves the identity, including at the truncated end windows. Each integral test is finite by backward enumeration inside the indicated ball. The state has up to $h(h-1)/2$ continuous parameters at fixed diagonal. On a geometric profile common rescaling removes the column index after initialization. Part 68's history-independent bound on $K_j1$ drops the distribution of the surviving state.

At width two set $r_i=g_{i+1}/g_i$ and $P(r)=[1-2\sqrt{(1-r^2)_+}]_+$. Exactly $W_2=\prod_iP(r_i)$. The nearest horizontal lift of last coefficient one gives this factor. When the factor is positive, last coefficients of magnitude at least two already exceed the head in height. The factors use independent coefficients. Hence an exact additive steepness penalty is $\sum_i-\log P(r_i)$, also a lower bound on $-\log W_\beta$ for every larger width. For a small positive log drop $s$, the cost is $2\sqrt{2s}+O(s)$. A single drop reaching $\log(2/\sqrt3)$ costs infinity. Splitting that drop equally over two steps gives finite cost at width two. Total positive drop alone therefore does not determine the decay.

## The exact width-three kernel

Take $g_i=r^i$, $\sqrt3/2<r\le1$, and set $a=\sqrt{1-r^2}$. In head-length units a triple has columns $(1,0,0),(s,r,0),(y,rv,r^2)$, with signed coefficients before reflection. Survival of the old pair requires $|s|\ge a$, and the new pair requires $|v|\ge a$. Fold both signs so that $s,v\in[a,1/2]$. The remaining coordinate $y$ is uniform on the unit circle. Only last coefficient one can compete because $2r^2>1$. The middle coefficient, after reflecting signs, can only be 0 or −1 since $\sqrt{1-r^4}/r<1$. Minimizing over the first integer excludes arcs of respective half-lengths
$$
 R(v)=\min(1/2,\sqrt{(1-r^4-r^2v^2)_+}),\qquad T(v)=R(1-v).
$$
Their centers have circle distance $s$. Reflection preserves the union length, justifying the sign fold even after conditioning on all previous tests. Write $L(s,v)$ for the uncovered length. With $D=[a,1/2]$,
$$
 Kf(s)=2\int_D L(s,v)f(v)\,dv,\qquad W_3=2\int_D K^{n-2}1(s)\,ds .
$$
For arbitrary positive lengths, first return zero if an adjacent ratio is at or below $\sqrt3/2$. Otherwise, in the triple with successive ratios $u,w$, replace $r^4$ by $u^2w^2$ and $r^2v^2$ by $u^2v^2$ in $R$. Use the old and new state domains $[\sqrt{(1-u^2)_+},1/2]$ and $[\sqrt{(1-w^2)_+},1/2]$ respectively. The same two lifts exhaust the possibilities because $2uw>1$ and $1-u^2w^2<u^2$. Composing these varying kernels gives the exact joint integral for any profile at width three.

For geometric profiles, the Part 68 box keeps only the arc at zero, so its product is $P(r)B^{n-2}$, where $B=2\int_D(1-2R(v))\,dv$. The doubled-point correction vanishes by height. Whenever $1-r^4\le r^2/4$, the second arc is empty everywhere and the box formula is **exact in every dimension**. The exponential factor per additional column is then exactly $B$, including for the first three ratios below.

| $r$ | Exact width two, rounded | Width three, certified enclosure at $n=8$ | Part 68 box, rounded | Part 59 exponential, rounded |
|---:|---:|---:|---:|---:|
| .99 | .09824 | [.07883, .08155] | .08072 | .13877 |
| .97 | .009451 | [.003771, .003964] | .003864 | .03326 |
| .94 | .0003263 | [7.027e−6, 7.917e−6] | 7.572e−6 | .006227 |
| .92 | 2.205e−5 | [4.452e−11, 7.487e−11] | 2.701e−8 | .002723 |
| .90 | 5.698e−7 | 0 | 2.302e−11 | .002226 |

The last column uses the fixed-profile Part 59 weight $\exp[-2a-6\max(2a,\pi\min(1/4,1-r^4)/r)]$. The comparisons are pointwise, before integration against the Haar density. The box column can be evaluated by ordinary one-dimensional quadrature of the displayed $B$. At .92 the joint probability is over 300 times smaller. The row bounds in the certificate also imply $.017\le\rho(K)\le.032$ there. Indeed the upper matrix bounds the sup norm on surviving bins, while the lower matrix restricted to wholly surviving bins sends the constant one to at least .017 times one there. Iteration proves both bounds and sandwiches the per-column asymptotic decay factors (liminf and limsup) of the integral in the same interval. At .90 the upper row sums on surviving bins vanish, so even one triple has zero pass probability. These widths measure exact local geometry without assigning a small-width value to the asymptotic GSA slope.

### Reproducible integration certificate

The script uses exact integer lengths and rational probabilities. A state cell has width $1/M$. To enclose the two arcs, use monotonicity of each radius in its argument, round the radii outwards or inwards, and enlarge or erode the moving-center arc by one grid unit. An arc of radius zero has zero measure. The intersection length of arcs of radii $R,T\le M/2$ is the sum of the line intersection lengths at separations $s,M-s$. Thus each matrix bounds the true kernel throughout each cell. Folding gives bin mass $1/(M/2)$. Integer matrix products integrate the bounds through the entire chain. Shrinking the mesh gives the exact integral by dominated convergence since the adjacent cutoff has measure-zero boundary and the uncovered length is continuous. The fixed mesh in the script suffices for the table.

```python
from math import isqrt, exp, pi
import numpy as np

def calc(p,q,n=8,M=1024):
    # g_i=(p/q)^i. All circle lengths below use units of 1/M.
    assert M==1024 and q==100 and n>=2  # int64 cell geometry bounds
    h=M//2
    assert 3*q*q < 4*p*p and p<=q and 4*p**4>=q**4
    assert q**4-p**4 < p*p*q*q  # only horizontal integers 0,-1 for v>=0
    s=np.arange(h)[:,None]
    v=np.arange(h)
    def rad(t,up):
        z=max(0,M*M*(q**4-p**4)-p*p*q*q*int(t)**2)
        k=isqrt(z)//(q*q)
        return min(h,k+int(up and (k*q*q)**2<z))
    def valid(t):
        return q*q*t*t >= M*M*(q*q-p*p)
    def part(upper):
        # Upper survival uses inner forbidden arcs.
        R=np.array([rad(t+int(upper),not upper) for t in v])
        T=np.array([rad(M-t-int(not upper),not upper) for t in v])
        # Arc 2 center s..s+1. Erode/dilate by one unit about s.
        T=np.maximum(0,T-1) if upper else np.minimum(h,T+1)
        def intersect(d):
            return np.maximum(0,np.minimum(2*np.minimum(R,T),R+T-d))
        length=M-2*(R+T)+intersect(s)+intersect(M-s)
        if p==92 and not upper and n==8:
            from fractions import Fraction
            eligible=valid(v)
            # Upper rounded R gives a lower bound for the Part 68 box pass.
            box=Fraction(int(sum(eligible)),h)*Fraction(
                int(sum((M-2*R)*eligible)),M*h)**6
            assert box>Fraction(225,10**10)
        A=length*valid(v+int(upper))
        mask=valid(v+int(upper))
        row=A.sum(1)[mask]
        if p==92:
            assert row.max()*1000 < 32*M*h if upper else row.min()*1000 > 17*M*h
        if p==90 and upper:
            assert row.max()==0
        f=mask.astype(object)
        den=h
        for j in range(n-2):
            f=f @ A.astype(object)
            den*=M*h
        return int(sum(f)),den
    a,b=part(False); c,d=part(True)
    from fractions import Fraction
    return Fraction(a,b),Fraction(c,d)
if __name__=='__main__':
    for p in [99,97,94,92,90]:
        a,b=calc(p,100)
        r=p/100
        P=1-2*(1-r*r)**.5
        hit=max(1-P,pi*min(.25,1-r**4)/r)
        print(p,float(a),float(b),P**7,exp(-(1-P)-6*hit))
```

## Disjoint windows and the 34,000-log-unit benchmark

For intervals with disjoint sets of internal coefficients, single-block head-test events are independent. In particular one may choose disjoint index intervals of lengths at most the width. With a proved block cost $c(i,j)\le-\log\Pr(\mathrm{head\ passes\ on\ }i,\ldots,j-1)$, the best resulting cost satisfies $D_0=0$ and $D_j=\max(D_{j-1},\max_{i} [D_i+c(i,j)])$, with $j-\beta\le i<j$, $i\ge0$. Then $W\le e^{-D_n}$. The same optimization with mean counts is a diagnostic until a void-probability inequality supplies the costs.

For a block starting at $i$, use only sign pairs ending at $j=i+t$ with last coefficient one. The Part 57 torus unfolding gives their exact mean
$$
 U=V_t (1-e^{2(x_j-x_i)})_+^{t/2}\exp(t x_i-\textstyle\sum_{l=i}^{j-1}x_l).
$$
On **every profile** of the respective Part 50 witness boxes, a single interval already gives the following lower bounds. Singleton families qualify as disjoint, and extending an interval to a full window with the same start preserves the competitors.

| Width | Start | $t$ | Certified lower bound on $\log U$ |
|---:|---:|---:|---:|
|406|26|405|143|
|506|7|505|175|
|647|377|645|223|
|800|224|798|275|

Thus even $e^{143}\gg34000$ on the original witnesses. Part 61 already rules out their entire support by packing. Conversely, a uniform mean-count lower bound on **every** bad profile is impossible. Take logs constant and sufficiently negative through $k=n-\beta$, then constant and positive afterwards to restore determinant one. No projected vector can be strictly shorter than its head because its last height is at least the head. Strictly increasing perturbations give the same conclusion on an open bad set. These examples make no claim of large Haar intensity. A successful integral needs suppression on the profiles with substantial *remaining* intensity. Neither a Haar-lattice Rogers estimate nor the fixed-diagonal first moment gives a conditional exponential void bound there. The witness calculation and the width-three rates do not close the rank-1023 gap.

The second certificate imports the constants and their rounding checks from Part 50. The box permits log perturbations of at most $n/M$ after recentering, which the calculation charges on both sides of every difference.

```python
from pathlib import Path
src=Path('docs/research/wall1_volume_method.md').read_text().split('```python\n')[1]
exec(src.split('def shape')[0])
for b,dent,i,d in [(406,63281250,26,406),(506,55312500,7,506),(647,50703125,377,646),(800,45390625,224,799)]:
 S=[0]*(n+1)
 for l in reversed(range(n-1)):
    v=min((C[t]-10000*t+S[l+1]-S[l+t])//(t-1) for t in range(2,min(b,n-l)+1))
    S[l]=S[l+1]+v-(dent-3000000 if l==n-b else 0)
 # Centering cancels. Every perturbed log differs by at most n/M.
 x=[I.mpf(S[l]-S[l+1])/M for l in range(n)]
 e=I.mpf(n)/M
 j=i+d-1
 t=d-1
 z=t/2*I.ln(I.pi)-I.loggamma(1+I.mpf(t)/2)
 z+=I.mpf(t)/2*I.ln(1-I.exp(2*(x[j]-x[i]+2*e)))
 z+=t*(x[i]-2*e)-sum(x[i:j])
 floor={406:143,506:175,647:223,800:275}[b]
 assert z>floor
 print(b,floor)
```

## Related probability laws

Hanrot and Stehlé give the closest construction. They prescribe GS lengths and randomize lift coefficients to establish existence of HKZ and BKZ bases with specified profiles. Their short-vector probability estimates give sufficient conditions for existence. The upper tail of joint *acceptance* on high-intensity profiles requires the other direction. [Hanrot–Stehlé, Worst-Case Hermite–Korkine–Zolotarev Reduced Lattice Bases](https://arxiv.org/abs/0801.3331)

Akhavi, Marckert and Rouault derive limit laws for reduction levels under spherical random-input models with random GS lengths. Nguyen and Stehlé investigate the output quality of LLL experimentally. Neither supplies the conditional BKZ kernel used here. For ordinary Lovász LLL with parameter $\delta$ in the size-reduced product chart, direct independence gives the exact probability by replacing $1-r_i^2$ by $\delta-r_i^2$ in the width-two formula. [Akhavi–Marckert–Rouault](https://www.numdam.org/articles/10.1051/ps%3A2008012/) · [Nguyen–Stehlé, corrected version](https://perso.ens-lyon.fr/damien.stehle/downloads/average-corrected.pdf)
