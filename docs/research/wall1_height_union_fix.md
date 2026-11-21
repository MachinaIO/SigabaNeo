# Higher heights from the projected minimum alone: the corrected union bound

**Result.** With the inequality direction repaired (a *lower* norm cutoff inside the height-$k$ event), the fixed-direction union bound is valid but never beats elementary geometry, and the best sufficient condition on $\lambda_1(H)$ alone that this toolkit yields is the per-height quadratic threshold of [Part 47](wall1_decoupled.md) at a 99% norm quantile: $\lambda_1(H)>T(R_+)\approx R_+^2$, i.e. $c(\beta)\approx 1.5\sqrt\beta$ (37 to 54 on the requested widths, $\lambda_1\gtrsim 742$ to $1703$). The certified null minima (79 to 89 at widths 1000 to 1020, 443 at the empty prefix) are far below this, and so is the GSA prediction at every width. **No width is certified.** The obstruction is the large heights $3\le k\le\|v\|$, where any count of lattice points that uses only $\lambda_1(H)$ and the rank is too large for a fixed-direction tail.

Setting as in [Part 47](wall1_decoupled.md) and [the fixed-height note](wall1_random_plant_heights.md): conditional on the design and coins, $H$ is a fixed lattice of rank $d=\beta-1$ in the horizontal subspace $S$, $P$ is the orthogonal projector onto $S$, $Y\in\mathbb Z^N$ ($N\le1024$) has iid CBD(3) coordinates, $v_h=PY$, $v=(v_h,1)$ and $\|v\|^2=1+\|PY\|^2$. $F$ is the event that some $(k,x)\in\mathbb Z\times H$ other than $(0,0),(\pm1,0)$ has $\|x+kv\|\le\|v\|$. Since $(k,x)\mapsto(-k,-x)$ preserves the event, take $k\ge0$. Then $F$ splits into: $k=0$, $x\neq0$, $\|x\|\le\|v\|$; $k=1$, $x\ne0$, $\|x\|^2\le-2\langle x,v_h\rangle$; and $k\ge2$, $\|x\|^2+2k\langle x,v_h\rangle+(k^2-1)\|v\|^2\le0$. The height coordinate forces $k\le\|v\|$, and $x=0$ is impossible for $k\ge2$.

## Lemmas (all proved)

**L1 (sub-Gaussian proxy 3/2).** A CBD(3) coordinate is half a sum of six fair signs, so $\mathbb E e^{sY_j}=\cosh(s/2)^6\le e^{3s^2/4}=e^{\sigma^2s^2/2}$ with $\sigma^2=3/2$ (from $\log\cosh z\le z^2/2$). For $x\in S\setminus0$, $\langle x,PY\rangle=\sum_j x_jY_j$, hence $\Pr(\langle x,PY\rangle\le-a)\le e^{-a^2/(3\|x\|^2)}$. This is the fixed-direction theorem of the earlier note; the constant 3 in the denominator is $2\sigma^2$.

**L2 (upper tail, earlier note).** $\Pr(\|PY\|^2\ge h)\le e^{-th}(1-3t)^{-d/2}$ for $0<t<1/3$.

**L3 (lower tail, new).** For $t>0$,
$$
\Pr(\|PY\|^2\le h)\le e^{th}\Big[(1+3t)^{-d/2}+N e^{-\pi^2/(4t)}\Big].
$$
*Proof.* Let $G$ be a standard Gaussian on $S$, $G_j=\langle G,e_j\rangle\sim N(0,P_{jj})$, so $\sum_jG_j^2=\|G\|^2$. Then $e^{-t\|PY\|^2}=\mathbb E_G\cos(\sqrt{2t}\langle G,Y\rangle)$, and averaging over $Y$ first gives $\mathbb E e^{-t\|PY\|^2}=\mathbb E_G\prod_j\cos^6(\sqrt{2t}G_j/2)$, a product of nonnegative factors. On the event that every $|\sqrt{2t}G_j/2|<\pi/2$, $\log\cos u\le-u^2/2$ bounds the product by $e^{-(3t/2)\|G\|^2}$, whose mean is $(1+3t)^{-d/2}$. Off that event bound the product by 1. Its probability is at most $\sum_j 2\bar\Phi(\pi/\sqrt{2tP_{jj}})\le Ne^{-\pi^2/(4t)}$ since $P_{jj}\le1$. Markov's inequality finishes the proof. $\square$
Unlike the bounded-differences bound of Part 47 this does not depend on the orientation of $P$.

**L4 (corrected height-$k$ inclusion).** Let $R_-\le\|v\|$. For $k\ge2$, $(k,x)\in F$ implies $\langle x,v_h\rangle\le-a_k(x)$ with $a_k(x)=(\|x\|^2+(k^2-1)R_-^2)/(2k)$, because $(k^2-1)>0$. By L1, $\Pr(\{(k,x)\in F\}\cap\{\|v\|\ge R_-\})\le e^{-a_k(x)^2/(3\|x\|^2)}$. For $k=1$ the same argument gives $e^{-\|x\|^2/12}$. This is the inclusion the earlier note lacked.

**L5 (deterministic geometry).** Put $R=\|v\|$. If $(k,x)\in F$ with $x\ne0$, then $\|x\|\le R$ for $k=0$, $\|x\|\le 2\sqrt{R^2-1}$ for $k=1$, and for $2\le k\le R$
$$
\|x\|\le\|x+kv_h\|+k\|v_h\|\le\sqrt{R^2-k^2}+k\sqrt{R^2-1}.
$$
Let $T(R)=\max_{2\le k\le R}\big(\sqrt{R^2-k^2}+k\sqrt{R^2-1}\big)$, nondecreasing in $R$ and at least $\max(R,2\sqrt{R^2-1})$ when $R\ge2$. One also has $T(R)\le R^2$ by Cauchy–Schwarz (Part 47).

## Theorem

Let $h_+$ satisfy $\inf_t e^{-th_+}(1-3t)^{-d/2}\le0.01$ and put $R_+^2=1+h_+$. **If $\lambda_1(H)>T(R_+)$ then $\Pr_Y[F]\le0.01$.** Indeed on $\{\|v\|\le R_+\}$ every candidate in $F$ would have $\|x\|\le T(\|v\|)\le T(R_+)<\lambda_1(H)$, so $F$ is contained in $\{\|v\|>R_+\}$. Ties are covered, since $F$ uses $\le$ and the hypothesis is strict.

Writing $\lambda_1(H)\ge c(\beta)\sqrt\beta$, the interval certificate gives the following ($d=\beta-1$, values rounded; $h_-$ is the L3 lower 99% quantile, $R_-^2=1+h_-$, reported for use elsewhere):

| $\beta$ | $d$ | $h_+$ | $R_+$ | $R_-$ | required $\lambda_1(H)>T(R_+)$ | $c(\beta)$ | GSA terminal length at horizontal width $d$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 406 | 405 | 747 | 27.350 | 21.909 | 742.31 | 36.84 | 24.73 |
| 506 | 505 | 912 | 30.216 | 24.799 | 909.59 | 40.44 | 54.82 |
| 647 | 646 | 1142 | 33.808 | 28.425 | 1122.54 | 44.13 | 122.54 |
| 800 | 799 | 1390 | 37.296 | 31.922 | 1384.16 | 48.94 | 229.94 |
| 1000 | 999 | 1712 | 41.388 | 36.028 | 1702.09 | 53.82 | 420.19 |
| 1001 | 1000 | 1713 | 41.400 | 36.042 | 1702.67 | 53.82 | 421.27 |
| 1021 | 1020 | 1745 | 41.785 | 36.428 | 1720.77 | 53.85 | 443.20 |
| 1024 | 1023 | 1750 | 41.845 | 36.497 | 1723.52 | 53.86 | 446.53 |

Asymptotically $c(\beta)\sim1.5\sqrt\beta$, not a constant. [Parts 48 and 49](wall1_rankin_route.md) count width as the horizontal rank, so their width $b$ corresponds to $d=b$ here. The best certified lower bounds there are 80.2109 at $b=1000$, 88.984 at $b=1020$ and 443.0664 at the empty prefix $b=1023$, against requirements 1702.7, 1720.8 and 1723.5. Even the GSA heuristic, the most optimistic profile in [Part 48](wall1_null_terminal.md), stays below $1+1.5(b-1)$ at every width $40\le b\le1023$. Part 49 already found that the quadratic benchmark is not certifiable at any width.

## Why the union over $(k,x)$ cannot do better with $\lambda_1(H)$ alone

The only information about $H$ is $\lambda_1(H)=\lambda$ and the rank, so the count of $x\in H$ with $0<\|x\|\le r$ is controlled by the packing envelope $M(r)=(1+2r/\lambda)^d-1$. Any union estimate built from L4 has to allow a configuration that meets this envelope. Fix $k\ge1$ and $\lambda\le(k+1)R_+$, and look only at the outermost relevant shell $r=(k+1)R_+$. There $a_k\le(k+1)R_+^2$, so the L4 exponent is at most $R_+^2/3$, while $M(r)\ge3^d-1$. Since $d\log3-R_+^2/3>\log100$ at every tabulated width (asserted in the script; roughly $1.10d$ against $0.57d$), the estimate for height $k$ exceeds 0.01. Heights up to $\lfloor\|v\|\rfloor\approx R$ belong to $F$. So the union route certifies height $k$ only once $\lambda>(k+1)R_+$, where L5 has already removed every candidate. Its best output is therefore at least $(\lfloor R_+\rfloor+1)R_+>T(R_+)$, and the Theorem dominates it. A floating-point scan over all shells at $d=999$ agrees: for each $1\le k\le41$ the first $\lambda$ that passes lies 0.2% to 2% above the L5 threshold.

The same comparison holds at small heights. At $k=1$ the union needs $\lambda^2\ge12(d\log3+\log100)$, about 115 at $d=999$, against the deterministic $2\sqrt{R_+^2-1}\approx82.8$. At $k=2$ it needs about 205 against $3R_+\approx124$. The underlying mismatch: the fixed-direction tail is at most $e^{-\Theta(R^2)}=e^{-\Theta(d)}$, while a lattice with minimum $\lambda=c\sqrt d$ can have $e^{\Theta(d\log k)}$ points in the radius-$(k+1)R$ ball. Refined kissing or density bounds (Kabatiansky–Levenshtein) change constants but not the growth in $k$.

**What would be needed.** For $k\ge3$ the event says $kv_h\in H+B(\|v\|)$. A useful bound must show that $kv_h \bmod H$ is spread out (heuristically, probability about $\mathrm{vol}\,B(R)/\det H$). That requires anti-concentration or smoothing information about $H$, such as a lower bound on $\det H$ or on the dual minimum, which $\lambda_1(H)$ does not provide. Note also $H\subset PZ^N\ni v_h$, so the event is about the class of $kY$ in the finite group $\mathbb Z^N/(L_0+W\cap\mathbb Z^N)$. Heights $0$ and $1$ are fine under a linear threshold: with $\lambda_1(H)>2\sqrt{R_+^2-1}$ (82.8 at $d=999$, 83.5 at $d=1020$), the events $k\in\{0,\pm1\}$ are excluded on the 99% norm event. At $d=1020$ the Part 49 certificate of 88.984 clears this. So at width 1020, heights $0,\pm1$ are excluded with joint probability at least $1-0.000838-0.01$ (plane event plus norm tail; asserted below). At $d=1000$, 80.2109 is below 82.8, so not even heights $0,\pm1$ follow. Heights $\ge2$ remain open.

## Certificate

Python 3 with mpmath interval arithmetic. The optimizing tilts are chosen in floating point, and every bound is then evaluated in intervals.

```python
# Certificate for docs/research/wall1_height_union_fix.md (Python 3 + mpmath).
from mpmath import iv as I
import math
I.dps=40
N=1024  # number of CBD coordinates, at least m+n
def up(d,h):   # Pr(|PY|^2 >= h)
    t=I.mpf((1-1.5*d/h)/3); assert 0<t.a and (3*t).b<1
    return I.exp(-t*h)*(1-3*t)**(-I.mpf(d)/2)
def low(d,h):  # Pr(|PY|^2 <= h)
    import math
    f=lambda t: math.log(math.exp(t*h)*((1+3*t)**(-d/2)+N*math.exp(-math.pi**2/(4*t))))
    t=min((x/4000 for x in range(1,800)),key=f); t=I.mpf(t)
    return I.exp(t*h)*((1+3*t)**(-I.mpf(d)/2)+N*I.exp(-I.pi**2/(4*t)))
def T(R2):
    best=I.mpf(0)
    for k in range(2,math.floor(float(I.sqrt(R2).b))+1):
        s=R2-k*k
        v=I.sqrt(I.mpf([max(0,s.a),s.b]))+k*I.sqrt(R2-1)
        best=I.mpf([max(best.a,v.a),max(best.b,v.b)])
    return best
def gsa(b,n=1023,r=511):
    ld=(I.ln(I.pi*b)/b+I.ln(b/(2*I.pi*I.exp(1))))/(2*(b-1))
    return I.exp(r*I.ln(3329)/n+(2*b-n-1)*ld)
rows={}
for d in [405,505,646,799,999,1000,1020,1023]:
    h=int(1.5*d)+2
    while up(d,h).b>0.01: h+=1
    assert up(d,h)<=I.mpf('0.01') and up(d,h-1).a>I.mpf('0.01')
    hl=int(1.5*d)-2
    while low(d,hl).b>0.01: hl-=1
    R2=1+I.mpf(h); lam=T(R2)
    # union obstruction: even the single outermost shell r=(k+1)R+ defeats the packing count
    assert (I.mpf(d)*I.ln(3)-R2/3-I.ln(100)).a>0
    rows[d]=lam
    print(d,d+1,h,I.nstr(I.sqrt(R2),7),hl,I.nstr(I.sqrt(1+I.mpf(hl)),7),
          I.nstr(lam,9),I.nstr(lam/I.sqrt(d+1),5),I.nstr(gsa(d),5))
# comparison with certified null-lattice lower bounds (Parts 48-49)
for d,cert in [(1000,"80.2109"),(1020,"88.984"),(1022+1,"443.0664")]:
    assert I.mpf(cert)<rows[d]
assert all((gsa(b)<1+1.5*(b-1)) for b in range(40,1024))   # GSA never reaches even the quadratic mean
h1020=1745; assert 2*I.sqrt(I.mpf(h1020))<I.mpf('88.984') and up(1020,h1020)<=I.mpf('0.01')
assert 2*I.sqrt(I.mpf(1712))>I.mpf('80.2109')
print('ok')
```
