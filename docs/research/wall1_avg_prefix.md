# Average prefix determinants and the Rankin quotient

For the full horizontal graph lattice of rank 1023, the proved 99% Rankin width remains **1020** for the comparison with $\sqrt{6b}$. Here $b$ counts horizontal dimensions. Even granting the GSA prefix determinant exactly, the existing joint plane-event numerator first passes at **1018** among widths $40\le b\le1023$. There is a structural obstruction on Haar lattices at proportional prefix rank.

## The exact uniform denominator on Haar lattices

Fix $0<x<1$. Take $j=\lfloor xn\rfloor$, except that at $x=1/2$ take $j=\lfloor(n-1)/2\rfloor$. Put $k=j-1$. For a unimodular lattice define $M_{k,b}$ as the supremum of the rank-$k$ prefix covolume among all exact BKZ-$b$ bases. With Haar probability $1-o(1)$, simultaneously for every $2\le b\le n$,
$$
 \log(\mu_{k+1}/M_{k,b})\le
 -\left(\tfrac{1-x}{2}[-\log(1-x)-x]+o(1)\right)n\log n .
$$
The coefficient is positive throughout the open interval. At half rank it is $(\log 2-1/2)/4>0.0482$.

**Proof.** An HKZ basis exists on every lattice and satisfies the exact shortest-vector condition on every truncated window. The head belongs to the window and is shortest even in the full suffix. Consequently $M_{k,b}$ dominates its prefix determinant for every width on the same input. Proposition 3 gives a log determinant of $(p(x)+o(1))n\log n$ there, with $p(x)=-(1-x)\log(1-x)/2$. Lemma 5 of the same paper, applied with the unrestricted block property, gives a primitive rank-$j$ witness of log determinant at most $[j(n-j)/(2n)]\log n+O(n)$ with probability $1-o(1)$. Intersect the two events and subtract. The witnesses may belong to different flags, precisely as allowed in the proposed quotient. [Laarhoven, Proposition 3 and Lemma 5](https://arxiv.org/html/2610.15265v1)

On the success event of any cutoff covering every basis, substituting that cutoff can only decrease the quotient. Rescaling to determinant $D$ multiplies the quotient by $D^{1/n}$, so the obstruction persists for polynomially bounded root determinant against any inverse-polynomial benchmark. The proof supplies no explicit crossover dimension or graph-congruence witness. Near-full widths with bounded $k$ remain open. The actual projected minimum can be much larger than the quotient.

## A finite Haar test accounting for selection

Work in determinant-one units. Let $k=n-b>0$, let $X$ be the Part 6 cutoff, and take $P_i$ from Part 48 at width $b$. Set $a=\exp(-\sum_{h=1}^k P_h/k)$. If a reduced prefix has determinant $s$, multiplication of $g_i\le g_k\exp(P_{k-i})$ for $0\le i<k$ gives $g_k\ge a s^{1/k}$. Its terminal quotient has determinant $1/s$ and minimum $g_k$. Thus its normalized quotient has no nonzero point in the open ball of radius $a s^{1/k+1/b}$.

Write $H_b(u)$ for the Haar probability of such an empty ball. For $0<Y<X$,
$$
 \Pr(M_{k,b}>Y)\le n A(n,k)\int_Y^X s^{n-1}H_b(a s^{1/k+1/b})\,ds .
$$
Indeed, count all primitive rank-$k$ marks in this determinant interval satisfying the necessary hole test. Under split averaging their intensity is $n A(n,k)s^{n-1}ds$, with the Part 6 normalization, and their normalized quotients have Haar shape. Apply Markov. For $b\ge3$, Part 46 gives mean and variance both $h=V_bu^b/(2\zeta(b))$ for the primitive pair count in the open ball ($V_b$ is unit ball volume). Cantelli gives $H_b(u)\le1/(1+h)$. This explicit sufficient test pays the full mark intensity even for a single profile bin. [Split averaging, Lemma 2](https://arxiv.org/html/2610.15265v1) · [Rogers pair count](wall1_haar_prefix_law.md) · [Propagation](wall1_null_terminal.md)

A lower bound on block minima alone points the wrong way for reducing the prefix upper envelope. The Hermite constraints bound the block head from above. One needs to exclude large normalized heads or exploit joint constraints on overlapping windows. A prefix can be intrinsically HKZ while its admissibility as part of a reduced ambient basis is undecided. The pencil examples in Parts 41–43 concern the planted setting. For the graph ensemble a mark has an arithmetic weight depending on modular rank and its quotient is discrete. Using $H_b$ in this ensemble requires a separate comparison. [Wall 1, Parts 41–48](../PROOF_GAP.md) · [Graph incidence weights](wall1_rankin_route.md)

## Finite denominator accuracy required

Let $D=3329^{511}$, $n=1023$, $k=n-b$ and $j=k+1$. Use $m_j$ for the log Rankin lower bound on the single joint event $\lambda_1>442$, $\mu_2>193000$, of failure probability below 0.000838. Take the larger of the line and plane bounds on this event from the [Rankin note](wall1_rankin_route.md). Let $G_k=D^{k/n}\delta_b^{kb}$ be the GSA prefix covolume with the [Part 6 convention](wall1_prefix.md). The signed error budget is $E=(m_j-\log\sqrt{6b}-\log G_k)/\log 2$. A theorem bounding all prefixes by $G_k2^e$ with failure at most 0.009162 suffices if $e<E$, by a union bound. Negative entries require a denominator below GSA for this numerator.

| Horizontal width | Prefix rank | Budget in bits |
|---:|---:|---:|
|506|517|[−1294.39, −1294.38]|
|1000|23|[−21.65, −21.64]|
|1017|6|[−0.180, −0.179]|
|1018|5|[0.593, 0.594]|
|1019|4|[1.208, 1.209]|
|1020|3|[1.749, 1.750]|

At 1018 the available slack is less than a factor of 1.51 in the whole determinant. An unspecified $o(n\log n)$ error cannot certify that inequality at $n=1023$. The direct GSA terminal crossing at 506 and the hypothetical GSA-denominator quotient use different numerators.

The following Python certificate uses outward interval arithmetic. The plane formula applies Hermite to the first two HKZ heads of a rank-$j$ witness. GSA is evaluated as a hypothesis only.

```python
from mpmath import iv as I
I.dps=45
n=1023
D=511*I.ln(3329)
def C(j):
    if j<=1:return I.mpf(0)
    if j<=8:
        a,d=[(4,3),(2,1),(4,1),(8,1),(64,3),(64,1),(256,1)][j-2]
        return I.ln(I.mpf(a)/d)/2
    return j*I.ln(2/I.pi)/2+I.loggamma(2+I.mpf(j)/2)
def bits(b):
    k=n-b
    j=k+1
    m=j*I.ln(442)-C(j)
    if j>=2:
        m=max(m,(j*I.ln(193000)-(j-2)*C(j)/(j-1)-j*C(j-1)/(j-1))/2)
    h=(I.ln(I.pi*b)/b+I.ln(b/(2*I.pi*I.exp(1))))/(2*(b-1))
    G=k*D/n+k*b*h
    return (m-I.ln(6*b)/2-G)/I.ln(2)

rows={506:('-1294.39','-1294.38'),1000:('-21.65','-21.64'),
      1017:('-.180','-.179'),1018:('.593','.594'),
      1019:('1.208','1.209'),1020:('1.749','1.750')}
for b,(lo,hi) in rows.items():
    assert I.mpf(lo)<bits(b)<I.mpf(hi)
for b in range(40,1024):
    assert bits(b)<0 if b<1018 else bits(b)>0
assert (I.ln(2)-I.mpf(1)/2)/4>I.mpf('.0482')
```

The missing result is a simultaneous graph-lattice upper quantile for reduced prefixes. Neither the Haar obstruction nor the marked first moment proves such a quantile at the tabulated cutoffs. The certified horizontal widths remain 1020 via the Rankin quotient and 1000 via direct propagation. A planted recovery probability also needs the height and lifting estimates of Part 47.

## Quantitative check of the Haar test

As a diagnostic, normalize the two q-ary target cutoffs to determinant-one units, $Y=\exp(m_j)/[\sqrt{6b}D^{k/n}]$, and use these numbers in the Haar test. At 1018 and 1019 even the slice $[Y,1.01Y]$ contributes more than $2^{532}$ and $2^{961}$ respectively to the **Cantelli upper bound** on the marked mean. This rules out that particular numerical relaxation at both cutoffs. It gives no lower bound on the true bad-event probability. Indeed $a\le1$, $\zeta(b)>1$, and throughout the slice the Cantelli denominator is at most $1+V_b(1.01Y)^{1+b/k}/2$. Integrate the intensity exactly over the slice and bound each zeta ratio in $A(n,k)$ from below by $1/2$ (with the Part 6 convention at index one).

Run this continuation from the repository root after the first code block. It reuses the interval lower endpoint for the normalized Part 6 envelope from the Rankin note to check that the slice lies below $X$.

```python
from pathlib import Path
src=Path('docs/research/wall1_rankin_route.md').read_text().split(chr(96)*3+'python\n')[1]
env={}
exec(src[:src.index('def run(')],env)
sums,M=env['sums'],env['M']
ln=I.ln
def V(i):return i*ln(I.pi)/2-I.loggamma(1+I.mpf(i)/2)
for b in (1018,1019):
 k=n-b; j=k+1
 m=max(j*ln(442)-C(j),(j*ln(193000)-(j-2)*C(j)/(j-1)-j*C(j-1)/(j-1))/2)
 y=m-ln(6*b)/2-k*D/n
 sl,su=sums(n,b,False),sums(n,b,True)
 x=I.mpf(int(sl[n])*(n-k)-int(su[n-k])*n)/(n*M)
 A=-ln(n)
 for i in range(1,k+1):
    A+=ln(I.mpf(n-i+1)/i)+V(n-i+1)-V(i)
    # zeta(i)>=1 and zeta(n-i+1)<2
    A-=ln(2)
 # slice [Y,1.01Y], a<=1
 t=y+ln(I.mpf('1.01'))
 assert x>t
 h=I.exp(V(b)+(1+I.mpf(b)/k)*t)/2
 bound=(A+n*y+ln(I.mpf('1.01')**n-1)-ln(1+h))/ln(2)
 assert bound>({1018:532,1019:961}[b])
```
