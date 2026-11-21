# A finite graph-lattice certificate for the Part 88 twin test

Use physical Euclidean covolumes and put $N=m+n=1023$, $m=511$, $n=512$, $q=3329$, $u=q^{m/N}$. All radii below use Part 88's exact terminal oracle and 1% twin slack. The probability is per width and simultaneous over qualifying bases.

| Horizontal width | Extension rank | Physical radius (rounded down) | Covolume-one radius | Part 88 Haar radius | Fraction of Haar bound |
|---:|---:|---:|---:|---:|---:|
| 406 | 618 | 2.96377411 | 0.05157150 | 0.12531282 | 41.15% |
| 506 | 518 | 6.83703605 | 0.11896865 | 0.36188705 | 32.87% |

The normalized shortfalls relative to the displayed Haar bounds are 0.07374132 and 0.24291840. These compare sufficient radii. The actual finite-ensemble quantiles could be higher. The losses include discarding the projection-rank restriction in the height count, summing over all coordinate charts, and bounding every translated row sum uniformly. No GSA or Haar approximation enters the finite certificate. Both physical radii fall below even the Part 58 low-height cutoffs (54.66 and 60.40 in its width convention). The planted lifting step, prefix control and the dimension-647 frontier identified in the repository remain open to improvement. [Width conventions](wall1_selfdual_qary.md) · [Wall 1 frontier](../PROOF_GAP.md)

## First moment

For each rational $r$-plane take its ambient saturation $S$ with basis $(E;F)$ and height $h=\det S$. Its unique primitive representative in the graph lattice is $P=S\cap L_0$. Write $t=\operatorname{rank}_q F$, $s=r-t$. The reduction of a basis of $S$ is independent by primitivity. Thus $E(\ker F)$ has dimension $s$, and on a complement the images under $AF$ are independent uniform columns. Modulo $E(\ker F)$ the remaining rank $j$ has the law of a uniform $(m-s)\times t$ matrix. Consequently $\det P=hq^{s+j}$. With $C_t(T)$ counting these planes of height at most $T$ and secret projection rank $t$, the exact mean is
$$
\sum_{t,j} C_t(X/q^{s+j})q^{-(m-s)t}
\prod_{i=0}^{j-1}\frac{(q^{m-s}-q^i)(q^t-q^i)}{q^j-q^i}.
$$
Here $\max(0,r-m)\le t\le\min(r,n)$ and $0\le j\le\min(m-s,t)$. The product counts factorizations of rank $j$ modulo changes of intermediate basis. [AB](wall1_selfdual_qary.md) · [Part 54](wall1_qary_basis_count.md)

Put $z=N-r$ and $d=m-s-j$. The rank probability is at most $2q^{-d(r-m+d)}$, since the reciprocal denominator correction is bounded by $1/\prod_{i\ge1}(1-q^{-i})<2$ (the product is at least $1-1/(q-1)$). We have $0\le d\le m-r+t\le z$. The exponent identity
$$
N(m-d)+d(r-m+d)-mr=(z-d)(m-d)\ge0
$$
is why even the deepest possible defect is covered. Typical full rank alone would give a different estimate.

## Finite height bound

The following argument gives all constants directly. For background on asymptotic Grassmannian counts see [Kim](https://arxiv.org/abs/1908.01245). For $T\ge1$ we prove
$$
\sum_t C_t(T)\le K(1+\log T)T^N,\quad
K=\binom Nr 2^r B^z,\qquad B=\sum_{i=0}^r\binom ri
\frac{\pi^{i/2}\Gamma((r+1-i)/2)}{\Gamma((r+1)/2)} .
$$
Below one the count vanishes by integrality of squared height.

Choose $r$ coordinate axes onto which the plane projects bijectively over the reals. The projection of $S$ is an index-$D$ lattice $H$ in the coordinate $\mathbb Z^r$. The plane is the graph of $z$ rows in $H^*$, and its height is $D\sqrt{\det G_z}$, where $G_l=I+\sum_{i\le l}v_iv_i^t$ for graph rows written as columns $v_i$. In particular $D\le T$. Overcount by allowing every row in $H^*$, including choices whose graph has a larger integral projection.

For $G\succeq I$, $p\ge r+1$, and any coset $w+\mathbb Z^r$,
$$
\sum_v(1+v^tG^{-1}v)^{-p/2}\le \sqrt{\det G}\, B .
$$
Indeed for the Gaussian $\exp(-a v^t G^{-1}v)$, Poisson summation bounds its translated sum by $\sqrt{\det G}$ times the standard unshifted Gaussian sum at the same $a>0$. On the Fourier side drop phases and use $h^tGh\ge\|h\|^2$. Integrate with Gamma weight $a^{p/2-1}e^{-a}/\Gamma(p/2)$. The resulting standard sum is largest at $p=r+1$. Group its points by nonzero coordinates and signs. In the positive orthant, integrating over the unit box immediately below each positive integer point upper bounds its summand by coordinatewise monotonicity. Summing signs gives the full-space radial integral in each dimension $i$, equal to the gamma ratio including the displayed power of $\pi$ (by the same Gaussian mixture).

Charge each graph by $(T/D)^N(\det G_z)^{-N/2}$, which is at least one on the cap. Sum rows backwards. The matrix determinant lemma and the coset bound give a factor $DB$ at each step ($[H^*:\mathbb Z^r]=D$) and decrease the exponent parameter $p$ by one, from $N$ down to $r+1$ on the final row. The remaining index sum is $\sum_{[\mathbb Z^r:H]=D\le T}D^{-r}$, summing over $H$. In triangular Hermite normal form the diagonal entries $a_i$ have product $D$ and, ordering the diagonals appropriately, multiplicity $\prod_i a_i^{i-1}$. Thus the last diagonal gives a harmonic sum at most $1+\log T$ and the others give at most $\prod_{j=2}^r\zeta(j)\le2^r$. Including all charts proves the bound.

In particular for $1\le X\le q^m$ the expected count is at most
$$
2(n+1)^2 K(1+m\log q)\,(X/q^{mr/N})^N .
$$
This uses the total height bound separately in every stratum and at most $(n+1)^2$ terms. For larger $X$ replace $m\log q$ by $\log X$.

## Conversion and numerical check

With $k=N-\beta$, $r=k+1$, Part 88 gives $\det P\le M_0 g^r$ for the primitive extension of a passing prefix with terminal head $g$. In its notation $\log M_0/r=k(\log h+\log(1.01)/(k-1))$. We use the same certified upper cap for $\log h$. Thus a mean below 0.01 at $X=M_0\rho^r$ excludes every head below $\rho$ with probability greater than 0.99. The exact terminal call identifies the projected minimum with that head. [Part 88](wall1_li_walter.md)

Run this block from the repository root. The integers for the two Hermite caps reproduce the Part 86 setup. The sum for $B$ uses the gamma recurrence two dimensions at a time. The script targets 0.009 before rounding down and checks the physical cap and the final strict mean inequality.

```python
from pathlib import Path
source = Path('docs/research/wall1_dual_pinning.md').read_text()
exec(source.split('\n```python\n')[1].split('def ceildiv')[0])
N, m, q = 1023, 511, 3329
logu = m*I.ln(q)/N
for b, cap in [(406,776598654340), (506,1020115234016)]:
    assert C[b] == cap and M == 10**9
    k = N-b
    r, z = k+1, b-1
    f = [I.mpf(1), I.sqrt(I.pi)*I.gamma(I.mpf(r)/2)
         /I.gamma(I.mpf(r+1)/2)]
    for i in range(2,r+1):
        f.append(f[i-2]*2*I.pi/(r+1-i))
    B = sum(comb(r,i)*v for i,v in enumerate(f))
    L = (I.ln(2*513**2*comb(N,r))+r*I.ln(2)+z*I.ln(B)
         +I.ln(1+m*I.ln(q)))
    ell = k*(I.mpf(cap)/(M*b*(b-1))+I.ln(I.mpf('1.01'))/(k-1))
    R = I.exp((I.ln(I.mpf('.009'))-L)/(N*r)-ell)
    a = int((10**8*R).a)
    R = I.mpf(a)/10**8
    logX = r*(ell+I.ln(R)+logu)
    assert 0 < logX and logX < m*I.ln(q)
    assert L+N*r*(ell+I.ln(R)) < -I.ln(100)
    print(b, a, int((10**8*R*I.exp(logu)).a))
```
