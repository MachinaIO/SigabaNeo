# A finite near-alias test for the positive heights

At horizontal ranks 505 and 506, exact integer aliases, including the zero frequency, contribute less than $1+2\cdot10^{-13}$ to the Gaussian-weighted dual sum below. Frequencies of physical length at least 10 contribute less than 1, even if their CBD factors are discarded. The remaining test is a **finite weighted count of nonintegral dual vectors of length below 10**. The determinant floors allow that count to be as large as $10^{48}$ and $10^{49}$ respectively. The available certificates do not bound it at those levels. Height one also requires a separate Voronoi estimate.

## Conditional first moment

Fix the graph design and the coins choosing its horizontal prefix, independently of the plant as in Part 47. Write $V$ for the remaining subspace, $\pi$ for projection onto it, $H=\pi L_0$, $y=\pi X$, and $R^2=1+\|y\|^2$. Identify $w\in H^*$ with its isometric lift $\pi^T w\in V\subset\mathbb R^{1023}$ whenever taking ambient coordinates. At height one exclude $h=0$ and count ties against the plant. At integer heights $2\le k\le R$ every $h\in H$ is eligible, including $h=-ky$ when this belongs to $H$. The failure condition is $\|h+ky\|^2\le R^2-k^2$. Negative heights follow by symmetry of the lattice. [Part 47](../PROOF_GAP.md) · [Exact threshold](wall1_threshold.md)

Take $a=1.9d$, $B=1+a$, $K=\lfloor\sqrt B\rfloor$, $t=d/(2B)$, and $c=\pi_{\rm circ}^2/t$, where $\pi_{\rm circ}$ denotes the circle constant (written $\pi$ in scalar expressions below). Let $G=(\det H)^{1/d}$ and $C_0=\sqrt{2\pi e B/d}$. With $v=2a/(3d)$ the probability of **any positive-height failure** is bounded by the smaller of 1 and
$$
e^{-d(v-1-\log v)/2}+S_1+
(C_0/G)^d\sum_{k=2}^K e^{-tk^2}F_k,\quad
S_1=\sum_{0\ne h\in H}e^{-\|h\|^2/12},
\quad F_k=\sum_{w\in H^*}e^{-c\|w\|^2}\prod_j\cos^6(\pi k w_j).
$$

Indeed CBD(3) is the difference of two sums of three independent fair bits. One bit difference has characteristic function $|(1+e^{2\pi i u})/2|^2$, giving the sixth power of the cosine for CBD(3). Its linear mgf is $\cosh(s/2)^6\le e^{3s^2/4}$. Integrating this product mgf against a standard Gaussian in $V$ gives $\mathbb E e^{s\|y\|^2}\le(1-3s)^{-d/2}$ for $0<s<1/3$ and optimizing gives the displayed cap exception. At height one apply the linear mgf to $-\langle X,h\rangle\ge\|h\|^2/2$. At each higher height on the cap, failure is majorized by the sum over $h$ of $\exp(t(B-k^2)-t\|h+ky\|^2)$. Drop the cap indicator before averaging. Gaussian Poisson summation gives exactly the stated term. Haar measure would give $F_k=1$. The unsmoothed plant law has finite support and total variation distance one from continuous Haar measure for every $k$. This comparison concerns the Gaussian test function. [Conditional first moments](wall1_dist_unique.md)

## Which aliases survive

Write $q=3329$, $N=1023$, $D=qL_0^*=\{(x,z)\in\mathbb Z^N:z=A^Tx\bmod q\}$. Then $H^*=V\cap D/q$ by pairing against $\pi L_0$. For every tested $k$, coprimality with $q$ gives
$$
kw\in\mathbb Z^N\quad\Longleftrightarrow\quad w\in J=V\cap\mathbb Z^N .
$$
The rational plane has a full-rank integer lattice $J$. These modes have characteristic function one, regardless of dilation. Nevertheless their total heat weight is at most $(1+2e^{-c}/(1-e^{-c}))^N$ by inclusion in the ambient integer lattice and $j^2\ge j$ for positive integers.

For $w=u/q$ define $r_k(u)$ by coordinatewise centered reduction of $ku$ modulo $q$. It lies in $D$, though centering can take it outside $V$. Its length divided by $q$ is exactly $\operatorname{dist}(kw,\mathbb Z^N)$. Off the exact aliases Part 92 gives $\|r_k(u)\|/q>446.59/q>0.134$ on its design event. Thus the q-ary minimum **does apply after wrapping**. Its consequence for each nonintegral mode is only the factor $\exp[-3\pi^2(446.59/q)^2]$ (about 0.59), since $\log\cos(\pi x)\le-\pi^2x^2/2$ for $|x|<1/2$ by integrating the tangent bound. The missing datum is multiplicity as a function of both original and wrapped length. [Graph dual and design event](wall1_qary_gap.md)

For comparison, with the convention $\sum_{w\ne0}\exp(-\pi\eta^2\|w\|^2)\le\epsilon$, the Micciancio–Regev bound gives $\eta_{2^{-d}}(H)\le\sqrt d/\lambda_1(H^*)<168$ on the same event. The heat kernel used here alone has parameter $\sqrt{c/\pi}<3.46$. A continuous Gaussian of covariance $3k^2 I/2$ would add $3\pi k^2$ to the *squared* parameter. Substituting this on all CBD modes would discard wrapping, including the entire lattice $J$. [Micciancio and Regev, Lemma 3.2](https://cims.nyu.edu/~regev/papers/average.pdf)

Define the finite statistic
$$
A_k=\sum_{u\in D\cap V,\ u\notin q\mathbb Z^N,\ \|u\|<10q}
\exp\left[-c\|u\|^2/q^2-3\pi^2\|r_k(u)\|^2/q^2\right].
$$
To bound the omitted modes put $\delta=0.134$. Disjoint radius-$\delta/2$ balls in $V$ bound the number through radius $s$ by $(1+2s/\delta)^d$. Thus the tail from radius 10 is at most $\sum_{j\ge10}b_j$ with $b_j=e^{-cj^2}(1+2(j+1)/\delta)^d$. Its consecutive ratio is decreasing and below $1/2$ at 10. In particular $F_k<3+A_k$. This gives a reproducible finite certificate: enumerate in the integer kernel of the prefix orthogonality equations subject to the graph congruences, using exact squared lengths for both cuts and outward upper weights. Certified upper counts in bins of the two squared lengths suffice, using the lower endpoints in the exponent. Feasibility of enumeration at these ranks is open. The graph equations specify the test for a supplied prefix. Part 92's one-vector exclusion alone gives no such counts for the selected plane.

## Evaluation in physical units

| Horizontal rank | Final rank | Certified $G$ exceeds | $K$ | Sufficient $A_k$ ceiling at every tested higher height |
|---:|---:|---:|---:|---:|
|505|506|7.22|30|$10^{48}$|
|506|507|7.259112|31|$10^{49}$|

Both rows use the passing width-506 block; the first projects away its exact shortest head. Meeting the row spends at most 0.005 on heights two and above on the cap. The norm exception costs less than 0.0025. To conclude positive-height failure below 0.01 one can additionally certify $S_1\le0.0025$. For example the product of the one-dimensional Gaussian sums at the primal GS lengths bounds $1+S_1$ by successive summation over translated integer fibers. A common physical GS floor of 13 suffices. Part 95 supplies only the prescribed suffix, with literal last certified floor about $0.01677121\,q^{511/1023}<1$. The Part 92 minimum floors (7.41883519 at 506 and its $\sqrt3/2$ multiple after dropping the head) also fall below the cap-based height-one cutoff $2\sqrt a$. Neither positive-height budget is thereby certified in full. Full uniqueness additionally requires the strict height-zero test $\lambda_1(H)>R$. All plant probabilities here condition on the design and reducer, so design-event failure is a separate cost. [Tail certificate](wall1_hkz_terminal.md) · [Determinant calculation](wall1_dist_unique.md)

## Interval checks

Run from the repository root with Python and mpmath. The preamble imports the audited log-Hermite caps. The assertions check sufficient thresholds, without substituting invented counts for $A_k$.

```python
from pathlib import Path
from math import isqrt, gcd
exec(Path('docs/research/wall1_dual_pinning.md').read_text()
     .split('\n```python\n')[1].split('def ceildiv')[0])
q, N, b = 3329, 1023, 506
ell = N-b
j = I.mpf(C[b])/(M*b)
U = ell*(ell+1)*(j/(b-1)+I.ln(I.mpf('1.01'))/(ell-1))
unit = I.exp(511*I.ln(q)/N)
G0 = unit*I.exp(-(U+ell*j)/N)
delta = I.mpf('.134')
assert I.mpf('446.59')/q > delta
for d, cap, exponent, K0 in [(505,'7.22',48,30),(506,'7.259112',49,31)]:
    G = G0*I.exp(-j*(b-d)/(b-1))
    assert G > I.mpf(cap)
    B = 1+I.mpf('1.9')*d
    t = d/(2*B)
    c = I.pi**2/t
    K = isqrt((10+19*d)//10)
    assert K == K0 and all(gcd(k,q)==1 for k in range(2,K+1))
    v = I.mpf(19)/15
    assert I.exp(-d*(v-1-I.ln(v))/2) < I.mpf('.0025')
    z = I.exp(-c)
    assert (1+2*z/(1-z))**N < 1+I.mpf('2e-13')
    first = I.exp(-100*c)*(1+22/delta)**d
    ratio = I.exp(-21*c)*((delta+24)/(delta+22))**d
    assert ratio < I.mpf('.5') and 2*first < 1
    assert I.sqrt(d)/delta < 168 and I.sqrt(c/I.pi) < I.mpf('3.46')
    cost = (I.sqrt(2*I.pi*I.exp(1)*B/d)/I.mpf(cap))**d
    assert cost*(K-1)*(3+10**exponent) < I.mpf('.005')
    z = I.exp(-I.mpf(169)/12)
    assert (1+2*z/(1-z))**d-1 < I.mpf('.0025')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT. All embedded blocks pass, as do the blocks of Parts 92, 94 and 97. Verified:

* periodicity of cos⁶;
* exact aliases (k coprime to q, so kw ∈ Z iff u ∈ qZ), with nonzero alias mass < 1.014·10⁻¹³;
* each nonintegral wrapped residue lies in D and has length > 446.59, so its weight is < 0.586926;
* the tail truncation at length 10;
* the budget: higher-height failure ∩ cap is < 0.003985 at rank 505 and < 0.002114 at rank 506, given the A_k ceilings.

Still open:

* multiplicity control of A_k;
* height one;
* the strict height-zero test.
