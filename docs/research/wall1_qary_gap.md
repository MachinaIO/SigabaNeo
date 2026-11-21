# Screening twin extensions by the ambient dual minimum

For uniform graph matrices at $(m,n,q)=(511,512,3329)$, the following lower bounds hold with probability greater than 0.99, simultaneously for both widths and all passing bases. The terminal oracle is exact and the twin slack is 1%, with the Hermite caps of Part 88. Length normalization divides by $u=q^{m/N}$, $N=m+n$. All radius entries are rounded down independently.

| Horizontal width | Physical terminal minimum | Normalized | Part 88 Haar bound | Fraction of displayed Haar bound | Remaining normalized gap (approx.) |
|---:|---:|---:|---:|---:|---:|
|406|3.36337038|0.05852472|0.12531282|46.70%|0.06678810|
|506|7.41883519|0.12909231|0.36188705|35.67%|0.23279474|

The gain over Part 89's 41.15% and 32.87% comes from excluding all low-determinant extensions on a single event about short dual vectors. The gap in the table compares sufficient radii. Neither calculation gives a lower bound on the exact finite-ensemble first moment relative to Haar. [Part 89](wall1_twin_qary.md) · [Part 88](wall1_li_walter.md)

## What maximal defect counts

Write $C=\ker[I\ A]$ over the field, $V$ for the extension plane of dimension $r=N-\beta+1$, $S=V\cap\mathbb Z^N$, $W=S\bmod q$, and $z=N-r$. Saturation gives $\dim W=r$. In the notation of the [exact graph mean](wall1_selfdual_qary.md),
$$
d=m-\mathrm{rank}([I\ A]|_W),\qquad
\dim(W\cap C)=r-m+d,\qquad
d=\dim(W^\perp\cap C^\perp).
$$
Hence $d=z$ means precisely $C\subset W$. It requires $t=n$, $s=r-n=m-z$ and $j=0$, since projection of $C$ onto the secret coordinates is bijective. Its exact contribution at physical cap $X$ is
$$q^{-nz} C_n(X/q^{m-z}).$$
Indeed the induced $z\times n$ matrix must vanish. In the Part 89 height envelope the $T^N$ term cancels the modular penalty exactly here. At $d=z-i$ its residual multiplier relative to the common envelope is $q^{-i(m-z+i)}$. Already at $i=1$ the exponents are 107 and 7 respectively. This identifies the dominant term of that *bound*. Shallower terms can be nonzero. For example a coordinate plane with full secret projection has height one, and its induced matrix can have rank one with positive probability whenever the cap admits index $q^{m-z+1}$. Even a factor of a million saved in an $X^N$ bound improves the inferred radius by only $10^{6/(Nr)}$.

Every extension $P=L_A\cap V$ contains $qS$. The horizontal intersection with $q\mathbb Z^m\oplus0$ has rank $\dim_{\mathbb Q}(V\cap(\mathbb Q^m\oplus0))$, irrespective of $A$. Thus horizontal rank alone does not detect defect. In particular for a fixed full-secret coordinate plane it stays constant while $d$ varies with $A$. The source of the apparent excess over Haar is the unsuppressed *upper estimate* for the arithmetic height count in the displayed term. Establishing an actual excess would require a sharper evaluation or a lower bound for the exact sum. Haar has no positive mass on any fixed rational plane.

Maximal defect is compatible even with an exactly shortest first head and a short terminal head. Take $A=0$, and order the orthogonal coordinate basis with $n-1$ secret units first, then $m-z$ horizontal $q$-axes, then the omitted secret unit, then the remaining $z$ horizontal $q$-axes. The prefix rank is $k=r-1$, its volume is $q^{m-z}$, and the terminal quotient is exactly $\mathbb Z\oplus q\mathbb Z^z$, of minimum one. The extension contains the full code modulo $q$ in its **ambient saturation**. Both twin inequalities hold if $a\ge q^{(m-z)/k}$, where $a=1.01\,\gamma_\beta^{(k-1)/(2(\beta-1))}$. This inequality holds even using the elementary Haar lower bound $\sqrt{\gamma_b}\ge V_b^{-1/b}$: by the vector mean formula the expected number of nonzero vectors in the ball of volume one is one, and a nonempty count is at least two. Here $V_b$ denotes unit ball volume. The interval check below verifies the inequality. This is a passing witness on a positive-probability input, not a claim about which flag a particular implementation selects. The first block in the general twin predicate only needs HSVP.

## An obstruction shared by all low extensions

Let $D=qL_A^*$ and $w=q/u$, its determinant length unit. For each primitive extension form $J=D\cap V^\perp$. Then
$$\det J=q^z\det P/q^m.$$
Indeed, extend a basis of $P$ to a basis of $L_A$. The projected complementary basis has covolume $q^m/\det P$ and its dual generates $L_A^*\cap V^\perp$. In the deepest stratum $J=V^\perp\cap\mathbb Z^N$: the latter reduces into $W^\perp\subset C^\perp$ and $D$ is exactly the integral preimage of $C^\perp$. For every defect, $J$ must avoid any ball avoided by the nonzero vectors of $D$. Hermite's inequality therefore gives
$$
\det P/u^r=\det J/w^z\ \ge\ (\lambda_1(D)/(w\sqrt{\gamma_z}))^z .
$$
This bypasses the multiplicity of planes on exceptional inputs.

Explicitly $D=\{(x,y)\in\mathbb Z^{m+n}:y=A^t x\bmod q\}$. Below length $q$ every nonzero possible member has $x\ne0\bmod q$ and membership probability $q^{-n}$. For $T<q$, pair opposite vectors, dominate the ball indicator by $\exp(c(T^2-\|v\|^2))$, and extend the positive sum to all integral vectors. Poisson summation in one dimension and $j^2\ge j$ for $j\ge1$ give
$$
\Pr(\lambda_1(D)\le T)\le \tfrac12 q^{-n}e^{cT^2}
\left[\sqrt{\pi/c}\,(1+2v/(1-v))\right]^N,\qquad v=e^{-\pi^2/c}.
$$
The certificate uses $T\simeq446.59741$ and $c=N/(2T^2)$. Off this event, combine the determinant floor with Part 88's $\det P\le M_0g^r$, where $g$ is the physical terminal head, to obtain
$$g/u\ \ge\ M_0^{-1/r}\left(T/(w\sqrt{\gamma_z})\right)^{z/r}.$$
Exact terminal SVP identifies $g$ with the projected minimum. No assumption on the output distribution or heuristic on sublattice shape enters this step. The one-vector Hermite obstruction can leave many admissible extensions above its cutoff. It does not evaluate their number or close the [planted lifting gap](../PROOF_GAP.md).

## Reproduce from the repository root

The setup imports the same outward-rounded Hermite caps as Part 88, with $C[j]/(Mj)$ bounding $\log\sqrt{\gamma_j}$. Output integers are in units of $10^{-8}$.

```python
from pathlib import Path
exec(Path('docs/research/wall1_dual_pinning.md').read_text()
     .split('\n```python\n')[1].split('def ceildiv')[0])
N,m,q = n,511,3329
u = I.exp(m*I.ln(q)/N)
w = q/u
# exp(-a |v|^2) with the continuous Gaussian saddle point.
L = I.sqrt(N/(2*I.pi*I.exp(1))) * I.exp(I.ln(I.mpf('.0199'))/N)
T = w*L
a = N/(2*T**2)
v = I.exp(-I.pi**2/a)
theta = I.sqrt(I.pi/a)*(1+2*v/(1-v))
assert T < q and a*T**2 + N*I.ln(theta)-512*I.ln(q)-I.ln(2) < -I.ln(100)
def down(x):
    return int((10**8*x).a)
for b, haar in [(406,'0.12531282'),(506,'0.36188705')]:
    k,z = N-b,b-1
    ell = k*(I.mpf(C[b])/(M*b*z)+I.ln(I.mpf('1.01'))/(k-1))
    H = I.exp(I.mpf(C[z])/(M*z))
    R = I.exp(-ell+I.mpf(z)/(k+1)*I.ln(L/H))
    print(b,down(R),down(R*u),down(R/I.mpf(haar)),down(T))
    logV = (I.mpf(b)/2)*I.ln(I.pi)-I.loggamma(1+I.mpf(b)/2)
    assert I.ln(I.mpf('1.01'))-(k-1)*logV/(b*z) > (m-z)*I.ln(q)/k
```

## Audit note (Nov 2026)

Independent audit: CORRECT WITH MINOR ISSUES. The scripts reproduce every number (0.05852472 / 0.12909231; Part 89's
0.05157150 / 0.11896865 also reproduced). The dual-vector implication is deterministic. The event λ1(D) > T does not depend on
the width, so both rows hold jointly. An exact theta-sum recomputation gives log Pr ≤ −4.6102 against log 0.01 = −4.6052, so the
1% budget is met with only about 0.5% relative slack. A display typo (`\qquad`) has been fixed.
