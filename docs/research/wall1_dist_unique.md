# Conditional first moments for terminal uniqueness

At horizontal rank 506 the certified covolume is already large enough for the volume term of a Gaussian first moment. The missing higher-height quantity is a **CBD-weighted dual theta sum**, evaluated on the selected quotient at several integer dilations. At rank 406 even the available covolume floor falls short for this test. At both ranks height zero is a separate obstruction. None of the comparisons below establishes a new full-terminal width below 647.

## Conditional certificate

Use physical lengths. Write $Q$ for the horizontal orthogonal projection, $H=QL_0$ in its $d$-dimensional span, $X$ for the 1023 independent CBD(3) coordinates, $y=QX$ and $R^2=1+\|y\|^2$. Fix the design and independent reducer coins. Part 47 gives projected vectors $(ky+h,k)$ with $h\in H$, and preserves the product law of $X$ after this conditioning. All sums below are for this fixed lattice. Positive heights suffice by sign symmetry. Ties count as failures. [Wall 1, Part 47](../PROOF_GAP.md) · [Unique splitting and fiber counts](../../SigabaNeo/Lib/Lattices/Research/Wall1/Decoupled.lean)

Fix $a>3d/2$, $B=1+a$, $K=\lfloor\sqrt B\rfloor$, and write
$$p_a=\exp[-(d/2)(v-1-\log v)],\qquad v=2a/(3d).$$
Then $\Pr(R^2>B)\le p_a$. Indeed the coordinate mgf is $\cosh(s/2)^6\le e^{3s^2/4}$. Integrating the linear mgf against an independent standard Gaussian in the projection space gives $\mathbb E e^{t\|y\|^2}\le(1-3t)^{-d/2}$ for $0<t<1/3$. Chernoff optimization gives the claim. [Threshold note](wall1_threshold.md)

At height one the competitor test for $h\ne0$ is $-\langle X,h\rangle\ge\|h\|^2/2$. Its probability is at most $e^{-\|h\|^2/12}$ by the same linear mgf. Write $S_1=\sum_{0\ne h\in H}e^{-\|h\|^2/12}$. Alternatively the height-one cost on the capped event is zero if $\lambda_1(H)>2\sqrt a$ by the triangle inequality. Let $E_1$ be $S_1$ or this zero bound when applicable.

For $2\le k\le K$ define, for any $t>0$,
$$
F_k(t)=\sum_{w\in H^*}e^{-\pi^2\|w\|^2/t}
                \prod_{j=1}^{1023}\cos^6(\pi k w_j),\qquad
M_k(t)=\frac{e^{t(B-k^2)}(\pi/t)^{d/2}}{\det H}F_k(t).
$$
Here $w_j$ is in the **ambient CBD coordinate frame**. For arbitrary positive $t_k$ the requested nonzero-height probability is at most
$$\min\{1,\ p_a+E_1+\textstyle\sum_{k=2}^K M_k(t_k)\}.$$
For uniqueness including height zero the same formula suffices if $\lambda_1(H)>\sqrt B$.

**Proof.** On the capped event a competitor at $k\ge2$ contributes at least one to $\sum_{h\in H}\exp[t(B-k^2-\|h+ky\|^2)]$. We may include $h=0$ in this majorant. Integrate over the original plant law, without conditioning it further on the norm cap. Gaussian Poisson summation on $H$ gives the displayed formula since $\langle w,QX\rangle=\langle w,X\rangle$ and each coordinate is a sum of six independent fair half-signs. The dual series converges absolutely by Gaussian decay. Sum the resulting first moments and charge the cap exception once. This proof also covers $B=k^2$. Neither a Gaussian plant nor uniformity modulo $H$ is assumed.

There is also a finite primal version when a shell count is available. For $k\ge2$ completing the square gives the *exact* test
$$
\left\|y+\frac{k h}{k^2-1}\right\|^2
\le \frac{\|h\|^2}{(k^2-1)^2}-1 .
$$
Thus only $k^2-1\le s=\|h\|\le k\sqrt a+\sqrt{B-k^2}$ can contribute on the cap. In this annulus put $m_k(s)=(ks-\sqrt{s^2-(k^2-1)^2})/(k^2-1)$. The ball lies in the half-space $-\langle X,h/s\rangle\ge m_k(s)>0$. Consequently the finite shell sum of $\exp(-m_k(s)^2/3)$ over these $h$ can replace $M_k$, taking the smaller bound separately at each height. This test uses only lengths and multiplicities and may be pessimistic because it drops all transverse constraints. For a profile-only majorant, the count inside radius $r$ is at most $\prod_i(1+\lfloor2r/g_i\rfloor)$: fix the later coefficients, then the $i$th coefficient belongs to an interval of length at most $2r/g_i$. Multiplying this count at the upper end of each shell by the supremum weight on that shell gives a valid upper sum, including for sheared bases.

## Values at the two budgets

Here is one reproducible allocation. Take $a=1.9d$, $t=d/(2B)$, $E_1\le0.0025$ and allocate $0.005$ to heights $2,\ldots,K$. Writing $G=(\det H)^{1/d}$ and $C=\sqrt{2\pi e B/d}$, it suffices that
$$\sum_{k=2}^K e^{-tk^2} F_k(t)\le0.005(G/C)^d.$$
A simple benchmark is $F_k(t)\le2$ at every such height and $G\ge G_*=C[2(K-1)/0.005]^{1/d}$. The factor two is a sufficient test, not a prediction. Alternatively a supplied list of GS lengths $g_i$ gives $1+S_1\le\prod_i\sum_{n\in\mathbb Z} e^{-n^2g_i^2/12}$: sum the first integer coefficient at fixed later coefficients, bound the translated one-dimensional Gaussian sum by its value at zero by Poisson summation, and repeat. For example a common floor 13 suffices for the specified $S_1$ budget at all four ranks. One still needs the height-zero minimum.

| Final rank | Horizontal $d$ | Height-zero sufficient floor (strict) | Floor handling height one as well (strict) | $G_*$ rounded up | Available physical minimum floor |
|---:|---:|---:|---:|---:|---:|
|406|405|27.758|55.480|5.832|2.912 (inherited)|
|407|406|27.793|55.549|5.832|3.36337038|
|506|505|30.992|61.952|5.807|6.424 (inherited)|
|507|506|31.023|62.013|5.807|7.41883519|

The 405/505 rows drop the exact shortest head of the corresponding horizontal 406/506 block. Lifting a quotient vector with parallel component at most half the old minimum gives the inherited factor $\sqrt3/2$. The other rows use the published horizontal widths directly. The combined low-height floors at those widths are only about 2.62 and 1.32 times the published physical $0.85$ GSA targets, **conditional on the separate higher-height test**. The earlier 35.02 and 19.41 multipliers required only a minimum certificate. [Threshold note](wall1_threshold.md)

For clarity, Part 88's two twin tests and exact terminal head give the following deterministic covolume floors. In determinant-one units let $V$ be the prefix determinant, $b$ the horizontal width, $l=1023-b$, $J_b$ the audited upper bound on $\sqrt{\gamma_b}$ and $U=l(l+1)[\log J_b/(b-1)+\log(1.01)/(l-1)]$. Then $V\le e^U g^l$ and $g\le J_b V^{-1/b}$ for normalized head $g$. Hence $G\ge D\exp[-(U+l\log J_b)/1023]$, $D=3329^{511/1023}$. After dropping the head the new physical geometric mean is at least $G/J_b^{1/(b-1)}$ by the same Hermite inequality. [Part 88](wall1_li_walter.md) · [Terminal determinant calculation](wall1_hkz_terminal.md)

At $b=406,506$ the physical floors round down to **3.099229 and 7.259112** respectively. At 406 even $F_2\ge1$ makes the displayed sum test fail when evaluated with that floor. At 506 one can allow every $F_k$ as large as $10^{49}$ using the certified floor. Thus a near-uniformity theorem would be stronger than necessary there. The respective determinant comparisons persist after dropping the head. These failures of sufficient tests say nothing decisive about the actual selected lattice.

Part 92 bounds the minimum of the ambient dual, hence also of its sublattice $H^*=L_0^*\cap\mathrm{im}(Q)$ (physical floor about $446.6/3329$). This excludes a ball but supplies no estimate here of the weighted sum at the required scale. In particular if $kw\in\mathbb Z^{1023}$ the CBD factor is one. Discarding all CBD factors gives the unshifted Gaussian sum, whose primal zero term alone contributes $e^{t(B-k^2)}\ge1$ to the majorant. The listed tail heights for the prescribed dual completion cover only a suffix and their literal last floors in physical units are below one at both widths. They do not supply the common floor 13 test. The Haar head radii from Part 88 apply to another ensemble; no Haar averaging of the output quotient enters these comparisons. [Part 92](wall1_qary_gap.md) · [Tail heights](wall1_hkz_terminal.md)

Finally a fixed quotient with 99% uniqueness necessarily has $\lambda_1(H)>\sqrt{1+1.2d}$: Paley–Zygmund for $\|y\|^2$ gives probability at least $0.04d/(d+2)>0.01$ above $1.2d$, using the nonpositive CBD fourth cumulant as in the threshold note. The certified minima are below even this necessary floor. A higher-height estimate alone cannot close Wall 1. The 99% calculation is conditional on a fixed quotient satisfying the tests. An overall recovery theorem must also budget failure of the design event and of prefix lifting. [Threshold note](wall1_threshold.md)

## Interval checks

Run from the repository root with Python and mpmath. The imported preamble supplies outward Hermite caps.

```python
from pathlib import Path
from math import isqrt
exec(Path('docs/research/wall1_dual_pinning.md').read_text()
     .split('\n```python\n')[1].split('def ceildiv')[0])
D = I.exp(511*I.ln(3329)/1023)
for b,old in [(406,'3.36337038'), (506,'7.41883519')]:
    l = 1023-b
    j = I.mpf(C[b])/(M*b)
    U = l*(l+1)*(j/(b-1)+I.ln(I.mpf('1.01'))/(l-1))
    G0 = D*I.exp(-(U+l*j)/1023)
    assert int((10**6*G0).a) == {406:3099229,506:7259112}[b]
    for d in (b-1,b):
        a = I.mpf('1.9')*d
        B = 1+a
        K = isqrt((10+19*d)//10)
        t = d/(2*B)
        v = 2*a/(3*d)
        assert I.exp(-d*(v-1-I.ln(v))/2) < I.mpf('.0025')
        c = I.sqrt(2*I.pi*I.exp(1)*B/d)
        Gstar = c*I.exp(I.ln(400*(K-1))/d)
        assert Gstar < I.mpf('5.832' if b==406 else '5.807')
        G = G0 if d==b else G0*I.exp(-j/(b-1))
        budget = I.mpf('.005')*(G/c)**d
        if b==406:
            assert budget < I.exp(-4*t)
        else:
            assert budget > 2*(K-1)
            if d==b:
                assert budget > (K-1)*10**49
        z = I.exp(-I.mpf(169)/12)
        assert (1+2*z/(1-z))**d-1 < I.mpf('.0025')
        minimum = I.mpf(old)*(1 if d==b else I.sqrt(3)/2)
        assert minimum < I.sqrt(1+I.mpf('1.2')*d)
        print(d, I.sqrt(B), 2*I.sqrt(a), minimum, Gstar, G)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES. Both conditional first-moment bounds hold:

* Poisson/CBD characteristic-function step: ⟨w, QX⟩ = ⟨w, X⟩ for w ∈ H*.
* Primal shell counts: valid under shear.

The allocation and every rounding direction were rechecked:

* d = 406: the determinant root 3.0992 cannot even pay the k = 2, w = 0 term.
* d = 506: the root 7.2591 is above the benchmark 5.8063, and the budget is 7.1·10⁵⁰, so F_k ≤ 10⁴⁹ at each height 2..31 suffices.

The height-zero floor (actual λ1(H) > 24.6617 at d = 506) is necessary, by Paley–Zygmund with the nonpositive fourth cumulant.

Wording: "nonzero-height probability" means the probability that a nonzero-height competitor ties or beats the plant.
