# Selection bias after one exact SVP and orthogonal projection

For one full Haar block, at the radius enclosing unit volume the conditional quotient density is at most **2 times Haar**, at either width 406 or 506. Integrating over the selected radius also gives a one-step 1% lower-tail certificate at **0.925 times the quotient's own Gaussian heuristic** at both widths. Neither certificate propagates through a sliding-window tour by multiplication. The obstruction concerns the conditional law of the next *input*, even for a tour starting on a Haar lattice.

## The marked Haar calculation

Put $m=b-1$, $X_j=SL_j(\mathbb R)/SL_j(\mathbb Z)$ with Haar probability $\mu_j$, $V_j=\pi^{j/2}/\Gamma(1+j/2)$, and $G_j=V_j^{-1/j}$ (unit-determinant GH radius). Use a fair sign for the shortest pair and a measurable orthonormal transverse frame depending only on its direction. Two nonparallel integer vectors having equal length imposes a nontrivial quadratic equality on the basis matrix, hence ties have Haar measure zero by a countable union. Every shortest vector is primitive.

First count **all oriented primitive marks**. Unfolding the sum over the orbit of the first coordinate vector gives Haar measure on the quotient by its integer stabilizer. The base variable is the marked vector $v=\ell\theta$ with marginal $dv/\zeta(b)$ by primitive Siegel. At the first coordinate vector the real stabilizer has lower right block in $SL_m$ and a free top row. Modding out the integer stabilizer gives a unimodular transverse lattice and a row modulo integer shears. Invariance gives Haar base shape and Haar probability in each torus fiber. Transport to $v$ by rotation and diagonal scaling $(\ell,\ell^{-1/m},\ldots,\ell^{-1/m})$ gives physical quotient $M=\ell^{-1/m}\Lambda$, with $\Lambda\sim\mu_m$. For $X_1$ use a point mass. [Primitive Siegel mean formula](https://doi.org/10.3934/jmd.2025015) · [Part 46, primitive incidence](wall1_haar_prefix_law.md)

Write $t\in\operatorname{Hom}(\Lambda,\mathbb R/\mathbb Z)$ with Haar probability $dt$. Its values on a basis are independent uniform phases. The reconstructed lattice consists of
$$
 \ell^{-1/m}x+\ell s\theta,\qquad x\in\Lambda,\quad s\bmod1=t(x).
$$
The zero fiber is precisely $\mathbb Zv$. Put $R=\ell^{b/m}$. The nearest lift of each $x\ne0$ gives the finite void test
$$
 I=\prod_{0<|x|<R}{\bf1}\{(|x|/R)^2+\|t(x)\|_{\mathbb R/\mathbb Z}^2\ge1\}.
$$
Multiplying primitive incidence by $I/2$ assigns total mass one per generic parent. Consequently the joint density in $(\ell,\theta,\Lambda,t)$ relative to $d\ell$, uniform direction, $d\mu_m$, and $dt$ is exactly
$$
 \frac{b V_b\ell^{b-1}}{2\zeta(b)} I.
$$
Integrating out direction leaves the same density. Write $w_\ell=\int I\,dt$ and $Z_\ell=\int w_\ell\,d\mu_m$. The length density is the radial prefactor times $Z_\ell$ and the conditional shape density is $p_\ell=w_\ell/Z_\ell$ wherever $Z_\ell>0$. Lifts after selection are uniform on the accepted subset. All formulas apply conditionally to a normalized projected input *if its conditional shape law is Haar*. A physical input determinant $D$ scales lengths by $D^{1/b}$.

## Bounds on the void probability

For each pair $\{x,-x\}$ with $0<|x|<R$, the chance of a short lift equals
$h(x)=\min(1,2\sqrt{1-(|x|/R)^2})$, since evaluation of a uniform character at any nonzero vector is uniform, including nonprimitive vectors. Let $S$ sum $h$ once per pair. This counts in expectation the number of transverse pairs admitting a short lift. The union bound gives
$$
 (1-S)_+\le w_\ell\le1,\qquad (1-S)_+\le p_\ell\le1/Z_\ell .
$$
No independence among phases at different vectors is required. On $\lambda_1(\Lambda)\ge R$ the upper bound is attained; on $\lambda_1(\Lambda)<\sqrt3 R/2$ every character fails, since the distance to the nearest integer is at most $1/2$. On $S\le\delta<1$ the density is at least $(1-\delta)/Z_\ell$.

For $m\ge2$ apply ordinary Siegel in the quotient, dropping the cap at one. By slicing the unit $b$-ball along its last coordinate,
$$
 \mathbb E S\le\tfrac12 R^m\int_{|u|<1}2\sqrt{1-|u|^2}\,du
 = V_b\ell^b/2=:a .
$$
Thus for *every* event of Haar mass $\varepsilon$, its conditional probability is at most $\min(1,\varepsilon/(1-a))$ when $a<1$. The same bound with the largest $a$ applies to any conditioning interval in this range. At both requested widths the constant is 2 at $\ell=G_b$ and below 3.26 at $\ell=(2\log2)^{1/b}G_b$. The latter is a reference radius, not an asserted finite-dimensional median. These are bulk scales in a verifiable sense. At $a\le1$, integrating the radial density with $1-a\le Z_\ell\le1$ brackets the minimum CDF between $(a-a^2/2)/\zeta(b)$ and $a/\zeta(b)$. In particular the unit-volume radius has CDF between 0.374 and 0.5 at both widths. For lengths beyond this range $1/Z_\ell$ remains the conditional bound when defined.

## Integrating the length for a small quotient minimum

Unconditionally Minkowski gives $V_b\ell^b\le2^b$, so integrating the joint envelope proves the crude all-event constant $2^{b-1}/\zeta(b)$. For $E_c=\{\lambda_1(\Lambda)<cG_m\}$ the failed-lift region gives a much smaller integration range. On accepted marks in $E_c$, $R<2cG_m/\sqrt3$. Integrate the radial prefactor up to this cutoff, then use primitive Siegel and the sign pair in the quotient:
$$
 \Pr(E_c)\le \frac{V_b}{2\zeta(b)V_m}(2c/\sqrt3)^m\mu_m(E_c)
 \le \frac{V_b}{4\zeta(b)\zeta(m)V_m}(2c^2/\sqrt3)^m.
$$
At $c=0.925$ this is below 1% at both widths, over the actual joint one-step output. At the fixed length $G_b$ the conditional estimate instead gives $\Pr(E_c\mid\ell=G_b)\le c^m/\zeta(m)$, below 1% already for $c=0.988$ at both widths.

## Where the tour calculation stops

After exact SVP in $[i,i+b)$ the next window retains the projected $b-1$ directions and appends one column. Even knowing their normalized shape leaves their physical determinant, the new perpendicular height, and the new column's displacement modulo the retained lattice undetermined. Conditioning on earlier comparisons and basis updates can change their joint law. Even the first proper window requires a specified basis or block sampling rule. The incidence law of a marked block does not identify the law of a window chosen by a basis section on an ordinary Haar parent.

More explicitly, if the full parent has conditional Haar density $f_h$ at history $h$, and $q_h(v\mid L)$ is its oriented selection probability (averaging presentation data conditional on $L,h$), the unfolded next-state weight at fixed $v,\Lambda$ is $\int f_h(L)q_h(v\mid L)\,dt$ in the **full parent dimension**. For a full-width first step this reduces to $w_\ell/2$. For a proper window, a shorter vector outside the window does not veto selection. The full projected parent contains the exterior columns, and retaining the presentation may be essential to predict the next window. [Marked reducer kernel](wall1_markov_reducer.md)

A path likelihood product would require conditional Radon–Nikodym derivatives for the actual transitions against a specified comparison process on the same histories. The first-step marginal derivative supplies none of these subsequent derivatives. Even a hypothetical per-step bound of 2 would give $2^k$ after $k$ factors. No bound on the product restricted to the terminal short-minimum event, or tour-level 1% value of $c$, follows here. This leaves open a specified implementation's quantile. For a physical horizontal block $H$ the relative-GH event uses $\det(H)^{1/\mathrm{rank}(H)}G_{\mathrm{rank}(H)}$; a fixed physical threshold also requires control of that random determinant. Independent planting leaves the reducer-dependent horizontal lattice law to determine. Simultaneous prefix bounds for bases passing the Li–Walter tests concern a different hypothesis and observable. [Horizontal projection](wall1_decoupled.md) · [Two-block slide bounds](wall1_li_walter.md) · [Wall 1](../PROOF_GAP.md)

## Reproducible interval checks

The zeta upper bound isolates the term at two and integrates the remaining decreasing tail. Lower bounds of one suffice in the short-event estimates. Half-integer ball volumes use the exact two-rank recurrence.

```python
from mpmath import iv
iv.dps = 60
I = iv.mpf
V = [I(1), I(2)]
for j in range(2, 507):
    V.append(2 * iv.pi * V[j-2] / j)
for b in (406, 506):
    m = b - 1
    z_hi = 1 + I(2)**(-b) * (1 + I(2)/(b-1))
    a = I(1)/2
    assert 1/(1-a) == 2
    assert (a-a*a/2)/z_hi > I('0.374')
    assert a == I('0.5')
    assert 1/(1-iv.log(2)) < I('3.26')
    c = I('0.925')
    assert V[b]/(4*V[m]) * (2*c*c/iv.sqrt(3))**m < I('0.01')
    assert I('0.988')**m < I('0.01')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Factor of two and denominator.** The oriented primitive incidence marginal is dv/ζ(b), and exactly two marks survive. The
  lower bound 1 − Z_ℓ ≤ V_bℓ^b/2 comes from a union over sign pairs, Siegel averaging and slicing of the b-ball. Together they
  give Z_ℓ ≥ 1/2 at ℓ = G_b, and hence density ≤ 2.
* **Unconditional bound.** Pr[λ1(Λ) < 0.925·G_{b−1}] ≤ V_b/(4ζ(b)ζ(m)V_m)·(2c²/√3)^m. This is below 0.023303% at rank 406 and
  below 0.006237% at rank 506. It was also verified in exact rational arithmetic.
* **Scope.** No tour-level bound follows. The law of the appended column, conditional on earlier selections, is missing.
