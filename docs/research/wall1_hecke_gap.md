# The Hecke correspondence in the first tour

The full-torsion append is an affine chart of a genuine **rank-$b$** Hecke correspondence based at a split lattice. The chart has relative mass greater than $1-1/q$. Even the complete correspondence applied to this base does not produce a Haar density from the cubic start. In fact the append is singular in rank $b$ even if the incoming rank-$b-1$ shape is Haar. Thus the proposed density iteration fails before a comparison of spectral constants.

## The two ranks and the marks

Put $r=b-1$, $X_d=SL_d(\mathbb R)/SL_d(\mathbb Z)$, and write $m_d$ for Haar probability. These are embedded determinant-one lattices. Intrinsic shapes and length events also factor through rotations. Use the no-lookahead, horizontal-first exact tour with fixed ambient tie rule. Its state $z$ includes the physical retained lattice $L$ in its frame, $D=\det L$, and its marked subgroup $H\le q^{-1}L/L$. At a graph step let $e$ be the next perpendicular unit axis and $h=1$. With $u$ uniform on $H$, form
$$
 W_u=L+\mathbb Z(\tilde u+he),\qquad x_u=(Dh)^{-1/b}W_u\in X_b.
$$
Choice of lift has no effect. Select a shortest vector $v$ in physical units, project by $Q_v$ orthogonally to its complement, and set $L'=Q_vW_u$, $D'=Dh/|v|$, $H'=(Q_v)_*H$. The new shape is $(D')^{-1/r}L'$. For bounded tests the exact Markov operator is $P F(z)=|H|^{-1}\sum_u F(z'_u)$ with frame updated as in the tour. For a test only of the next shape this is extension followed by SVP and projection, with the same tie convention. Before graph columns enter, the appends have $u=0,h=q$. [Part 108](wall1_first_tour.md)

One can define a family of shape-to-shape kernels by prescribing the missing marks for each input. For example, fix $D$, take $L=D^{1/r}x$, $H=q^{-1}L/L$, and fix the frame convention. This gives a single-step $P_D$ on $X_r$. Iteration requires updating $D$ and $H$. Even for the same shape the normalized input height $hD^{-1/r}$ can vary. A marginal transition for the actual tour integrates the marked kernel against the time-dependent conditional law of these data given the current shape.

## Which Hecke neighbors occur?

Set $B=L\oplus qh\mathbb Ze$. For full $H$, each $W_u$ contains $B$ with index $q$. The index-$q$ superlattices of $B$ are indexed by the lines in $q^{-1}B/B\simeq\mathbb F_q^b$. In an integral basis of $L$, writing $u=a/q$ modulo $L$ gives exactly the line $[(a,1)]$. The missing lines have last coordinate zero. Consequently, if $T$ averages all normalized index-$q$ superlattices and $j(z)=(qDh)^{-1/b}B$, then for every nonnegative window test $F$,
$$
 A F(z)=\mathbb E_u F(x_u)\le p^{-1}(TF)(j(z)),\qquad
 p=\frac{q^r(q-1)}{q^b-1}.
$$
This is conditioning at the level of labeled neighbors, so the inequality also holds after any common nonnegative quotient test. The TV error on window events is at most $1-p<1/q$. A proper mark of dimension $k$ selects only $q^k$ chart points, with mass $p q^{k-r}$ in the complete correspondence. This comparison of probabilities gives no centered operator norm. In rank $r$, adjoining a nonzero $u$ *horizontally* would give an index-$q$ neighbor; it erases which generator accompanies the new height and computes a different window.

Here is an intrinsic witness to singularity. Every $W_u$ contains $qhe$ and its dual contains $e/h$. Thus the normalized window has parallel nonzero primal and dual vectors, including after an arbitrary common rotation. For a Haar lattice $g\mathbb Z^b$, fix nonzero integral labels $a,d$. Parallelism of $ga$ and $g^{-T}d$ requires $g^Tg a\in\mathbb Rd$, a proper real analytic condition (a determinant-one positive definite form can vary the direction of its value on $a$). The countable union over labels is Haar-null. The same witness applies to all neighbors of $B$ using $qe/h$ in the dual, since each neighbor lies in $q^{-1}B$. Hence even averaging over an incoming Haar shape and a random scale cannot justify evaluating Haar $L^2(X_b)$ classes on these windows. The indicator of the null set is zero as an $L^2$ class and its append average is identically one. In particular the split-base restriction of $TF$ is a pointwise operation requiring a specified test representative.

## The spectral number for the complete correspondence

For the split level-one lattice space in any dimension $d\ge3$, the normalized fixed-rank index-$q$ operator satisfies
$$
 \|T\|_{L^2_0(m_d)\to L^2_0(m_d)}\le B_q=\frac{2\sqrt q}{q+1}.
$$
Use Clozel–Oh–Ullmo, *Hecke operators and equidistribution of Hecke points*, Theorem 1.1 and its split-case remark, Theorem 1.7 and §4.7 for the central quotient, and §5.1 for $GL_d$. The rational diagonal has valuations $(1,0,\ldots,0)$ for sublattices; the inverse correspondence for superlattices is its adjoint. Pairing the extreme entries gives one strongly orthogonal root of valuation difference one, with all other paired differences zero. The rank-one spherical factor at distance one is $q^{-1/2}(1+(q-1)/(q+1))$; the split-case prefactor is one. This uses the finite-place spherical estimate underlying the Hecke theorem. Qualitative property (T) of the real group alone supplies no numerical $q$-factor. [Clozel–Oh–Ullmo, especially §§1, 3.1 and 5.1](https://ullmo.ihes.fr/publications/COU-Invent.pdf)

At $q=3329$, $0.03465<B_q<0.03466$ in all four dimensions $405,406,505,506$. This is a verified upper bound for an operator on Haar mean-zero functions. No spectral constant for $P$ follows. Part 52 uses a different Smith type and ambient starting lattice to transfer suitable tests as $q$ grows. Its point-evaluation and boundary costs are relevant even for the complete orbit. Part 104 concerns arbitrary fresh basis selectors; the singularity above holds already for this specific inherited window. [Part 52](wall1_hecke_transfer.md) · [Wall 1, Part 104](../PROOF_GAP.md)

## Haar bounds for SVP and projection

Write $K$ in the forward direction on densities from $X_b$ to $X_r$ and $K^*$ on tests in the reverse direction. Use Part 105's transverse frame depending only on the selected direction and its fair sign, or use intrinsic shape tests. For $p_b=K1$, Jensen and duality give
$$
 \|K^*F\|_{2,m_b}^2\le\int |F|^2 p_b\,dm_r
 \le\|p_b\|_\infty\|F\|_{2,m_r}^2,\qquad
 \|K\|\le\sqrt{\|p_b\|_\infty}.
$$
For a deterministic shape map the first inequality is equality. Under disintegration of the Haar parent at shortest length $\ell=G_b$, where $G_d=V_d^{-1/d}$ for unit-ball volume $V_d$, Part 105 gives conditional output density at most 2. Thus the corresponding conditional operator, measured against the **conditional parent law**, has norm at most $\sqrt2$. In physical quotient units acceptance forces minimum at least $\sqrt3\ell/2$ by rounding a lift along the selected vector. For the determinant-one quotient the bound is $\sqrt3\ell^{b/r}/2$ for unit parent determinant.

Unconditionally the unfolded radial density envelope is $bV_b\ell^{b-1}/(2\zeta(b))$. Integrating up to Minkowski's cutoff $V_b\ell^b\le2^b$ gives $M_b=2^{b-1}/\zeta(b)$ as a bound on $\|p_b\|_\infty$. Hence $\|K\|\le\sqrt{M_b}$ and $\|K1-1\|_2\le\sqrt{M_b-1}$. The conditional product $\sqrt2 B_q<0.05$ uses incompatible reference laws. The unconditional upper estimate $\sqrt{M_b}B_q$ exceeds one at both widths (use $\zeta(b)<2$); this upper estimate gives no lower bound on the actual norm. Even a sharper estimate would leave the singular extension unresolved. [Part 105](wall1_selection_law.md)

## Cubic start and terminal probability

In $W_u/qW_u$, the mark spans a $k$-plane in horizontal coordinates. Projection by a primitive $v$ quotients this vector space by the line of $v\bmod q$ (complete $v$ to an integral basis). Thus $k$ drops by one precisely when the line lies in that plane. A chart estimate uniform in the full mark cannot be iterated without controlling the distribution of the surviving marks. For $H=0$ there is a single transition. Even full marks can preserve the cube on a zero draw, since the new vertical axis is shortest there.

At the cubic start $L=q\mathbb Z^r$ the shape law is a point mass. Each of the 512 graph draws has finite support. With the prescribed ties every finite-time intrinsic shape law is finitely supported, hence singular to nonatomic Haar. There is no $f_i=d\mu_i/dm_r$ even at the terminal step. Cauchy–Schwarz would bound the short-minimum probability under an actual density by $\|f_i\|_2(c^r/(2\zeta(r)))^{1/2}$ by primitive Siegel, but cannot be invoked for this law. A possible replacement is an observable-specific approximation with a proved error for this terminal event, or direct averaging of Part 109's layer test over penultimate marked states. No such error or average is established here. [Part 109](wall1_terminal_mixing.md)

For $m=511,n=512,q=3329$, the strongest terminal certificates from the supplied notes already spend zero of the 1% budget. The entries are lower thresholds $c$ in the tested lattice's own GH units, with strict failure event $\lambda_1<c\,G_d\det(L_{\rm tested})^{1/d}$.

| Width | Last window | Retained quotient |
|---:|---:|---:|
| 406 | $8.66605\,10^{-6}$ | $8.54005\,10^{-6}$ |
| 506 | $5.27489\,10^{-6}$ | $5.21484\,10^{-6}$ |

These are Part 110's pathwise bounds obtained by coupling terminal covolume to the run of subunit selections. The Hecke argument yields no improved unconditional 1% threshold. [Part 110, terminal run and interval verification](wall1_additive_tour.md)

## Interval checks

Run from the repository root. The last two lines rerun the source note's interval proof for all four table entries.

```python
from pathlib import Path
from mpmath import iv

iv.dps = 60
q = 3329
B = 2 * iv.sqrt(q) / (q + 1)
assert iv.mpf('0.03465') < B < iv.mpf('0.03466')
assert iv.sqrt(2) * B < iv.mpf('0.05')
for b in (406, 506):
    r = b - 1
    degree = (q**b - 1) // (q - 1)
    assert 0 < q * (degree - q**r) < degree
    assert iv.sqrt(2**(b-2)) * B > 1

source = Path('docs/research/wall1_additive_tour.md').read_text()
exec(source.split('```python\n', 1)[1].split('```', 1)[0])
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Hecke norm.** The bound 2√q/(q+1) = 0.034653… holds for d ≥ 3. It follows from COU Thm 1.1 together with Remark (3) after
  Thm 1.7 and §4.7 (GL_d modulo center), with the §5.1 roots. Exactly one PGL_2 spherical factor contributes.
* **Affine chart.** The count is exact: exactly q^{b−1} of the (q^b−1)/(q−1) lines have a representative (a, 1).
* **Singularity.** Parallel primal and dual vectors (qhe and e/h) form a countable union of proper analytic sets, so they are
  Haar-null. The cubic start gives finite support, so f_i does not exist.
* **Terminal certificates.** They are unchanged. All scripts of this note and of Parts 105, 108 and 110 pass.
