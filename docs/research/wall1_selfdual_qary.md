# Primitive sublattice counts in the finite graph ensemble

The tuple identity gives an exact stratified first moment. Its weights are explicit, but evaluating it requires an arithmetic count of rational planes of bounded height. The Haar mean in [Part 86](wall1_dual_pinning.md) does not evaluate that count. There are also two independent issues in interpreting a terminal GS bound: the reduction predicate and the horizontal dimension.

## An exact first moment without basis multiplicities

Let $A$ be uniform in $M_{m,n}(\mathbb F_q)$ for prime $q$, and let $L_A$ be the kernel in $\mathbb Z^{m+n}$ of $(x,y)\mapsto x+Ay\pmod q$. A primitive rank-$r$ sublattice of $L_A$ is uniquely $L_A\cap V$ for a rational $r$-plane $V$. Conversely every such plane contributes one primitive sublattice, since $q\mathbb Z^{m+n}\subset L_A$. Write $S=V\cap\mathbb Z^{m+n}$, $h(V)=\det S$ (Euclidean covolume), and let $(E;F)$ be an integral basis matrix of $S$. Saturation makes its reduction modulo $q$ injective on $\mathbb F_q^r$, by extending the basis to an ambient integral basis.

Set $t=\mathrm{rank}_q F$ and $s=r-t$. Then $U=E(\ker F)$ has dimension $s$. On a complement of $\ker F$, the $t$ columns of $AF$ in an adapted basis are independent uniform vectors of $\mathbb F_q^m$: their arguments under $A$ are independent. Adding the fixed columns of $E$ and projecting modulo $U$ therefore gives a uniform $(m-s)\times t$ matrix. Consequently $\mathrm{rank}_q(E+AF)=s+j$, where $j$ has the rank distribution of that matrix. The kernel index in $S$ is exactly $q^{s+j}$. This incorporates all rank defects, including the directions whose membership is impossible because their secret residue vanishes. Equivalently the tuple lemma for any fixed columns has weight zero unless $\ker F\subseteq\ker E$, and weight $q^{-mt}$ otherwise. [Part 54](wall1_qary_basis_count.md)

Define $C_t(B)=\#\{V:h(V)\le B,\ \mathrm{rank}_q F=t\}$ over rational $r$-planes. This is finite since the primitive integral Plücker coordinate vector has Euclidean norm $h(V)$ and determines $V$ up to the immaterial sign of the vector. For physical cap $D$, the expected count is exactly
$$
\sum_{t=\max(0,r-m)}^{\min(n,r)}\ \sum_{j=0}^{\min(m-s,t)}
 C_t(D/q^{s+j})\,
 q^{-(m-s)t}
 \prod_{i=0}^{j-1}\frac{(q^{m-s}-q^i)(q^t-q^i)}{q^j-q^i},
 \qquad s=r-t .
$$
Indeed the product counts rank-$j$ matrices by factoring into two full-rank matrices and dividing by the number of changes of intermediate basis. Linearity of expectation needs no independence between planes. This formulation counts sublattices primitive *in the random lattice*, including ones of nontrivial index in their ambient saturation. A numerical first-moment certificate still requires a proved upper bound on the weighted sum at the indicated cap. Substituting the Haar integral, or summing over unrestricted ordered bases, does not supply one.

## Units, dimensions and quantifiers

For the graph ensemble the length unit is $a=3329^{511/1023}$ and a normalized rank-$r$ cap scales by $a^r$. The table converts the reported Haar radii arithmetically. The last three columns reproduce or evaluate the comparisons in [Part 58](wall1_height_union_fix.md). Its width includes the embedding height, while Part 86 uses a horizontal width.

| Width label | Part 86 Haar GS radius in physical units | Part 58 low-height cutoff | Part 58 all-height cutoff (rounded) | Part 58 GSA heuristic |
|---:|---:|---:|---:|---:|
|406|7.27376–7.27377|54.66260–54.66261|742.31|24.73|
|506|21.00574–21.00575|60.39867–60.39868|909.59|54.82|

The following exact integer interval checks certify the conversion and low-height columns.

```python
from fractions import Fraction as Q
for rho, lo, hi, h, u, v in [
    ('0.12656799', '7.27376', '7.27377', 747, '54.66260', '54.66261'),
    ('0.36551297', '21.00574', '21.00575', 912, '60.39867', '60.39868'),
]:
    assert (Q(lo)/Q(rho))**1023 < 3329**511 < (Q(hi)/Q(rho))**1023
    assert Q(u)**2 < 4*h < Q(v)**2
```

Even a hypothetical transfer of the stated Haar numbers would leave them below the listed low-height cutoffs. A like-for-like comparison for embedded widths 406 and 506 would require horizontal suffix ranks 405 and 505 and prefix indices $N-405$ and $N-505$. Furthermore a suffix basis always gives $\lambda_1(H)\le g_k$ by taking its projected head. Equality in [Part 48](wall1_null_terminal.md) uses a primal shortest-head test on that very suffix. Part 86's recursive Micciancio–Walter proof bounds the original GS length and permits basis changes in its recursive witnesses. The proof supplies no corresponding equality for the original suffix.

There is a deterministic obstruction to a uniform lower bound on all prefix heights under the recursive predicate. Apply the unimodular replacement $v_0\gets v_0+M v_1$ in the first block. It fixes the block lattice, its last reciprocal vector (for width at least three), and the availability of the same recursive witness after a first-block basis change. Its first two vectors span the same area, while its first length tends to infinity. Hence $g_1$ tends to zero on the same lattice. Both prefixes in question contain this index. A probabilistic claim about a particular implementation's chosen flags would need another argument. In particular the sufficient prefix minima near 12 and 25 in the [Part 47 audit](wall1_decoupled.md) do not follow from Definition 1.

Neither width acquires a low-height, all-height, or lifting certificate from this argument. Conditional plant independence from Part 47 still applies. The first moment above has not been bounded numerically here for the Part 86 caps. The [recorded frontier](../PROOF_GAP.md) remains Part 39's dimension-647 exact SVP call at 99%, with its runtime unproved. That is a separate construction. No end-to-end block size for the decoupled construction follows from this comparison.

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Verified.** The exact index q^{s+j}, including boundary cases. An exhaustive check of the rank law for small q. The Fraction
  script. The cutoffs, which lie in [742.30401, 742.30403] and [909.58568, 909.58569].
* **Correction.** "With its runtime unproved" is too broad. Part 39 has a deterministic worst-case Õ(4^647) bound
  (Micciancio–Voulgaris). What is unproved is a sieve-scale runtime on these instances.
