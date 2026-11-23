# The proposed exponent 15 and the two terminal residuals

**Finding.** Part 187 chose $q^{15}$ as a loss that the earlier $4\cdot10^{-7}$ budget could afford. Part 190 still states the corresponding finite-to-Haar inequality as a conjecture. At the audited determinant floor refining the Haar spacing calculation can improve its upper bound by a factor smaller than $1+2.37\cdot10^{-13}$. The horizontal residual requires a terminal **area** hit. Under Haar at that floor, more than 99.995% of area hits have spacing above 26. Neither residual ceiling follows. The numerical gaps below apply to a comparison evaluated at the determinant floor. The actual distortion on gated histories remains unknown. [Part 186](wall1_quotient_slack.md#audit) · [Part 187](wall1_local_comparison.md#audit) · [Part 190](wall1_rank2_transverse.md#audit)

## Origin of the exponent and the exact subgroup order

Write $q=3329$, $D_*=\exp L_{406}$, and let $E$ be the radius-26 shortest-line quotient event for the retained rank-505 lattice after draw 406. Part 186 obtained a physical Haar upper bound $B(D_*)\in(3.3366580972102,3.3366580972103)\cdot10^{-60}$. Thus
$$
  15.06928 < \log_q\big(4\cdot10^{-7}/B(D_*)\big)<15.06929.
$$
Choosing the integer exponent 15 spent less than that allowance. Part 190 kept this choice in its Eq. (5), whose left side is the selected finite mass of $E\cap G$, with $G$ the raw-minimum and dual-floor gates. Its reference is the Haar probability averaged over the actual terminal determinant. The equation also allows an additive charge. There is no loss of 15 powers in the derivation of the marked transition or a union over candidate blocks to undo. [Part 187, physical budget](wall1_local_comparison.md#audit) · [Part 190, Eq. (5)](wall1_rank2_transverse.md)

**Exact index on a realized history.** At time $i$, use its raw graph $L=\ker\sigma\subset\mathbb Z^N$, where the syndrome $\sigma$ surjects onto $V=\mathbb F_q^{400}$. Let $F$ be its rational frozen space, $S=F\cap\mathbb Z^N$, $P$ orthogonal projection off $F$, $M=PL$ and $T=\operatorname{span}(M)/M$. If $d=400-\dim_{\mathbb F_q}\sigma(S)$, then
$$
 H=P\mathbb Z^N/M\simeq V/\sigma(S),\qquad
 |H|=q^d=\det M\,\det S,\qquad [T[q]:H]=q^{505-d}.
$$
Indeed horizontal columns represent every syndrome. Projecting two integral vectors identifies their classes modulo $M$ exactly when their difference lies in $L+S$. A basis of the primitive section $S$ extends to an integral basis of $\mathbb Z^N$, whose volume factors into $\det S\,\det(P\mathbb Z^N)=1$. Taking the index of $M$ in that projected lattice proves the determinant identity. Cauchy–Binet gives $(\det S)^2\ge1$ since it is a sum of squared integer minors, at least one nonzero (use volume one in rank zero). This argument applies pointwise even when selection chose $F$. [Part 108, append law](wall1_first_tour.md#filtration-and-append-law) · [Part 200, projected section formula](wall1_hybrid_tail.md)

In particular, the floor gives $110.42215<L_{405}/\log q<110.42216$ before the draw-406 mark, and $109.95553<L_{406}/\log q<109.95554$ afterwards. Thus the incoming group has order **at least $q^{111}$** and the outgoing group at least $q^{110}$. The index inside the full $q$-torsion is at least $q^{105}$ in either case since $d\le400$. The ambient torus has dimension 505, and each fresh raw column has 400 field coordinates. None of these quantities accounts for 15. At a positive-height winner of height $k$ coprime to $q$, the order is even preserved. Indeed if $v=(\lambda+k\tilde u,k)$, then an old class killed by projection must be represented modulo $M$ by an integer multiple of $\lambda/k$, by equating fresh coordinates in $\mathbb Rv+W_u$. Its order divides $k$, and a killed mark also has order dividing $q$. This covers all heights 1 through 12 in the vertical residual. [Part 176, inverse branch](wall1_inverse_branch.md) · [Part 193](wall1_z2_vertical.md#audit)

For a fixed incoming raw prefix $p$, every $u\in H_p$ has exactly $q^{400}/|H_p|$ completions by one column. For a residual event $B$, put $w_B(p,u)=\Pr(B\mid p,u)$, including all first-hit, gate and terminal conditions. The exact mass is
$$
 \Pr(B)=\mathbb E_p\left[\frac1{|H_p|}\sum_{u\in H_p} w_B(p,u)\right].
$$
The weight averages over raw columns in the fiber as necessary. The uniform mark law is for the original prefix before imposing any further gate. Conditional on an additional event, the mark probabilities are proportional to its fiber weights. Computing the exact order fixes the denominator but gives no upper bound on the average of these weights below one. Part 187's local factor $|H|/k_S$, where $k_S$ marks pass a test, compares a pinned **finite** branch to a product of finite marginals. It supplies no Haar denominator. Similarly, the gated index $[C:P][P:B]\ge1893$ in Part 206 counts projection and section cosets of a physical plane. Turning it into a probability divisor would require a bound on how the successful histories occupy equally weighted fibers. Finite support also precludes a multiplicative comparison on all shape events, including after conditioning on any positive-mass subset of histories. That singularity leaves comparison on one threshold open. [Part 188](wall1_state_counting.md) · [Part 205](wall1_doubly_gated.md) · [Part 206](wall1_raw_section_compression.md#audit)

## What an exact Haar count can change

Let $A=\{a_2(M)\le1352/\sqrt3\}$. Write $e(D)$ and $p(D)$ for the Haar probabilities of $E$ and $A$ at physical determinant $D$. The audited endpoints are
$$
\begin{aligned}
 e_-&=9.97119357603428\cdot10^{-63}<e(D_*)<9.97119357603664\cdot10^{-63}=e_+,\\
 p_-&=2.0005903166\cdot10^{-58}<p(D_*)<2.0717836951\cdot10^{-58}=p_+.
\end{aligned}
$$
Part 190 counts primitive planes using binary reduction, then obtains its lower bound by retaining only planes whose outer quotient minimum exceeds $52/\sqrt3$. On these planes the marked shortest line wins in the parent and the internal witness plane is unique. Hence even an exact restriction to the actual shortest line and removal of all multiple counting can improve the spacing upper endpoint by a factor of at most $e_+/e_-<1+2.37\cdot10^{-13}$. For area, the exact single-plane mean already uses the primitive rank-two constant. The probability enclosure additionally controls multiplicities. An exact area probability can improve its audited upper endpoint by at most $p_+/p_-<1.03559$. [Part 190, Theorem 2 and audit](wall1_rank2_transverse.md) · [Part 192, probability and multiplicities](wall1_rank2_tail.md#haar-probability-and-multiplicities) · [Kim, sublattice mean values](https://arxiv.org/abs/2005.10874)

The implication is $E\subset A$. If $s$ is the designated shortest length and a shortest quotient witness has length $h\le26$, its rounded lift has squared length at most $h^2+s^2/4$ and at least $s^2$. Its plane therefore has area $sh\le2h^2/\sqrt3$. Consequently
$$
 \Pr_{D_*}(A\setminus E)>p_--e_+>2.00049\cdot10^{-58},\qquad
 \Pr_{D_*}(E^c\mid A)>1-e_+/p_->0.99995015.
$$
Even requiring just that an area witness contain the actual shortest line can discard all witnesses. Take the orthogonal sum of a length-28 line, a triangular lattice of side 29, and $40\mathbb Z^{502}$. The triangular factor is saturated and has area $29^2\sqrt3/2<1352/\sqrt3$. The first line is uniquely shortest. Every saturated plane through it has area at least $28\cdot29=812>1352/\sqrt3$, by the quotient minimum. This example concerns the geometric implication. The two-window example in the terminal-law note additionally attains $A\cap E^c$ with consecutive horizontal selections and replacement of the first hit plane. Neither example establishes a positive mass on eligible doubly gated prefixes. [Two-window example](wall1_z1_terminal_law.md#two-horizontal-wins-and-a-replacement-plane)

## Absolute budgets and the unresolved finite mass

Let $b_H=7.1275\cdot10^{-11}$ apply to the horizontal remainder after charging draws 155–171. Let $b_V=6.485\cdot10^{-11}$ apply to $Z_{\rm rem}$ after charging the controlled vertical cases. The full $Z_2$ allocation is $9\cdot10^{-11}$. For a reference upper endpoint $u$, zero additive error and the floor calculation, $q^c u\le b$ exactly when $c\le\log_q(b/u)$. The exponent column rounds **down** to eight decimals. The last column encloses $q^{15}\Pr_{D_*}(\text{observable})/b$ using the two audited endpoints.

| Finite mass budget | Reference observable | Sufficient exponent at floor | Factor over budget at exponent 15 |
|---|---|---:|---:|
| Horizontal remainder | Spacing $E$ | 14.72162705 | (9.56129, 9.56130) |
| Vertical remainder | Spacing $E$ | 14.70997924 | (10.50858, 10.50859) |
| Full $Z_2$ | Spacing $E$ | 14.75038806 | (7.57201, 7.57202) |
| Horizontal remainder | Area $A$ | 13.49584267 | (191835, 198662) |
| Vertical remainder | Area $A$ | 13.48419485 | (210841, 218345) |
| Full $Z_2$ | Area $A$ | 13.52460367 | (151922, 157330) |

At $c=14.72$ the spacing charge is between $7.03406\cdot10^{-11}$ and $7.03407\cdot10^{-11}$. Charging this floor value to the horizontal spacing portion under a hypothetical zero-error comparison would leave about $9.344\cdot10^{-13}$ for the horizontal mass on $E^c$. The spacing charge alone already exceeds $b_V$ by a factor greater than 1.08466. It fits the full $Z_2$ allowance only in a direct comparison covering the entire vertical event, including its mass outside $E$. With the actual area observable at $c=14.72$ even the **lower** Haar endpoint exceeds the respective remainder budgets by factors above 19,800 and 21,762. A single upper bound on the whole terminal area mass by $b_V$ would suffice for both remainders by containment. Separate bounds can use their respective history restrictions. [Horizontal allocation](wall1_z1_terminal_law.md) · [Vertical allocation](wall1_z2_vertical.md#audit)

The floor is another possible source of slack. Part 190 gives $e(D)\le K(D_*)(D_*/D)^2$, with $K(D_*)<e_+$. Even at exponent 15, a proof that $\mathbb E[(D_*/D)^2]\le0.10458831$ would fit the *spacing reference term* inside $b_H$. For $b_V$, $0.09516032$ suffices. The deterministic floor gives only an upper bound of one on that expectation. The lower Haar endpoints used above apply at $D_*$ only. They impose no lower bound of these sizes on the finite law or on its determinant-matched Haar average. [Part 190, determinant dependence](wall1_rank2_transverse.md) · [Part 192, determinant weight](wall1_rank2_tail.md)

**Completeness.** The irreducible gaps quantified here are for sharpening the Haar endpoints at the audited floor. On the finite side the undetermined quantity is the prefix-weighted fraction of completions passing both gates, the appropriate first-hit tests, and the terminal area test. Following a single first-hit plane would also need to account for a terminal replacement after its projection loses rank. The only general upper bound from group cardinality and $0\le w_B\le1$ alone is one, over $1.40\cdot10^{10}$ times $b_H$ and $1.54\cdot10^{10}$ times $b_V$. This is a gap in those bounds. No lower bound contradicting either residual target has been established.

## Numerical verification

From `docs/research/scripts/` run `python -B wall1_z1_terminal_law.py` for the existing two-window and budget checks. Run the following script from the same directory with `sed -n '/^\x60\x60\x60python$/,/^\x60\x60\x60$/p' ../wall1_distortion_sharpening.md | sed '1d;$d' | python -B -`. It takes the audited Haar enclosures as inputs and uses outward interval arithmetic.

```python
from mpmath import iv

iv.dps = 70
R = iv.mpf
q = R(3329)
logq = iv.ln(q)
B = R(["3.3366580972102e-60", "3.3366580972103e-60"])
assert R("15.06928") < iv.ln(R("4e-7") / B) / logq < R("15.06929")

L = 400 * logq
for i in range(1, 407):
    period = L - logq
    hermite = 505 * L / 506 - iv.ln(R("56.2142")) / 2
    assert period < hermite or hermite < period
    L = max(period, hermite)
    if i == 405:
        assert R("110.42215") < L / logq < R("110.42216")
assert R("109.95553") < L / logq < R("109.95554")

spacing = R(["9.97119357603428e-63", "9.97119357603664e-63"])
area = R(["2.0005903166e-58", "2.0717836951e-58"])
assert spacing.b / spacing.a - 1 < R("2.37e-13")
assert area.b / area.a < R("1.03559")
assert area - spacing > R("2.00049e-58")
assert 1 - spacing / area > R("0.99995015")
assert 29**2 * 3 < 2 * 1352 and 812**2 * 3 > 1352**2

horizontal = R("7.6330e-11") - R("5.055e-12")
vertical = R("9e-11") - R("2.515e-11")
full = R("9e-11")
rows = [
    (horizontal, spacing, "14.72162705", "9.56129", "9.56130"),
    (vertical, spacing, "14.70997924", "10.50858", "10.50859"),
    (full, spacing, "14.75038806", "7.57201", "7.57202"),
    (horizontal, area, "13.49584267", "191835", "198662"),
    (vertical, area, "13.48419485", "210841", "218345"),
    (full, area, "13.52460367", "151922", "157330"),
]
for budget, prob, exponent, lo, hi in rows:
    c = iv.ln(budget / prob.b) / logq
    assert R(exponent) < c < R(exponent) + R("1e-8")
    assert R(lo) < q**15 * prob / budget < R(hi)

factor = q**R("14.72")
charge = factor * spacing
assert R("7.03406e-11") < charge < R("7.03407e-11")
assert R("9.3437e-13") < horizontal - charge < R("9.3438e-13")
assert charge / vertical > R("1.08466")
assert factor * area / horizontal > 19800 and factor * area / vertical > 21762
assert q**15 * spacing.b * R("0.10458831") < horizontal
assert q**15 * spacing.b * R("0.09516032") < vertical
assert 1 / horizontal > R("1.40e10") and 1 / vertical > R("1.54e10")
print("All subgroup-floor and Haar budget enclosures passed.")
```

## Audit

**Verdict — CONFIRMED for all five claims.** Both verifiers in the preceding section passed. An independent 95-decimal-digit evaluation of the formulas in Parts 186, 190 and 192 also reproduced the quoted floor enclosures.

1. Part 186 supplies the physical budget exponent $15.069284388273\ldots$. Part 187 rounds it down to the integer 15. Part 190 explicitly labels Eq. (5) a sufficient comparison conjecture and retains both the actual determinant average and an additive allowance.
2. For each realized prefix, the map $z\mapsto Pz+M$ on $\mathbb Z^N$ has kernel $L+S$, so its image has exactly $q^{400-\dim\sigma(S)}$ elements. The volume identity gives $q^d=\det M\det S\ge\det M$. Immediately before draw 406, $L_{405}/\log q=110.422154884389\ldots$, so the integer $d$ is at least 111. This counts distinct incoming marks before conditioning on the gates.
3. The two spacing endpoints give $e_+/e_- -1=2.366817956149\ldots\cdot10^{-13}$. This bounds the relative gain from replacing the audited upper endpoint by the exact Haar probability at $D_*$.
4. Since $E\subseteq A$, the fraction of Haar area hits with spacing above 26 is exactly $1-e(D_*)/p(D_*)$. Substitution of $e_+$ and $p_-$ gives a strict lower bound above $99.99501587\%$.
5. Using the upper endpoints in $\log_q(b/u)$ gives $14.721627059394\ldots$ and $14.709979248339\ldots$ for spacing, and $13.495842670374\ldots$ and $13.484194859319\ldots$ for area, in horizontal then vertical order. All four eight-decimal round-downs and both full-$Z_2$ rows agree with the table.

The closing sentence of the Part 208 entry in the proof-gap index needs the spacing qualification. At exponent 14.72 the horizontal spacing charge fits its allowance, but a terminal area hit can have spacing above 26. Part 208's two-window example illustrates this distinction and its audit establishes that the example has zero restart probability. The finite mass of the gated residuals remains open. [Proof-gap index, Part 208](../PROOF_GAP.md) · [Part 208 audit](wall1_z1_terminal_law.md#audit)
