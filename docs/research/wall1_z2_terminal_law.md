# Terminal plane counts under determinant conditioning

The unconditional Haar second moment of the primitive-plane count is **infinite** at every positive area cutoff and every determinant in the ranks relevant here. In rank 505, imposing a lower cutoff \$b\$ on the length of the common primitive line makes the intersecting-pair term finite and exactly proportional to \$b^{-501}\$. This identifies the missing term in a calculation based on independent pairs. There is a separate obstruction on the finite-law side. Even the *scalar* least plane area has total variation distance one from its determinant-matched Haar law on every positive-mass determinant profile. These facts leave the vertical residual open.

The retained rank is 505, the window rank is 506, and the raw rank at draw 406 is 911. In Part 193's notation, the requested allowance of \$6.485\\cdot10^{-11}\$ applies to \$Z_{\\rm rem}\$. It includes first vertical hits on draws 396–406 with \$1\\le k\\le12\$, \$\\max(30.5,0.945g)<s\\le2^{1/4}\\sqrt a\$, both gates, and a hit at draw 406. The first hit can precede 406 even if the plane witnessing it disappears. Part 193 separately charges \$Z_2-Z_{\\rm rem}<2.515\\cdot10^{-11}\$. [Part 193, audit](wall1_z2_vertical.md#audit) · [Parts 183–206 and frontier](../PROOF_GAP.md)

## The term omitted by the independent-plane formula

Let \$N_a\$ count unoriented saturated rank-two sublattices of area at most \$a>0\$ in a Haar lattice of rank \$n\\ge5\$ and physical covolume \$D>0\$. Write \$V_j\$ for unit ball volume, \$c_j=V_j/(2\\zeta(j))\$, and \$U=\\mathbb E N_a\$. Let \$I_b\$ count **ordered** pairs of distinct qualifying planes meeting in a line whose primitive generator has length at least \$b>0\$.

**Lemma 1.** The expected number of ordered pairs meeting only at zero is \$U^2\$. The expected intersecting-pair count with cutoff is
\$$
 \\mathbb E I_b =
 \\frac{n c_n c_{n-1}^2 a^{2n-2}}{(n-4)D^3}\\,b^{4-n}.
\$$
In particular \$\\mathbb E[N_a(N_a-1)]=\\infty\$. The divergence and its origin are Kim's Theorem 4. The displayed coefficient specializes the intersection calculation to physical scale and counts each unoriented line once. [Kim, Theorems 3–4 and the integral in §4](https://arxiv.org/pdf/2005.10874)

**Proof.** Kim's independent-sublattice formula with ranks \$(2,2)\$ gives the first assertion since \$4<n\$. An intersecting pair determines its unique saturated common line. Unfold over such lines of length \$r\$. Their intensity is \$n c_n r^{n-1}dr/D\$, and their orthogonal quotient has Haar shape and covolume \$D/r\$ under the unfolded measure. A plane through this line corresponds bijectively to a primitive line in the quotient by taking its full preimage. Its area is \$r\$ times the quotient line length. Thus the quotient cutoff is \$a/r\$. Two distinct primitive quotient lines are independent, and Kim's formula in rank \$n-1\$ gives their ordered count in expectation as
\$$
 \\left(\\frac{c_{n-1}(a/r)^{n-1}}{D/r}\\right)^2 .
\$$
Multiplication by the line intensity leaves the power \$r^{3-n}dr\$. Its integral from \$b\$ to infinity is \$b^{4-n}/(n-4)\$. Sending \$b\$ down to zero and applying monotone convergence proves divergence. No choice of lift shear enters the area of a plane containing the marked line. [Kim, quotient disintegration, Lemma 10](https://arxiv.org/pdf/2005.10874)

For the Part 192 determinant floor \$D_*\$ at draw 406, \$n=505\$, and \$a=1352/\\sqrt3\$, the common-line length has the following effect on the *Haar* count. The denominator in the last column counts all ordered disjoint pairs at this floor. [Part 192, Haar calculation](wall1_rank2_tail.md#haar-probability-and-multiplicities)

| Common-line cutoff | Expected ordered intersecting pairs above cutoff | Ratio to \$U^2\$ |
|---|---:|---:|
| \$26\$ | \$(6.6216,6.6218)\\cdot10^{-74}\$ | \$(1.1342,1.1343)\\cdot10^{41}\$ |
| \$30.5\\sqrt3/2\$ | \$(2.4296,2.4298)\\cdot10^{-77}\$ | \$(4.1618,4.1620)\\cdot10^{37}\$ |

The second cutoff has a geometric interpretation at a first hit. After projecting off a shortest window vector of length \$s\$, every nonzero quotient point lifts with parallel component of magnitude at most \$s/2\$. That lift has length at least \$s\$, giving quotient minimum at least \$s\\sqrt3/2\$. On the residual band this exceeds the second cutoff. Hence an indicator of that minimum gate times the intersecting-pair count is bounded by \$I_b\$ pointwise. The table integrates \$I_b\$ over all Haar lattices. It does not compute the mean conditional on either of the restart's gates. A first hit before draw 406 puts this minimum constraint on the lattice at the first hit.

## What a full determinant profile reveals about the mark

**Lemma 2.** Fix the incoming *raw history* at the last draw, and let \$H\$ be its finite mark group. Write \$s(u)\$ for the length selected by mark \$u\$, using the prescribed tie rule, and \$D\$ for the incoming covolume. For a possible outgoing determinant \$d\$, define
\$$
 B_d=\\{u\\in H:s(u)=D/d\\}.
\$$
Given this history and \$d\$, the mark is uniform on \$B_d\$. Its total variation distance from uniform on \$H\$ equals \$1-|B_d|/|H|\$. More generally, let \$J\$ be any event involving the gates or history and put \$w(u)=\\Pr(J\\mid\\text{history},u)\$. Given this history, \$d\$, and \$J\$, the mark probabilities are
\$$
 \\Pr(u\\mid\\text{history},d,J)
 =\\frac{\\mathbf1_{B_d}(u)w(u)}{\\sum_{v\\in B_d} w(v)}
\$$
whenever the denominator is positive.

**Proof.** Part 108 gives equal incoming mass to each mark and the determinant update \$d=D/s(u)\$. Restriction to this level set gives the first assertion. The mass excluded from uniform on \$H\$ is exactly its total variation distance from the restricted uniform law. Multiplying each mass by its conditional probability of \$J\$ and normalizing proves the last identity. Conditioning only on a profile through 406 further averages this expression over the *posterior* incoming histories. Raw histories can differ even at a fixed incoming determinant. [Part 108, marked law](wall1_first_tour.md) · [Part 193, same-mark selection](wall1_z2_vertical.md)

**Lemma 3.** Fix any positive-probability full determinant profile of the finite matrix experiment, optionally restricted to a positive-probability gate event on that profile. Let \$X\$ be the least saturated plane area of its terminal output. Let \$Y\$ be the same observable in a Haar lattice at the profile's terminal determinant. Then \$d_{\\rm TV}(X,Y)=1\$. The conclusion also holds after restricting the Haar law to a measurable event of positive Haar probability.

**Proof.** There are finitely many raw designs, so the conditional law of \$X\$ has finite support \$S\$. At fixed determinant the squared area for any primitive integer rank-two frame is a nonconstant real-analytic function of the ambient positive-definite metric. At any such metric one can contract the frame's plane isometrically up to scale and expand the orthogonal complement to preserve determinant. Thus every fixed level set has measure zero in smooth Haar coordinates. There are countably many frames. The least area is attained by discreteness in the exterior-square lattice, so \$\\Pr(Y\\in S)=0\$. Restriction to a positive-measure event preserves null sets. Taking \$S\$ as the total variation test gives equality. The same argument works for the scalar observable even though the test forgets the rest of the shape. [Part 108, finite-time law](wall1_first_tour.md) · [Part 192, plane area level sets](wall1_rank2_tail.md#haar-probability-and-multiplicities)

An additive comparison using this total variation distance costs exactly one, over \$1.54\\cdot10^{10}\$ times the entire residual allowance. This loss belongs to the supremum over measurable tests. It gives no lower bound for the discrepancy at the particular threshold \$a\$. Likewise, a finite gated second moment under Haar would bound an integral under that reference measure. Transferring it requires the actual profile-weighted probability that a qualifying plane occurs on the selected, doubly-gated histories. Neither comparison supplies this quantity. The bound \$Z_{\\rm rem}\\le6.485\\cdot10^{-11}\$ remains open.

## Reproducing the enclosures

Run the embedded Python script from `docs/research/scripts/` with
`sed -n '/^```python$/,/^```$/p' ../wall1_z2_terminal_law.md | sed '1d;$d' | python -`.
It uses outward interval arithmetic for the Part 193 recurrence and the constants in Lemma 1. The elementary integral test gives \$1<\\zeta(j)\\le1+2^{-j}+2^{1-j}/(j-1)\$.

```python
from mpmath import iv

iv.dps = 80
R = iv.mpf
n = 505
vol = [R(1), R(2)]
for j in range(2, n + 1):
    vol.append(2 * iv.pi * vol[j - 2] / j)

def zeta_bound(j):
    excess = R(2)**(-j) + R(2)**(1-j) / (j-1)
    return R(1) + R([0, 1]) * excess

def line_constant(j):
    return vol[j] / (2 * zeta_bound(j))

log_q = iv.ln(3329)
log_det = 400 * log_q
for _ in range(406):
    period = log_det - log_q
    hermite = 505 * log_det / 506 - iv.ln(R("56.2142")) / 2
    assert period > hermite or hermite > period
    log_det = max(period, hermite)

D = iv.exp(log_det)
a = 1352 / iv.sqrt(3)
U = (n-1) * iv.pi * line_constant(n) * line_constant(n-1) * a**n / (6 * D**2)
assert R("7.64065e-58") < U < R("7.64066e-58")
coefficient = n * line_constant(n) * (line_constant(n-1) * a**(n-1))**2
rows = [
    (R(26), "6.6216e-74", "6.6218e-74", "1.1342e41", "1.1343e41"),
    (R("30.5") * iv.sqrt(3) / 2, "2.4296e-77", "2.4298e-77", "4.1618e37", "4.1620e37"),
]
for b, low, high, ratio_low, ratio_high in rows:
    pairs = coefficient * b**(4-n) / ((n-4) * D**3)
    assert R(low) < pairs < R(high)
    assert R(ratio_low) < pairs / U**2 < R(ratio_high)
assert R("1.54e10") * R("6.485e-11") < 1
print("All interval checks passed.")
```

## Audit

**Verdict — CONFIRMED for all three lemmas and both numerical rows.** The only correction is typographical. The body escapes its dollar delimiters and doubles TeX command backslashes. Use the same math delimiters and single command backslashes as in the Part 193 note.

**Lemma 1.** Kim's Theorem 3 applies to ranks $(2,2)$ in dimension $n$ and $(1,1)$ in dimension $n-1$ for every $n\ge5$. Theorem 4 applies with intersection rank one. Each ordered intersecting pair determines one unoriented common line. Its length intensity is $n c_n r^{n-1}\,dr/D$. The quotient covolume $D/r$ and area cutoff $a/r$ give a factor $c_{n-1}^2 a^{2n-2}r^{4-2n}/D^2$ for its ordered pair of quotient lines. The resulting integral of $r^{3-n}$ gives the stated coefficient and diverges at zero. The unrestricted factorial and ordinary second moments are therefore both infinite. [Kim, Theorems 3–4 and §4](https://arxiv.org/pdf/2005.10874)

The embedded interval script passed every assertion. An independent 210-digit calculation iterated the floor in physical covolumes and evaluated Kim's constants using gamma and zeta functions. The period branch was active 20 times and the Hermite branch 386 times, giving $\log D_*=891.786365038306\ldots$ and $U^2=5.83796212510\ldots\times10^{-115}$. At $b=26$ the intersecting count was $6.62167719406\ldots\times10^{-74}$. At $b=30.5\sqrt3/2$ it was $2.42968149575\ldots\times10^{-77}$, or $4.16186580812\ldots\times10^{37}$ times the ordered disjoint count. Both ratios fall inside the reported intervals. [Part 192, determinant floor and mean](wall1_rank2_tail.md#audit)

**Lemma 2.** At a fixed raw prefix, each mark has the same prior mass. The determinant update selects precisely the fiber $B_d$. The gate then weights each member by $w(u)$, giving the displayed posterior whenever its normalizing sum is positive. The TV formula follows by testing $B_d$ itself. [Part 108, marked kernel](wall1_first_tour.md)

**Lemma 3.** There is also a direct check of atomlessness. At fixed $D$, the Haar mean $\mathbb E N_t=a(n,2)t^n/D^2$ is continuous in $t$. Hence the expected count of planes of area exactly $t>0$ is zero, by taking increasing cutoffs below $t$. The least area is attained, so it too has zero mass at every such $t$. The finite chain's conditional support has probability one for the chain and zero for Haar, including after a positive-probability Haar restriction. This proves scalar TV distance one on every positive-mass profile. [Kim, Theorem 3](https://arxiv.org/pdf/2005.10874)

The separating TV test is the finite support. It gives no lower bound on the discrepancy for the single area threshold $a$. The geometric length cutoff applies to the output at the first hit, which can precede draw 406. The Haar pair integral supplies no estimate of the chain's joint mass with both gates and a terminal hit. Part 193's $6.485\times10^{-11}$ bound for $Z_{\rm rem}$ remains open. [Part 193, residual event](wall1_z2_vertical.md#audit)
