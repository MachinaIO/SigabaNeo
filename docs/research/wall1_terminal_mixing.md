# The last full window of the first forward tour

For the inherited, exact, no-lookahead tour with the horizontal $qI$ first, the following constants give **zero** probability of a strict lower-tail violation. Each length is divided by the Gaussian heuristic of the indicated lattice itself. The stronger question of a near-GH 1% quantile remains open.

| Width | Last full window | Quotient by its selected shortest vector |
|---:|---:|---:|
| 406 | $6.4758\,10^{-8}$ | $6.4843\,10^{-8}$ |
| 506 | $3.3322\,10^{-8}$ | $3.3357\,10^{-8}$ |

There are two reasons to distinguish this certificate from a mixing estimate. A string of subunit minima has a deterministic geometric constraint that improves the earlier $2.7554\,10^{-37}$ floor. Conversely, even the largest possible displacement subgroup admits a reachable penultimate state on which **every** final draw has ratio below 0.21, at both output ranks. The probability of visiting that state is tiny. The obstruction is to a history-uniform near-GH estimate, and gives no comparable upper bound on the unconditional quantile.

## Which block is tested?

Write $N=m+n=1023$, $r=b-1$, and $G_d=V_d^{-1/d}$ for the unit-ball volume $V_d$. Freeze one direction per call, preserve the integral window span, and fix a deterministic tie rule. At the last append all 512 graph columns have entered. Just before the last SVP, the projected window $W$ is the entire remaining lattice of rank $b$, with $N-b$ directions frozen. In one-based indexing it starts at 618 or 518 and ends at 1023. The call gives $s=\lambda_1(W)$, and the new retained lattice $QW$ has rank 405 or 505. Reducing a shorter tail internally preserves the integral span of this last full block modulo its fixed prefix. A later tour can change the prefix. These statements use the input and filtration of [the first-tour recursion](wall1_first_tour.md).

## A pathwise lower bound from consecutive subunit selections

Put $\alpha=\sqrt3/2$. After projecting off a shortest vector of length $a$, every nonzero quotient vector has length at least $\alpha a$, by lifting and rounding its parallel component to at most $a/2$. In the graph phase, appending a column can introduce only vectors with perpendicular component a nonzero integer or vectors already in the retained lattice. Thus the first selected length below one in any consecutive run of such lengths is at least $\alpha$. This also holds if the final observation is the minimum of the retained quotient, treated as one extra selection without an append. The initial cubic retained minimum is $q$.

A run of subunit lengths $a_1,\ldots,a_h$ comes entirely from the rank-$r$ retained lattice immediately before its first append. Indeed the new coordinate at that append is integral, so the first selected vector lies in the old span. Inductively the removed directions lie in this same original span. Projection off them leaves every newer vertical coordinate intact. In any combination using newer columns, the last used new coordinate is a nonzero integer. Hence every subunit selection lies in the projected old lattice, and $h\le r$. If the run starts at the extra selection without an append, take the current retained lattice. Within the run the selected vector is shortest also in the projected old lattice, since that lattice is contained in the current window and contains the minimizer.

Consider the last $k$ selections of the run beginning with $a_i$, $i=h-k+1$. In the lattice at step $i$ lift the subsequent selected vectors successively through the earlier projections. The resulting $k$ independent vectors span an integral sublattice with covolume $\prod_{j=i}^h a_j$ in its span, by Gram–Schmidt. Its minimum is at least $a_i$. The Hermite inequality with upper constant $\gamma_k$ therefore gives
$$
a_i^{k-1}\le \gamma_k^{k/2}\prod_{j=i+1}^h a_j .
$$
This uses only lifts from the same old lattice. Applying the inequality across arbitrary earlier windows without that inclusion would be unjustified.

Set $A_1=0$ and bound $\log(a_{h-k+1}/a_h)$ by
$$
A_k=\min\left\{A_{k-1}-\log\alpha,\frac{(k/2)\log\gamma_k+\sum_{j<k} A_j}{k-1}\right\}.
$$
The adjacent bound holds inside the run by the lift argument, since each new subunit minimizer belongs to the previous quotient. Use $\gamma_2=2/\sqrt3$ and Blichfeldt's upper bound $\gamma_k=(2/\pi)\Gamma(2+k/2)^{2/k}$ for $k\ge3$. One direct proof of the latter scales the minimum to one and integrates $f(x)=(1-2\|x\|^2)_+$. For $t$ lattice translates contributing at a point, the sum of their squared distances from that point is at least $(t-1)/2$, by the pairwise squared-distance identity and unit separation. The sum of translates of $f$ is at most one, so the determinant is at least $\int f=2^{-k/2}V_k/(1+k/2)$.

Every observed minimum $s$ is consequently at least $s_r=\alpha\exp(-\max_{k\le r}A_k)$, also when $s\ge1$. To convert to own-GH units, the full graph lattice contains $q\mathbb Z^N$ (multiply graph columns by $q$ and subtract horizontal periods). Its orthogonal image contains the projected $q$-axes, of lengths at most $q$, spanning the terminal space. Extend a shortest vector to a real basis using $d-1$ such vectors. The covolume of their integral span is at most $s q^{d-1}$ by Hadamard, and is an integer multiple of the terminal determinant. At either rank $d$ this proves the tabulated lower bound by rounding down
$$
G_d^{-1}(s_r/q)^{1-1/d}.
$$
The same proof applies at a graph-phase prefix using its used coordinates. No probability budget is spent on previous windows.

## Exact last-step count and the obstruction to uniform refresh

Given the penultimate state $(\Lambda,H)$ of rank $r$ and determinant $D$, let $U$ be uniform on its marked subgroup. The height-one extension $W(U)$ has determinant $D$ for every draw. For radius $R=cG_bD^{1/b}$, the conditional failure probability equals one if $\lambda_1(\Lambda)<R$. Otherwise it is exactly
$$
\frac{1}{|H|}\#\bigcup_{1\le k<R}
 \{u\in H:\operatorname{dist}(ku,\Lambda)<\sqrt{R^2-k^2}\},
$$
where distance is evaluated using a torus representative. Positive layers suffice by sign symmetry. The union is in the **same** draw space for every layer. To count all short vectors instead, put $L_k=\Lambda+\mathrm{lifts}(kH)$ (the full preimage of $kH$). The expected number in positive layer $k$ is
$$
\frac{\#(L_k\cap B^\circ_{\sqrt{R^2-k^2}})}{|kH|}.
$$
Each point in the numerator lies in exactly one of the equiprobable cosets. Horizontal nonzero vectors contribute their deterministic count, and negative layers double the positive contribution for a signed count. In particular, if $\rho_k$ is a covering radius of $L_k$, disjoint Voronoi cells give an upper bound $V_r(\sqrt{R^2-k^2}+\rho_k)^r/D$ per positive layer. This identifies a metric spread condition in addition to cardinality. At prime $q$, $kH=H$ unless $q\mid k$, when $kH=0$. The same union bounds quotient failure using $R=(cG_r D^{1/r}/\alpha)^{r/(r+1)}$, since $\det QW=D/s$ and $\lambda_1(QW)\ge\alpha s$. The exact quotient test enumerates $u$, selects $v(u)$ with the specified ties, and tests $QW(u)$ directly.

For exact tracking, represent the horizontal marks by their $q$-multiples modulo $q\Lambda$. In the appended basis the marks become $(C,0)$ in $W/qW$. Quotient by the line of the primitive selected vector $v\bmod q$, then express the surviving marks in an integral quotient basis (complete $v$ unimodularly and drop its coordinate). Thus $\log_q|H|$ starts at $r$ and drops by exactly one iff that line lies in the marked subspace. Carry the projected Gram matrix as well to compute each $L_k$ and its ball counts. This gives a finite rational recursion for the marked geometry on each branch. For a terminal-only probability, propagate all branches through graph draw 511, then average the conditional test at draw 512. In particular no survival conditioning or multiplication of one-step success probabilities is necessary.

A reachable test state shows the limit of this approach. Starting with $\Lambda=q\mathbb Z^r$ and full $H$, take zero displacement in each of the first 511 graph draws. Each selected vector is the new vertical unit up to sign, and both lattice and marks return to their initial values. This history has probability $q^{-511r}$. At draw 512 the determinant of $W$ is $q^r$ and $s\le q$ from the horizontal axes. At least one horizontal axis projects nontrivially into $QW$, so its minimum is also at most $q$, while its determinant is at least $q^{r-1}$. Both ratios are bounded above by $q^{1/d}/G_d$ at the respective ranks. All four upper bounds are below 0.21. Here $L_1=\mathbb Z^r$ is the full regular subdivision of the cube. Even this mark cannot remove inherited short horizontal vectors. More generally, condition on zero displacements until $l$ graph draws remain, with $1\le l<r$. After $j\le l$ additional selections the original horizontal span loses at most $j$ dimensions under projection. Some original horizontal axis still projects nontrivially, with length at most $q$. Each selected length is therefore at most $q$. Dividing the initial determinant $q^r$ by these lengths shows that the last window has determinant at least $q^{r-l+1}$ and its quotient at least $q^{r-l}$. Both terminal ratios are at most $q^{l/d}/G_d$ for **every** continuation. At $l=64$ this is below 0.74 at both ranks and widths. Thus even 64 unrestricted final draws cannot give a history-uniform 0.925-GH certificate. This argument does not bound the unconditional mass of bad histories from above.

The unconditional 1% optimum was not evaluated. An improvement toward one GH would require controlling the mass of penultimate histories with short horizontal vectors and the layer union on the remaining histories, or evaluating the marked recursion. After the first pass there is no fresh final graph draw conditional on the revealed matrix; an analysis of subsequent tours must propagate that matrix and updated presentation, or prove a suitable posterior law. The Haar calculation, fresh-selector counterexample and random-basis literature address different input laws. [Part 105](wall1_selection_law.md) · [Part 106](wall1_chain_law.md) · [Part 107](wall1_lit_random_bases.md) · [Wall 1](../PROOF_GAP.md)

## Reproducible interval checks

The code takes upper endpoints for the logarithmic bounds before choosing the better inequality. All decimal certificate thresholds are lower endpoints rounded down.

```python
from mpmath import iv
iv.dps = 60
I = iv.mpf
alpha = iv.sqrt(3)/2
V = [I(1), I(2)]
for k in range(2, 507):
    V.append(2*iv.pi*V[k-2]/k)

A = [I(0), I(0)]
total = I(0)
for k in range(2, 506):
    # gamma_k^(k/2) from Blichfeldt's integral
    power = I(2)**(I(k)/2)*(1+I(k)/2)/V[k]
    if k == 2:
        power = 1/alpha
    bound = (iv.log(power)+total)/(k-1)
    A.append(min(bound.b, (A[-1]-iv.log(alpha)).b))
    total += A[-1]

for b, bounds in [(406, ('6.4758e-8', '6.4843e-8')),
                  (506, ('3.3322e-8', '3.3357e-8'))]:
    r = b-1
    s = alpha*iv.exp(-max(A[1:r+1]))
    for d, lower in zip((b, r), bounds):
        inv_G = V[d]**(I(1)/d)
        assert inv_G*(s/3329)**(1-I(1)/d) > I(lower)
        assert inv_G*I(3329)**(I(1)/d) < I('0.21')
        assert inv_G*I(3329)**(I(64)/d) < I('0.74')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

**Verified.**

* The joint-length argument: subunit minimizers lie in successive projections of one retained lattice, and Hermite applies to
  their lifted span.
* The deterministic floors on every first-tour path: 6.4758·10⁻⁸ / 6.4843·10⁻⁸ at b = 406 and 3.3322·10⁻⁸ / 3.3357·10⁻⁸ at
  b = 506.
* Reachability of both bad histories under uniform A, with probabilities q^{−511r} and q^{−448r}.
* The upper bounds for every continuation, recomputed at 80 digits:

  | b | 1 draw left | 64 draws left |
  |---:|---:|---:|
  | 406 | 0.207408 | 0.730114 |
  | 506 | 0.185336 | 0.508755 |

**Clarification.** Exact tracking must carry an ambient-coordinate frame on each branch, because lexicographic ties need it.
The Gram matrix and marks alone are not enough for this.

**Open.** The unconditional near-GH 1% quantile, and the law for later tours.
