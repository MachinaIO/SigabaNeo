# Worst-case reduction and independent-error decoding at Wall 1

In the requested convention, $A$ has $m$ rows and $n=511$ columns, with $1\le m\le512$, and $q=3329$. Its entries are independent uniform residues. The secret and error have independent CBD(3) coordinates, independent of $A$. Write $p=20/64=5/16$ for the largest one-coordinate atom.

**For nearest-lattice decoding of $b$ in sample space, no block size achieves one-half success.** At 512 samples even a full-dimensional single-answer decoder of this type has probability below $2^{-847.47}$ of returning the planted lattice point, averaged over the design and planting. **For decoding on the graph lattice with the secret coordinates retained, no block size can guarantee one-half success for every full-rank design.** Average success on the graph is a different question. The cited reduced-basis inequalities do not establish a minimum successful width or a bit cost at 506 for that question.

## The sample-space lattice

Let $C=\operatorname{im}(A)\subseteq\mathbb F_q^m$, $r=\dim C$, and $L=C+q\mathbb Z^m$, where representatives of $C$ are lifted to integers. Its index is $q^{m-r}$. Permute coordinates to put a nonpivot complement first and use systematic generators of $C$. A triangular column basis then has diagonal blocks $qI_{m-r},I_r$, with the off-diagonal entries above the diagonal. Its exact GS lengths in this order are
$$
 (\underbrace{q,\ldots,q}_{m-r},\underbrace{1,\ldots,1}_{r}).
$$
On full row rank $L=\mathbb Z^m$. On full column rank at $m=512$ there is just one $q$ on the diagonal. After any basis reduction the geometric mean of the GS lengths is still $q^{1/512}\approx1.015967$ in this latter case. The initial triangular profile gives no general three-part reduced Z-shape. In particular $A=(I_{511},0)^\mathsf T$, understood as an identity matrix with a zero row appended, gives a rectangular lattice with an exact HKZ basis of 511 unit lengths followed by $q$.

**Counting proposition.** Fix $A$ and any preprocessing coins independent of the planting. Suppose a decoder returns one lattice point $D(b)$ and commutes with translation by $L$, so $D(b+v)=D(b)+v$. This includes Babai with translation-compatible rounding and exact CVP with a fixed choice of residual on each tied coset. The residual $b-D(b)$ takes one value per coset of $L$. Since $b=e\pmod L$, success at the planted lattice point requires $e$ to equal the chosen representative. At most $q^{m-r}$ error vectors qualify, each of mass at most $p^m$. This proof works with any lift of the modular input. The same count gives a factor of at most $K$ for a translation-equivariant list of size $K$. A decoder using the secret prior to score different lifts of the codeword need not have this symmetry.

Averaging the bound costs no rank-deficiency exception. The number of cosets is the number of left null vectors of $A$, and every fixed nonzero left vector vanishes on all $n$ independent columns with probability $q^{-n}$. Hence
$$
 \Pr[\text{planted point returned}]
 \le p^m\bigl[1+(q^m-1)q^{-n}\bigr].
$$

| Samples | Full-rank index | Conditional upper bound, full rank | Unconditional upper bound |
|---:|---:|---:|---:|
| 511 | 1 | $2^{-857.49}$ | $2^{-856.49}$ |
| 512 | 3329 | $2^{-847.47}$ | $2^{-847.47}$ |

The displayed probabilities are rounded upwards. At square full rank the ordinary closest point is $b$ itself, so its success probability is exactly $p^{511}$. There is also a uniform bound for **secret recovery via correct decoding of the planted point**, covering small sample counts where many secrets represent the same point. For $m\le64$, even an unrestricted estimator of $s$ has success at most $q^m p^{511}\le2^{-108.63}$: condition on $A$ and decoder coins, sum the joint probabilities of its guesses over the at most $q^m$ observed values of $b$, and bound each by the prior maximum. For $64\le m\le512$, the planted-point bound is at most $p^{64}+q p^{512}<2^{-107}$, since $p<1<qp$. Thus taking fewer samples does not provide a one-half-success single-answer sample-space decoder of the stated type. The unconditional calculation assumes a prescribed sample subset or a fresh iid design. Choosing a subset after observing the data changes its law.

## The graph lattice retains the secret prior

With columns as basis vectors, use
$$
 G_A=\{(x,y)\in\mathbb Z^{m+n}:x\equiv Ay\pmod q\},\qquad
 B=\begin{pmatrix}qI_m&A\\0&I_n\end{pmatrix}.
$$
For target $(b,0)$, an integer lift of the planted lattice point is $(b-e,s)$. The displacement is $X=(e,-s)$, again product CBD(3). The initial GS profile is $q$ repeated $m$ times followed by 1 repeated $n$ times, independently of rank. At $m=512$ its geometric mean is $3329^{512/1023}\approx57.92666$. This explains the large difference from the sample-space calculation. Preprocessing $G_A$ using only $A$ already appears in [Part 47](wall1_decoupled.md).

For a returned basis write $g_i=\|b_i^*\|$, $w_i=b_i^*/g_i$. Conditional on the design and independent reduction coins, a sufficient Babai event is $|\langle X,w_i\rangle|<g_i/2$ at every rounded index. Strict inequalities avoid ties. The CBD moment generating function in a unit direction is $\prod_j\cosh(t w_{ij}/2)^6\le\exp(3t^2/4)$. Thus the box-failure bound is $\sum_i 2\exp(-g_i^2/12)$. A common lower bound $g_i\ge\sqrt{12\log(4\cdot1023)}\approx9.990069$ suffices for this sum to be at most one-half on at most 1023 indices. The exact probability also depends on the GS **directions**. For a strip of half-width $1/2$, an axis gives mass $20/64$, whereas $(1,1)/\sqrt2$ gives mass $924/4096$. An exact one-dimensional convolution per direction gives individual marginals, and the strips can be dependent.

**Full-rank worst-case witness.** At $m=512$ take the identity design with a zero row appended. Each informative sample is exactly the ordinary signed sum $s_i+e_i\in[-6,6]$ after centering. The last sample is independent of $s$. For the weights $a_j=\binom6{3+j}$, the maximum a posteriori probability of correctly guessing one secret coordinate, averaged over its observation, is
$$
 \frac{1}{64^2}\sum_{h=-6}^6\max_j a_j a_{h-j}
 =\frac{924+792}{4096}=\frac{1716}{4096}.
$$
Log-concavity puts a maximizing split at the middle. Even sums contribute the sum of squares and odd sums the sum of adjacent products. Independence gives the exact best possible probability of recovering all secret coordinates, $(1716/4096)^{511}<2^{-641.38}$, even with unlimited computation. The graph itself is an orthogonal sum of 511 copies of the plane $x_i=y_i\bmod q$ and one $q\mathbb Z$ axis. An exact HKZ profile is $\sqrt2$ repeated 511 times, then $q/\sqrt2$ repeated 511 times, then $q$. Each plane has shortest vector $(1,1)$ and projected spacing $q/\sqrt2$. Picking the shortest remaining orthogonal summand at every step proves the claim. This example rules out a successful profile guarantee uniform in full-rank $A$, even for full HKZ and full CVP. Its tiny probability under the uniform design leaves room for an average-instance theorem.

## What the block guarantees certify

One deterministic **lower envelope**, as opposed to a predicted profile, comes from exact overlapping BKZ. Put $P_0=0$, $C_\ell=(\ell/2)\log\bar\gamma_\ell$ for certified Hermite caps. At zero-based index $j\ge1$ set
$$
 P_j=\min_{2\le\ell\le\min(j+1,\beta)}
 \frac{C_\ell+\sum_{v=j-\ell+1}^{j-1}P_v}{\ell-1}.
$$
Then $g_j\ge\lambda_1(G_A)e^{-P_j}$. Hermite on each leading subblock of a shortest-first window bounds its head by the geometric mean times $\sqrt{\bar\gamma_\ell}$. Backward induction from row $j$ gives the formula. It needs an ambient minimum estimate for typical designs to yield physical lengths larger than the worst-case example permits. For exact equal-block slide at $N=s\beta$, the corresponding aligned terminal-head guarantee is $\lambda_1(G_A)\bar\gamma_\beta^{-\beta(s-1)/(\beta-1)}$. The rank-1023 instance has a partial block at width 506. The equal-block conclusion cannot be applied there verbatim. The self-dual BKZ head bound also has different hypotheses from a shortest-first condition on every overlapping window. [Overlapping and slide derivations](wall1_null_terminal.md) · [Self-dual profile audit](wall1_selfdual_extend.md) · [Micciancio–Walter](https://iacr.org/archive/eurocrypt2016/96650251/96650251.pdf)

The repository contains the following comparisons. **Their design has 511 sample rows and 512 secret coordinates**, the reverse of the largest design in this question. The null ranks agree but the covolumes are $q^{511}$ and $q^{512}$, respectively.

| Certificate on the repository design | Reported result | Scope |
|---|---|---|
| Fully overlapping exact BKZ, horizontal width 506 | Terminal lower bound 0.2726, versus comparison length $\sqrt{6\cdot506}\approx55.100$ | The lower bound is too small. The actual terminal minimum could be larger. |
| Same propagation, all widths | First crossing of $\sqrt{6\beta}$ at 1000. Equal-block exact slide first crosses at 1023 | A crossing at the root-mean-square comparison alone proves no joint decoding probability. |
| Block-Rankin and prefix lifting | Part 49 reports a two-plane refinement at width 1000 and a separate Babai lifting certificate at about 915 | These estimates concern different conditions in the decoder. |
| Prescribed deletion, augmented exact SVP | One call at rank 647 or two calls at rank 646 | Established alternative with a different choice of prefix and the extra height coordinate. |

[Terminal minimum and width scan](wall1_null_terminal.md) · [Width-506 comparison](wall1_jw_slide.md) · [Rankin bounds and audit](wall1_rankin_route.md) · [Part 39](wall1_projected_reference.md) · [Parts 131–132](wall1_multiblock.md)

For exact CVP in the last horizontal block a sufficient condition is $2\|\pi X\|<\lambda_1(\pi G_A)$, followed by successful prefix lifting. One may union-bound failures without treating the lift and projection as independent. For embedded SVP the block has one additional height dimension, and competing vectors of every height must be considered. Hermite caps bound a shortest length **from above** at given covolume. The rank-506 cap 56.21420 and the rank-510/520/530/550 caps 56.79788/57.84689/58.89576/60.99269 can enter profile inequalities. They supply neither the required quotient minimum lower bound nor the probability of the Babai box by themselves. [Part 47](wall1_decoupled.md) · [Part 228](wall1_parameter_slack.md)

**Cost and open implication.** There is no finite cost for one-half success for the single-answer sample-space route under its translation hypothesis. For the typical graph-lattice route at 506 there is no certified cost from these results. A proof bypassing the selected-basis law could instead show a high-probability property of the raw design that implies a joint rounding and terminal decoding bound for every basis satisfying the chosen reduction predicate. It would also need a bounded implementation and call count. Parts 108, 172 and 183–230 analyze a particular adaptive first tour. Their long-winner and plane-hit estimates are not that basis-uniform theorem. Repeating a decoder on one fixed error does not exponentiate an average-instance success probability.

Part 140 records **799.23** in log-base-two operations at rank 647 with a real-RAM initial sampler. Part 141 records **794.98** in log-base-two word operations for its structured rank-647 input or its two structured rank-646 inputs combined. Applying either number to a graph-lattice reduction tour requires costs for the actual projected input representations, oracle type and number of calls. Part 141 specifies 512 secret coordinates. Neither value prices a rank-506 CVP call or a tour on the requested design. [Part 140](wall1_adrs_explicit.md) · [Part 141, input dimensions and model](wall1_sampler_wordram.md) · [Cost correction](wall1_parameter_slack.md)

## Reproducible numerical checks

This standalone Python block uses exact integers and fractions for the probability comparisons. The final displayed logarithms are for reporting only.

```python
from fractions import Fraction
from math import comb, log2

q, n = 3329, 511
p = Fraction(5, 16)
for m in (511, 512):
    full = q ** (m - n) * p ** m
    average = (1 + Fraction(q ** m - 1, q ** n)) * p ** m
    print(m, log2(full), log2(average))

assert q ** 64 * p ** n < Fraction(1, 2 ** 108)
assert p ** 64 + q * p ** 512 < Fraction(1, 2 ** 107)
a = {j: comb(6, 3 + j) for j in range(-3, 4)}
best = [max(a[j] * a.get(h - j, 0) for j in a) for h in range(-6, 7)]
assert sum(best[::2]) == 924 and sum(best[1::2]) == 792
optimum = Fraction(sum(best), 64 ** 2) ** n
assert optimum < Fraction(1, 2 ** 641)
print(log2(optimum))
```

## Audit

**Verdict.** Both probability bounds pass. They concern different experiments. The first counts residuals for a translation-equivariant sample-space decoder. The second gives the exact optimal secret-recovery probability for one full-column-rank design. Neither determines the success probability of the usual primal graph-lattice decoder on a random design.

1. **Sample-space CVP.** For a chosen integer lift $b$, the planted point is $b-e$. Changing the lift by $qz$ moves both this point and the decoder output by $qz\in L$. Equivariance therefore leaves one possible successful residual per error coset, including for exact CVP with equivariant tie-breaking. At 512 samples there are exactly 3329 cosets conditional on full column rank. Averaged over all designs their number is $3330-q^{-511}$, by counting the left kernel. The respective upper bounds have base-two logarithms $-847.47194226$ and $-847.47150896$. In the primal graph model the point also specifies $s$, and the decoding distance includes its secret coordinates. The sample-space count gives no corresponding ceiling there.
2. **Full-rank witness.** Exhaustively maximizing the joint numerator over the splits of each observed sum gives $1,6,36,90,225,300,400,300,225,90,36,6,1$ in order from $-6$ to $6$. The independent last observation sums out to mass one. The posterior factors over the other 511 coordinates, giving exact optimal joint success $(1716/4096)^{511}$ with base-two logarithm $-641.38990904$. This rules out a one-half guarantee uniform in full-column-rank designs, even for an unrestricted estimator.
3. **Random designs and width.** “Unknown” here means that the cited results do not determine the smallest width giving one-half average recovery for the specified graph decoder. For a sufficient statement, fix the reducer, decoder and width. Suppose a set of designs has probability at least $1-\delta$ and on each such design the conditional probability of both correct terminal decoding and correct lifting is at least $1-\varepsilon$. Then average success is at least $(1-\delta)(1-\varepsilon)$, which must reach one-half to certify the target by this argument. A bound valid for every basis allowed by the reduction predicate suffices. For a specified randomized reducer it also suffices to average over its independent coins. Certifying one width gives an upper bound on the minimum. Establishing minimality also requires ruling out smaller widths.
4. **Cost attribution.** Part 141 starts from 511 sample rows and 512 secret coordinates. One height coordinate and 134 retained samples give rank $512+134+1=647$. With 133 retained samples each of the two inputs has rank 646. Its audit reports base-two word-operation counts of 794.9789 for the single call and 794.9746 for both smaller calls combined. Both round upward to 794.98. Part 140's 799.23 uses its real-RAM sampler convention. These are costs for the recorded structured inputs. The reversed dimensions and the width-506 tour require their own cost analysis. [Part 140](wall1_adrs_explicit.md) · [Part 141](wall1_sampler_wordram.md)

The embedded Python block ran successfully. Its final assertion checks the integer exponent 641. I also checked the two headline decimal exponents without floating-point logarithms. For each rational probability bound $u/v$ in lowest terms, the integer comparison $2^k u^{100}<v^{100}$ passed with $k=84747$ for the unconditional sample-space bound and $k=64138$ for the full-rank witness.
