# A finite shifted-Gaussian bound for the four rank-638 CVPs

**Four sequential exact-CVP calls, including validation, cost less than
$2^{778.825}$ word operations.** Their peak space is less than $2^{766}$
words. On every input each call returns a closest point except with probability
less than $2^{-168}$. On the iid design and CBD(3) planting of Part 236 the
probability of returning the single correct secret exceeds
**$0.6431620941663886$**. These are worst-case work bounds and a distributional
recovery guarantee. The word model is Part 141's transdichotomous RAM, with
768-bit addressable words sufficient here. The cost exponent is over 447
bits below the $2^{1226}$ CBD-aware exhaustive-search upper bound, which
certifies the somewhat higher success probability $0.6722$. Neither number
is a measured running time. [Part 236 and audit](wall1_selfdual_envelope.md)

## Which decoding promise is available?

Write $r=127$, $v=511$, $d=r+v=638$, $q=3329$,
$L=\{(h,u)\in\mathbb Z^r\times\mathbb Z^v:h=Au\bmod q\}$ and
$t=(b,0)$ with canonical residues for $A,b$. Each call minimizes the norm in
$C=L-t$. Part 236 credits the planted point when it is the unique closest
point. The stronger condition $2\,\mathrm{dist}(t,L)<\lambda_1(L)$
belongs to a different row of its table.

For example, take the admissible design $A=0$, secret zero and an error
vector with one entry 1 and all others zero. The origin is uniquely closest
at distance 1, and a secret-coordinate unit vector gives $\lambda_1=1$.
In the usual Kannan embedding with any positive height $H$, the desired
height-one vector has length $\sqrt{1+H^2}>1$ while the horizontal unit vector
survives. Thus an exact-SVP oracle alone need not return the desired vector,
even on the translated-ball uniqueness event. Of the two proposed routes,
shifted sampling supplies a finite bound for the stated event. Comparing a
rank-639 SVP exponent as if it had the same promise would give an invalid
cost comparison.

## The fixed run

Use the **initial parameter of run zero at rank 647** in Part 141. This is a
choice of scale for rank 638 and lets us reuse its finite-precision tables
verbatim. Set

$$
s_0^2=647q^2\log(1298)/\pi,\quad s_i=s_0\,2^{-i/2},\quad
\ell=36,\quad \theta=1/8,\quad \Lambda_0=2^{753},\quad M=2^{754}.
$$

Generate $M$ independent approximate samples on $C$ as specified below.
At each of the 36 levels pair successive elements having the same
coordinate-parity key, discard each unmatched element, and pass each pair's
average to the next level. A key equality means the difference lies in $2L$:
if $2z\in L$ and $z$ is integral, the graph congruence and odd $q$ imply
$z\in L$. Each average therefore belongs to $C$. Use a fixed input-order
pairing, independent of norms. Return $t$ plus a minimum-norm member of the
last list, breaking ties by list order. An empty list reports failure. Zero
is a valid residual. There is one initial list and one scale schedule per
call.

The source algorithms are the shifted DGS construction of ADS and its
value-oblivious pairing variant. The integral squared-norm gap here allows a
fixed terminal scale in place of the general recursive exact-CVP reduction.
The following estimates price this specialization. [ADS, §§4–5](https://homepages.cwi.nl/~dadush/papers/fastcvp.pdf) · [ASD, Lemma 3.1 and Appendix A](https://arxiv.org/pdf/1709.01535)

## Shifted combiner with explicit loss

Write $\rho_s(x)=e^{-\pi\|x\|^2/s^2}$, extended by summation to a discrete
set. At level $i$ write $Z_i=\rho_{s_i}(C)$, $U_i=\rho_{s_i}(L)$, and
$F_i=\max_c\rho_{s_i}(2L+c-t)$ over the $2^d$ classes $c\in L/2L$.
Put $p_c=\rho_{s_i}(2L+c-t)/Z_i$, $p_* = F_i/Z_i$.

Two identities or inequalities suffice:

$$
\sum_c p_c^2=\frac{U_{i+1} Z_{i+1}}{Z_i^2},\qquad
F_i^2\le U_{i+1}F_{i+1}.
$$

For the first, the map $(x,y)\mapsto(a,h)=((x+y)/2,(x-y)/2)$ is a
bijection from pairs in $C$ with a common class onto $C\times L$.
Their weight factors as $\rho_{s_{i+1}}(a)\rho_{s_{i+1}}(h)$.
For the second, restrict both inputs to a class attaining $F_i$. For each
$h\in L$, the allowed $a$ lie in a single class of $C$ modulo $2L$, of
mass at most $F_{i+1}$. This proof also shows that the average, conditional
on the input class and output class, is a Gaussian restricted to that
output class. The allowed $h$ then range over a fixed class, independent
of the value of $a$ inside its class.

In the ideal analysis start with a Poisson list of mean $\Lambda_0$. For
each class couple its count $N_c\sim\mathrm{Pois}(\Lambda_i p_c)$ to an
independent-across-classes requested number of pairs
$K_c\sim\mathrm{Pois}(\theta\Lambda_i p_c^2/p_*)$ using Part 140, Lemma
4.3a. Its hypotheses involve only the counts. The ideal output mean and the
mean of the heaviest class satisfy

$$
\Lambda_{i+1}=\theta\Lambda_i\frac{U_{i+1}Z_{i+1}}{Z_i F_i}
\le\theta\Lambda_i,\qquad
A_{i+1}:=\Lambda_{i+1}F_{i+1}/Z_{i+1}\ \ge\theta A_i .
$$

Indeed $\sum p_c^2\le p_*$ proves the upper bound, and the second Gaussian
inequality proves the lower bound. In particular
$A_i\ge 2^{753-638-3i}$, since $p_*\ge 2^{-638}$ initially. Every
pairing step starts with $A_i\ge1024$, and the terminal level has
$A_{36}\ge128$. Poisson splitting, the squared-class law, and the first
identity give an ideal Poisson list of iid $D_{C,s_{i+1}}$ samples.

For clarity about the domination issue in ASD Definition 2.2, this uses a
joint coupling of lists. Given labels, independent count coins and past
labels, the values in each class are independent class-restricted Gaussians.
In the coupling one may pair the designated disjoint pairs first and then
complete a maximal pairing. Each input class produces the same number and
law of independent averages as the canonical maximal pairing. Conditional
on output labels, their values again have the specified restricted laws.
Induction gives the same law of class multisets; the last minimum is
invariant under permutations. The ideal list is contained up to the first
count mismatch. On a shortage one can supply fresh ideal pairs from the
relevant restricted Gaussian to continue the ideal process with its correct
marginal. This compares the algorithms up to failure without conditioning
the Poisson law on success. [Part 140, Lemmas 4.3–4.5 and audit](wall1_adrs_explicit.md)

The tail index in Lemma 4.3b is
$K=\lfloor A_i/(4\theta)-1/2\rfloor+1\ge2000$. Dropping its denominators
and rounding its exponential factors upwards, the sum of mismatch
probabilities over all steps is at most

$$
36\,2^{753}\,8\big[(1/4)^{1999}+(3/4)^{3999}\big]<2^{-830}.
$$

The probability that the initial Poisson count exceeds the actual list
length $2\Lambda_0$ is at most $(e/4)^{\Lambda_0}<2^{-800}$.
The Poisson counts and the extra pairs are proof devices and incur no RAM
cost.

## A terminal Gaussian hit is an exact CVP answer

Put $D=\min_{x\in C}\|x\|^2$, an integer, and
$N_d(k)=\#\{z\in\mathbb Z^d:\|z\|^2\le k\}$. In **each** parity class
the number of members of squared norm at most $D+k$ is at most $N_d(k)$.
If this set is nonempty, fix one member $x$. For any other member $y$,
the midpoint is in $C$, and

$$
\|(y-x)/2\|^2
=\tfrac12(\|x\|^2+\|y\|^2)-\|(x+y)/2\|^2\le k .
$$

The map $y\mapsto(y-x)/2$ is injective into the integer ball. This is the
midpoint calculation of ADS Lemma 5.1, used here to control the heaviest
class, including classes containing no optimum. [ADS, §5](https://homepages.cwi.nl/~dadush/papers/fastcvp.pdf)

Let $u=e^{-\pi/s_{36}^2}$. Summing the cumulative count bound against
$(1-u)u^k$ gives

$$
F_{36}\le u^D(1-u)\sum_{k\ge0} N_d(k)u^k
=u^D\Big(\sum_{a\in\mathbb Z}u^{a^2}\Big)^d
\le u^D \exp(2du/(1-u)).
$$

Here $-\log_2u=\pi^2 2^{36}/(647q^2\log(1298)\log 2)>16$.
Thus $F_{36}/u^D\le\exp(1276/65535)<16/15$. Fix any one closest residual.
The number of its copies in the ideal final list is Poisson of mean

$$
\Lambda_{36}\,u^D/Z_{36}= A_{36}\,u^D/F_{36}\ge120.
$$

The ideal miss probability is at most $e^{-120}<2^{-172}$, uniformly in
$A,b$. This estimate works for ties and does not use an upper bound on $D$.

## Initial sampling and the word budget

Use the tables and truncation in Part 141, §§3–4, at exactly the rank-647
run-zero parameter above. Draw $v$ tail coordinates independently from its
table for $\mathbb Z$. Given the tail $u'$, draw each head coordinate from
the table for $q\mathbb Z+(Au'-b)_i$. The conditional factorization is
exact for the ideal Gaussian. The only discrepancy before table rounding
is the tail marginal, tilted by the product of the $r$ one-dimensional
coset masses. Lemma 2 bounds that tilt uniformly over *all* choices of
residues. Subtracting $b$ therefore preserves the estimate. Both the head
and tail counts decreased from $(134,513)$ to $(127,511)$, and all scalar
tables are identical. Lemma 8 and the audit bound the per-sample total
variation by $2^{-923}$. Fresh coins give total variation below
$2^{754-923}=2^{-169}$ for the entire input list. The list phase is
deterministic. Adding the four error terms above gives per-call failure
below $2^{-168}$. [Part 141, Lemmas 2–9 and audit](wall1_sampler_wordram.md)

For explicit work accounting use unit-cost indirect loads and stores,
arithmetic including integer division and remainder, comparisons, branches,
bitwise operations and shifts, and a fresh uniform 64-bit random word per
random draw. Take a word width of 768 bits. The wide quantities are
addresses, keys, and counters. The scalar sampler uses Part 141's limb
arithmetic. Every residual coordinate is bounded by $2^{22}-1$, including
after averaging; its squared norm is below $2^{54}$. The following charges
include loop control and addressing.

| Work per call | Upper bound in operations | Basis for the charge |
|---|---:|---|
| Initial deterministic tables | $2^{42}$ | Part 141 charges $2^{40}$ even with its largest scale; the same tables can be rebuilt for each call. |
| Generate one vector | $S=8192d+32rv+64d+512$ | Each of $d$ draws needs 15 random limbs, at most 23 binary-search levels with 15-limb compares, and an output load. Allow 16 operations per limb per level and 32 per level for indexing and control, plus 16 per random limb and 64 for setup/output, below 8192 per draw. The $rv$ dot-product entries take at most 32 each including address calculation. The remaining terms cover the subtraction, modular reduction, vector stores and loops. |
| Pairing and terminal norm scan | $2M(64d+128)$ | For each visited vector form its key by $d$ mask/shift/append steps. A pending-index array pairs the next occurrence of the same key, clears the slot and appends a coordinatewise average. Per coordinate allow 16 operations for the key, 24 for averaging and stores, and 24 for norm scan or recording a best index. Use 128 per vector for index and loop setup. Including the terminal list, fewer than $2M$ vectors are visited. |
| Clear pending indices and level control | $\ell(8\cdot2^d+128)$ | Direct addressing of the packed $d$-bit key. A zero sentinel denotes an empty slot. The next list can be emitted in encounter order by the pairing argument above. |
| Per-call input and return | $2^{21}$ | Copy canonical residues and the target, return a minimum index's vector plus $t$, or signal an empty list. Even 16 operations per matrix entry and 64 per coordinate fit. |

Thus set

$$
W=2^{42}+MS+2M(64d+128)+36(8\cdot2^{638}+128)+2^{21}.
$$

Two vector buffers, the pending-index array, tables, input, and temporary
storage fit in $4(d+10)M+2^{640}+2^{30}<2^{766}$ words. The pending array
is initialized explicitly. Four calls can share the working space. A
further $2^{24}$ operations cover support testing of the four outputs,
their tests on four held-out rows, and final selection (at most
$4\cdot4\cdot511$ dot-product entries). In particular,
$W<2^{776.825}$ and $4W+2^{24}<2^{778.825}$. The very large memory is
part of the model; this bound does not price emulation on a fixed
64-bit-address machine.

## Recovery probability and reproduction

The exact rational lower bound from Part 236's rounded-down conditional
group credits is $P_{236}=0.6431620941663886012903702\ldots$. It already
accounts for the shared secret, all ties charged on the geometric event,
and validation. The probability that any of the four calls fails its
exact-CVP contract is less than $4\cdot2^{-168}=2^{-166}$, also after
averaging over the dependent inputs. Correctness on a credited group
forces the planted candidate, and each group's computation uses only its
own input and fresh coins before validation. Thus the same held-out-row
charge applies to any locally selected wrong candidate. The resulting lower
bound is $P_{236}-2^{-166}>0.6431620941663886$.

Run **python -B docs/research/scripts/wall1_cvp638_cost.py** at repository
root. The checker verifies the scale and Gaussian estimates by interval
arithmetic, the work exponents and Poisson-tail envelopes by integer or
rational comparisons, and recomputes the four-group probability with the
Part 236 checker. It performs certificate arithmetic only.
[Cost checker](scripts/wall1_cvp638_cost.py) · [Part 236 checker](scripts/wall1_selfdual_envelope.py)

## Audit

**Verdict — CONFIRMED for the stated graph inputs and word-RAM.** The four-call work allowance including validation has base-two logarithm $778.824244026$ and the peak-space allowance has base-two logarithm $765.339850003$. Each call returns a closest point with failure probability below $2^{-168}$ for every canonical $A,b$ of the specified dimensions. The recovery percentage additionally requires the iid design and CBD(3) planting of Part 236.

**Source attribution.** ADS15 Lemma 4.1 gives the shifted Gaussian law of an average conditional on a class collision. Its published Theorem 4.3 starts with $(32\kappa)^{\ell+1}2^n$ samples and gives an error bound involving unspecified constants. Theorem 4.7 and Corollaries 5.6–5.7 use a sampler and a recursive reduction to find all closest vectors. The finite calculation here instead uses Part 140's count coupling and the integral midpoint estimate to find one closest vector. It has one run, 36 levels, and no sparsification, recursive calls, or guessed distances to charge. The $A=0$ example in the note also verifies the obstruction to inferring a Kannan-embedding guarantee from uniqueness alone. [ADS15, §§4–5](https://homepages.cwi.nl/~dadush/papers/fastcvp.pdf)

**Joint coupling and terminal hit.** Conditional on the full label history, membership marks and count coins, distinct available vector values have independent Gaussian laws restricted to their respective classes. Averaging disjoint pairs preserves this property when their output labels are exposed, by ASD Lemma 3.1. Thus the distribution of the next class multiset depends only on the numbers of pairs taken from each class. Pairing marked pairs first preserves the marginal multiset law of the maximal pairing. Supplying fresh restricted pairs on shortage gives the ideal process its unconditional Poisson marginal. This construction justifies containment until failure without using closure of the upper-orthant order in ASD Definition 2.2. One wording clarification matters for ties. Permuting a final list preserves its minimum **norm** and the event of containing a closest point. Its first minimizing index can select a different point, which still fulfills the exact-CVP contract. [ASD, Definition 2.2 and Lemma 3.1](https://arxiv.org/pdf/1709.01535)

With ideal mean $2^{753}$, the $2^{638}$ classes give $A_0\ge2^{115}$. The collision identity and $F_i^2\le U_{i+1}F_{i+1}$ give $A_{i+1}\ge A_i/8$, hence $A_{35}\ge1024$, $K\ge2048$ at every pairing step, and $A_{36}\ge128$. The stated rounded mismatch envelope has log base two below $-898$. The Poisson overflow bound uses $e/4<3/4$ and $2^{753}>2000$. At $s_{36}=0.48794137\ldots$, the inverse temperature in bits is $19.03658872\ldots$. In any nonempty class portion of the ball of squared radius $D+k$, taking half-differences from one fixed member injects that portion into the integer ball of squared radius $k$. This proves the theta-series bound even when that class contains no minimizer. It gives mean multiplicity at least $128(15/16)=120$ for any one fixed optimum and ideal miss probability at most $e^{-120}$. All these estimates hold with $A,b$ fixed.

**Finite precision and storage.** The triangular basis has 12-bit unsigned entries, determinant $3329^{127}$, and Gram–Schmidt lengths $3329$ and $1$. Odd determinant makes coordinate parity an exact key for differences modulo $2L$. The initial scale has $s_0/q=\sqrt{647\log(1298)/\pi}$ independently of $A,b$. Substituting the shifted residues in Part 141's scalar bounds gives the following upper bounds, expressed as base-two logarithms. The Klein tilt is below $-6683$, the tail-coordinate table error below $-932.91$, and the worst head-coordinate table error below $-948.69$. The 511 tail and 127 head draws together give a one-vector bound below $-923.91$. These use $R=2^{22}-1$, 1024 fractional bits, 1088 working fractional bits and 960 threshold bits. The last threshold $2^{960}$ is the implicit upper endpoint of the binary search. The table builder uses limb arithmetic and each lookup draws fifteen independent 64-bit words. [Part 141, §§3–5](wall1_sampler_wordram.md)

The unreduced shifted row sum has magnitude at most $511(3328)R+3328<2^{43}$, and $638R^2<2^{54}$. The 638-bit key, list indices through $2^{754}$, and buffer addresses below $2^{766}$ each fit in one 768-bit word. The allowance of 8192 operations per scalar draw covers $23(16\cdot15+32)+16\cdot15+64=6560$ operations. Substituting the dimensions gives $S=7{,}344{,}544$. Maximal pairing visits at most $M\sum_{i=0}^{36}2^{-i}<2M$ vectors including the terminal scan. The separate clearing and validation charges cover all 36 pending-array initializations and all $4\cdot4\cdot511$ validation multiply-adds. The work bound counts indirect access to the full address space at unit cost.

**Independent reproduction.** Running the linked checker with Python assertions enabled passed. A separate exact-integer calculation multiplied the shell and CBD energy polynomials one coordinate at a time through degree 955. The first zero credit was at 955. Direct convolution for each fixed secret energy, rounding down to the $10^{-9}$ grid, reproduced the four-group credit. Subtracting the held-out charge $4(7/3329)^4$ and the solver charge $4\cdot2^{-168}$ gives $0.64316209416638860129037020396927075\ldots$. The solver charge follows by a union bound conditional on the inputs. The held-out charge conditions on the secret and the locally generated candidate list, which leaves all four validation rows fresh. The checker and this independent calculation evaluate the certificate arithmetic only. [Part 236, repetitions and audit](wall1_selfdual_envelope.md)
