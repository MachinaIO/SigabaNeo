# Smoothing and all-heights uniqueness for a fixed Wall1 block

**At final width 406 the recorded GSA profile itself rules out 99% uniqueness.** Its first terminal GS vector has length below 24.767. For *every* rank-405 orthogonal projection of the CBD(3) plant, a horizontal vector this short causes failure with probability greater than 2.137%. The same obstruction holds if 406 counts only horizontal dimensions. This conclusion uses the fourth centered moment of the projected energy and already applies at height zero.

**At final width 506 the GSA determinant passes the volume comparison, but a 1% bound on a physical GSA-type block is unverified.** The dual sum for a Gaussian plant and the dual sum for the CBD plant have different Fourier coefficients. Even an arbitrarily flat wrapped Gaussian need not give a volume estimate for a wrapped CBD sample. A fixed-block bound using the correct coefficients is given below, with an alternative finite-group bound. The formulas can be non-vacuous on physical blocks. The interval calculations distinguish that fact from verification on the proposed GSA geometry.

## Conditional law and the target event

Let the reducer depend on the design and on coins independent of the plant. Condition on both. Write $L_0$ for the horizontal null lattice, $Q$ for the orthogonal projection off the prefix, $E=\operatorname{im}Q$, $d=\dim E>0$, $H=QL_0$, and $D_H=\operatorname{covol}_E H$. The final oracle rank is $d+1$. In the original orthonormal coordinate frame, $X$ has independent CBD(3) entries, each distributed as a sum of six independent signs divided by two. Write $y=QX$, $Z=\|y\|^2$, $R^2=1+Z$, and $\lambda=\lambda_1(H)$. Every projected vector has the form $(h+ky,k)$. A tie with any vector outside the origin and the signed plant pair counts as failure. Thus the failure event is the union of

* $R\ge\lambda$ at height zero,
* $\|h+y\|\le\|y\|$ for some $0\ne h\in H$ at height one,
* $\|h+ky\|^2\le R^2-k^2$ for some $h\in H$ and integer $2\le k\le R$.

Negation covers negative heights. The radius on the last line depends on the *same* sample as the shift. The determinant of the full horizontal lattice is $3329^{511}$ with all rows present. The determinant in a terminal volume estimate is $D_H$, obtained by dividing by the prefix covolume. Part 39 counts over independent designs for a prescribed coordinate deletion. Here the randomness after conditioning is solely that of the plant. [Part 39 and audit](wall1_projected_reference.md) · [Part 47 and audit](wall1_decoupled.md) · [Part 94 and audit](wall1_threshold.md) · [Lean criterion](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessCriterion.lean) · [Physical projection](../../SigabaNeo/Lib/Lattices/Research/Wall1/AttackLattice.lean)

## Why the continuous smoothing implication fails

With the convention $\rho_s(x)=e^{-\pi\|x\|^2/s^2}$, a continuous isotropic Gaussian of standard deviation $k\sqrt{3/2}$ has width $s=k\sqrt{3\pi}$. Its density modulo $H$, relative to normalized Haar measure on $E/H$, has Fourier coefficients $e^{-\pi s^2\|w\|^2}$ for $w\in H^*$. This follows by integrating the periodized density over a fundamental cell and taking the ordinary Gaussian Fourier transform. The sum of the nonzero coefficients bounds the pointwise difference from one. For a *fixed* ball of radius $r$ the resulting expected lattice count is at most $(1+\varepsilon)V_dr^d/D_H$ when that sum is at most $\varepsilon$, where $V_d$ denotes the volume of the Euclidean unit ball. Unfolding the ball count over one cell gives the volume factor. [Lyubashevsky, Peikert and Regev, §2.2](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf)

For CBD the same coefficient is instead
$$
 C_k(w)=\mathbb E\,e^{2\pi i\langle w,ky\rangle}
       =\prod_{j=1}^N\cos^6(\pi k w_j).
$$
Indeed $Qw=w$ and $Q$ is self-adjoint. Each half-sign contributes one cosine. In particular $C_k(w)=1$ whenever $kw\in\mathbb Z^N$. The real-MGF bound in Lean controls linear tails and gives no Gaussian upper bound for these periodic coefficients. The finite support of $ky\bmod H$ has continuous Haar mass zero, so the total variation distance is exactly one for every $k$. One can still seek approximation for a *specific ball test*. Such a statement needs a bound on that test. The one-dimensional Lean smoothing lemma proves a bound for shifted Gaussian sums. [CBDTail](../../SigabaNeo/Lib/Lattices/Research/Wall1/CBDTail.lean) · [GaussianSmoothing1D](../../SigabaNeo/Lib/Lattices/Research/Wall1/GaussianSmoothing1D.lean)

**Counterexample with a ball test.** Take $H=2\mathbb Z$, $Q=1$, $k=2$. All shifts $2X$ equal zero modulo $H$. A closed ball of radius $1/10$ around the shifted origin contains exactly one lattice point, whereas its volume divided by the covolume is $1/10$. At the matched Gaussian width the nonzero dual mass is at most $2z/(1-z)<2.768\cdot10^{-13}$ with $z=e^{-3\pi^2}$, by $n^2\ge n$. For the actual Part 94 radius the height-two competitor $(-2X+2X,2)$ qualifies exactly when $X^2\ge3$, of mass $14/64$. Multiples of two as dilations on this same lattice give arbitrarily small Gaussian dual mass with the identical fixed-ball discrepancy. This rank-one example isolates the proposed smoothing implication.

At $r=0.954(D_H/V_d)^{1/d}$ the uniform continuous mean is exactly $0.954^d$. It lies in $(5.2130,5.2131)\cdot10^{-9}$ at $d=405$ and $(4.6981,4.6982)\cdot10^{-11}$ at $d=505$. This computation concerns a fixed-radius ball under Haar measure. Transferring it requires controlling both the CBD ball count and the probability that the plant exceeds the chosen radius.

There is a distinct finite reference measure for a physical graph. Put $J=Q\mathbb Z^N$. Then $qJ\subset H\subset J\subset q^{-1}H$, so $J$ is a lattice and $G=J/H$ is a finite group of exponent dividing $q$. For prime $q=3329$, every height $1\le k\le\lfloor\sqrt{1+9N}\rfloor$ at $N=1023$ acts by a permutation on $G$. In particular the distance of the CBD law on $G$ to *finite* uniform measure is exactly invariant under these dilations. Increasing $k$ can change which residues hit a ball. It cannot improve uniformity on $G$. Even an exactly uniform shift on $G$ gives mean closed-ball count $\#(J\cap B_r)/|G|$, by partitioning the points by coset. Replacing that count by $V_dr^d/D_H$ requires a further estimate.

**What Part 172 supplies.** Its audited simultaneous upper bound is between $8.14649452211672\cdot10^{-14}$ and $8.14649452211673\cdot10^{-14}$ for exits below specified raw dual floors in the width-506 marginal restart. The estimate concerns design randomness in a particular sequence of windows. A retained dual section inherits the relevant floor by inclusion. Neither the exit probability nor the floor bounds the CBD coefficients at the remaining frequencies. In particular the exit probability is not a permissible substitution for $\varepsilon$ in the Gaussian density argument. [Part 172, Proposition 2 and audit](wall1_transference.md)

## A fixed-block upper bound

Choose $a>3d/2$, $B=1+a$, $K=\lfloor\sqrt B\rfloor$, $r_k=\sqrt{B-k^2}$ for $k\le K$, and $v=2a/(3d)$. Set $p_a=\exp[-d(v-1-\log v)/2]$. If $\lambda\le\sqrt B$ use the trivial bound one in the following cap-based test. Otherwise define
$$
 \operatorname{err}_{\rm smooth}(H,Q)
 =\min\left(1,\ p_a+U_1+\sum_{k=2}^K U_k\right).
 \tag{1}
$$
The choice of cap and all numerical majorants is part of a witness for (1). Take $U_1=\min(1,\sum_{h\in H\setminus\{0\}} e^{-\|h\|^2/12})$. Set $U_1=0$ if $\lambda>2\sqrt a$. For $k\ge2$ one may take the minimum of one and either or both of the two bounds in (2).
$$
 \begin{aligned}
 M_k(t)&=\frac{e^{t r_k^2}(\pi/t)^{d/2}}{D_H}
 \sum_{w\in H^*} e^{-\pi^2\|w\|^2/t} C_k(w), \qquad t>0,\\
 A_k&=\sum_{g\in G}\mu(g)\,\#\{z\in J\cap B_{r_k}:z\bmod H=kg\},
 \qquad \mu(g)=\Pr[QX\bmod H=g].
 \end{aligned} \tag{2}
$$
The finite expression applies when $J/H$ is finite. In either case set $U_k=0$ if $\lambda>k\sqrt a+r_k$. The first expression in (2) is the CBD-weighted Poisson majorant of Part 97. The second gives an exact fixed-radius first moment on the physical graph. An upper bound for either expression suffices. [Part 97, conditional certificate and audit](wall1_dist_unique.md)

**Proof.** For $0<t<1/3$, integration of the product linear MGF bound against an independent standard Gaussian $g$ in $E$ yields
$$
 \mathbb E e^{tZ}
 =\mathbb E_g\mathbb E_X e^{\sqrt{2t}\langle g,X\rangle}
 \le\mathbb E_g e^{3t\|g\|^2/2}=(1-3t)^{-d/2}.
$$
Exponential Markov with $t=(1-1/v)/3$ gives $\Pr(Z>a)\le p_a$. On the complementary event height zero passes, and every height $k>K$ passes. At height one a competitor implies $-\langle h,X\rangle\ge\|h\|^2/2$, with probability at most $e^{-\|h\|^2/12}$ by the linear MGF and Markov. Sum over $h\ne0$. At any positive height a genuine competitor has $h\ne0$ since $(ky,k)$ is a multiple of the plant. The triangle inequality yields the two deterministic exclusions.

At $k\ge2$ a competitor on the cap gives a point in the fixed closed ball of radius $r_k$ centered at $-ky$. The unconditional expected count bounds this event. To obtain $M_k$, majorize each indicator by $e^{t(r_k^2-\|h+ky\|^2)}$. The periodized Gaussian has coefficients $(\pi/t)^{d/2}e^{-\pi^2\|w\|^2/t}/D_H$ by unfolding and the Gaussian Fourier transform. Its Fourier series converges absolutely. Taking the expectation termwise supplies $C_k(w)$. For $A_k$, partition by $QX\bmod H$ and count in the indicated coset. Both majorants may include $h=0$. Finally take the union bound and charge the cap exception once. The expectation in (2) uses the original CBD law. ∎

The weighted theta in (2) is checkable in principle from an **embedded** dual basis. A finite truncation needs a certified tail. For example, with $\lambda_1(H^*)\ge u>0$, the number of points in $ju\le\|w\|<(j+1)u$ is at most $(2j+3)^d$ by packing disjoint open $u/2$-balls. After enumerating all points shorter than $mu$, bound the tail by $\sum_{j\ge m}(2j+3)^d e^{-\pi^2j^2u^2/t}$ using $C_k\le1$. Successive majorant terms have ratio at most $[(2m+5)/(2m+3)]^d e^{-\pi^2(2m+1)u^2/t}$ for $j\ge m$. Once this is below one, a geometric series gives a certified remainder. The primal height-one sum admits the same packing argument with its own scale and minimum. Finite exact sums may be expensive. An intrinsic dual Gram matrix, or a GSA list, omits the orientation of the ambient CBD axes needed by $C_k$.

## A height-zero lower bound independent of the projection's orientation

**Proposition.** Let $d\ge405$ and let $Q$ be any rank-$d$ orthogonal projection. If
$$
 \lambda^2\le 1+\frac32d+\frac25\sqrt{15d/4},
 \tag{3}
$$
then the probability of a height-zero failure is greater than $0.0213734$. In particular a 1% certificate requires a minimum *strictly above* the square root of the right side. The implication gives a necessary condition.

**Proof.** Let $P$ be the $N$ by $6N$ matrix whose $i$th row is one half at the positions of the six signs defining $X_i$, zero elsewhere. With the independent sign vector $\xi$, put $T=P^\top QP$, $M=T-\operatorname{diag}T$. Then $Z=\xi^\top T\xi$ and $Y=Z-3d/2=\xi^\top M\xi$. Since $PP^\top=(3/2)I$, $0\preceq T\preceq(3/2)I$. Its diagonal entries are $Q_{ii}/4\in[0,1/4]$. Hence $-I/4\preceq M\preceq(3/2)I$. Writing $V=\mathbb EY^2$ gives
$$
 V=2\operatorname{tr}M^2=\frac92d-\frac34\sum_i Q_{ii}^2\ge\frac{15}4d.
$$
Here $\sum_i Q_{ii}^2\le\operatorname{tr}Q=d$. The exact variance also appears in Lean. [CBDQuadratic, projection variance](../../SigabaNeo/Lib/Lattices/Research/Wall1/CBDQuadratic.lean)

For completeness the next two moment bounds are
$$
 \mathbb EY^3=8\operatorname{tr}M^3,\qquad
 \mathbb EY^4\le3V^2+48\operatorname{tr}M^4.
$$
Expand $Y=\sum_{i<j}2M_{ij}\xi_i\xi_j$. Only products in which every vertex has even degree survive. For three edges these are triangles, with $3!$ edge orders and six orientations/starting vertices in the trace. For four edges the repeated-edge configurations contribute $3V^2-2\sum_{i<j}(2M_{ij})^4$. The only other configurations are simple four-cycles. A given undirected cycle occurs $4!$ times with coefficient $2^4$ times its product of matrix entries, and eight times in $\operatorname{tr}M^4$. All the other length-four closed walks in that trace have nonnegative weight since a repeated vertex forces paired edges. This proves the upper bound even for signed matrix entries.

For $W=Y/\sqrt V$ this gives $|\mathbb EW^3|\le6/\sqrt V$ and $\mathbb EW^4\le3+54/V$ by $\|M\|_{\rm op}\le3/2$. Take $c=2/5$, $b=4$, $s=6/5$ and
$$
 f(x)=(x-c)(x+s)^2(b-x),\qquad D=(b-c)^2(b+s)^2/4=87.6096.
$$
To see $f(x)\le D\mathbf1_{\{x>c\}}$ pointwise, observe that outside $[c,b]$ the polynomial is nonpositive, and inside one has $(x-c)(b-x)\le(b-c)^2/4$. Taking expectations, using $\mathbb EW=0$, $\mathbb EW^2=1$, gives
$$
 D\Pr(W>c)\ge
 -(3+54/V)-12/\sqrt V+10.56-1.6-1.44-2.304 .
$$
Indeed the cubic coefficient is $b+c-2s=2$. The right-hand side increases with $V$ and at $V=15\cdot405/4$ gives a probability lower bound in $(0.02137349,0.02137351)$. On $W>c$, $R^2>1+3d/2+c\sqrt{15d/4}$, which proves (3). ∎

## Interval checks at the recorded determinant

For clarity fix the repository's full-row geometric series assumption (GSA). Write $b$ for the width used to choose its slope, $N=1023$, $D_0=3329^{511/N}$ and
$$
 s_b=\frac{\log(b/(2\pi e))+\log(\pi b)/b}{2(b-1)}.
$$
The $i$th predicted physical length is $D_0 e^{(N-1-2i)s_b}$, zero-based. Their product is exactly $3329^{511}$. For the final $d$ horizontal indices the head is $h=D_0e^{(2d-N-1)s_b}$, and the terminal determinant root is $G_0=D_0e^{(d-N)s_b}$. Always $\lambda\le$ the *actual* head, since the first projected basis vector itself has that length. This inequality needs no exact-reduction hypothesis. The table tests the model head and determinant. A physical realization requires separate verification. [Recorded GSA convention](wall1_null_terminal.md) · [Part 94 width conventions](wall1_threshold.md)

Let $L_{\rm nec}$ denote the square root in (3). In the last column take Part 97's cap $a=1.9d$, $t=d/(2B)$, and sum the $w=0$ terms of $M_k(t)$ to give $S_0$. Each displayed interval is outward rounded.

| Slope width $b$ | Horizontal $d$ | Oracle rank | Head $h$ | Root $G_0$ | $L_{\rm nec}$ | $\log_{10} S_0$ |
|---:|---:|---:|---:|---:|---:|---:|
|406|405|406|(24.76650, 24.76652)|(5.05500, 5.05502)|(24.98175, 24.98177)|(20.79278, 20.79280)|
|406|406|407|(24.96210, 24.96212)|(5.07492, 5.07494)|(25.01214, 25.01216)|(20.15111, 20.15113)|
|506|505|506|(54.82114, 54.82116)|(10.03251, 10.03253)|(27.85509, 27.85511)|($-124.35041$, $-124.35039$)|
|506|506|507|(55.19183, 55.19185)|(10.06637, 10.06639)|(27.88231, 27.88233)|($-125.33667$, $-125.33665$)|

At width 406 the strict head comparison proves failure above 1% for any physical block whose head is at most the stated model value. Nearby profiles should be tested against (3). “GSA-type” with an unspecified tolerance gives no bound on an individual head. At width 506, $p_a<0.0005$ and the zero-frequency contribution is tiny. For example the high-height sum would be below $10^{-4}$ for $d=505$ if every full weighted sum in (2) were at most $10^{120}$ at this $t$. This is a conditional arithmetic comparison. No such estimate follows from the GSA listing or the Part 172 exit. Also a head above $L_{\rm nec}$ alone gives no lower bound on $\lambda$. The audited Part 171 minimum floor $0.954\cdot28.8095=27.484263$ falls below even the new necessary floor at $d=505$. A block whose minimum *equals* the former number fails. A lower bound of that size leaves its true minimum open. Part 101's minimum guarantees and Part 103's height-zero comparison concern different certified quantities. [Part 101 audit](wall1_qary_rogers.md) · [Part 103 audit](wall1_width_scan.md) · [Part 171 audit](wall1_budget_reallocation.md)

**Physical control for (1).** At the zero design take a basis starting with the 512 secret coordinate units and then $511-d$ of the $q$-scaled error axes. The remaining error axes project identically, giving $H=q\mathbb Z^d$ and $\lambda=q$. The full determinant is $q^{511}$. For all four table rows $B=1+1.9d<q$. For $1\le k\le K$, Cauchy–Schwarz gives $k\sqrt a+r_k\le\sqrt{a+1}\sqrt{k^2+r_k^2}=B$. Every deterministic exclusion in (1) therefore applies. Its value is $p_a<0.0022$ at all four ranks. This verifies that the fixed-block test can accept physical terminal geometry. This special design has a flat terminal profile of length 3329 and unit prefix directions. It provides neither a GSA witness nor a prefix lifting guarantee.

**Reproduction.** The following uses 80-decimal outward intervals. The formulas include the non-asymptotic zero mode of (2).

```python
from mpmath import iv as I
I.dps = 80
Vmin = I.mpf(15)*405/4
quartic = (-(3+54/Vmin) - 12/I.sqrt(Vmin) + I.mpf(5216)/1000)/I.mpf('87.6096')
assert I.mpf('.02137349') < quartic and quartic < I.mpf('.02137351')
D0 = I.exp(511*I.ln(3329)/1023)
for b in (406, 506):
    s = (I.ln(b/(2*I.pi*I.exp(1))) + I.ln(I.pi*b)/b)/(2*(b-1))
    for d in (b-1, b):
        h = D0*I.exp((2*d-1024)*s)
        G = D0*I.exp((d-1023)*s)
        L = I.sqrt(1 + I.mpf('1.5')*d + I.mpf('.4')*I.sqrt(I.mpf('3.75')*d))
        B = 1 + I.mpf('1.9')*d
        t = d/(2*B)
        K = int(I.sqrt(B).a)
        assert K < I.sqrt(B) and I.sqrt(B) < K+1
        S0 = sum(I.exp(t*(B-k*k))*(I.pi/t)**(I.mpf(d)/2)/G**d
                 for k in range(2, K+1))
        v = I.mpf(19)/15
        cap = I.exp(-d*(v-1-I.ln(v))/2)
        assert cap < I.mpf('.0022')
        if b == 406:
            assert h < L
        else:
            assert cap < I.mpf('.0005') and S0 < I.mpf('1e-124')
        print(b, d, h, G, L, I.ln(S0)/I.ln(10), cap)
```

## Exact small checks and Lean obligations

As an orientation check, project $\mathbb Z^2$ onto a unit vector $u$ and identify its span with $\mathbb R$. Take $H=\mathbb Z$ intrinsically in both cases. For $u=(1,0)$ this is realized by projecting the kernel of $x_2=0\bmod 5$. For $u=(3,4)/5$ use the kernel of $3x_1+4x_2=0\bmod5$. Bézout gives projected lattice $\mathbb Z$. Both have identical intrinsic primal and dual theta at **every** scale. Enumerating $i,j=-3,\ldots,3$ with weights $\binom6{3+i}\binom6{3+j}$ gives the following integer numerators for $5\langle u,X\rangle\bmod5$, in residue order $0,1,2,3,4$, with common denominator 4096.
$$
 (4096,0,0,0,0),\qquad (820,819,819,819,819).
$$
At $k=2$ and closed radius $1/5$, the first expected count is one and the second is $2458/4096$ (the residues of the doubled shift are $0,1,4$ for a hit). For the second projection the exact second, third and fourth centered moments of $Z$ are $10239/2500$, $2523/125$ and $1143925341/6250000$. Direct enumeration of all $2^{12}$ sign vectors agrees with the CBD pair enumeration. Exact rational trace multiplication verifies the moment identity and fourth-moment inequality used above. The separate $2\mathbb Z$ example gives 14 height-two hits in 64 equally weighted sign outcomes.

A Lean replacement for the terminal numerical hypothesis would prove
$1-\texttt{B.success}\le\operatorname{err}_{\rm smooth}(H,Q)$, then require a verified upper bound at most the assigned terminal allowance. A witness for (1) consists of a cap, its tail bound, a certified strict horizontal minimum floor, a height-one bound, and an upper bound (or a deterministic exclusion) for each remaining height. The Poisson version needs the terminal covolume and CBD-weighted dual sums in physical coordinates with rigorous remainders. The finite version needs the embedded projected integer lattice, its coset law and closed-ball counts. The separate prefix and design terms still need their own budgets in a restart statement. None of the numerical results here changes the existing Lean theorems. [Current fixed-block success and reduction error](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConditionalReduction.lean) · [Existing probability proof](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessProbability.lean) · [Profile form](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessProfile.lean) · [Profile obstruction](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProfileObstruction.lean) · [Restart lift](../../SigabaNeo/Lib/Lattices/Research/Wall1/RestartLift.lean)

**Open at width 506.** A physical GSA-type witness passing the minimum, height-one and weighted higher-height tests has not been verified. The additional claim that such witnesses occur with a specified probability under a reducer is a separate design-law conjecture. At width 406 a witness with the literal model head is excluded by (3), irrespective of the dual or the reducer.

## Audit

**Verdict — MINOR CAVEATS.** The width-406 obstruction, the zero-frequency calculation at width 506, the fixed-block bound (1), and the zero-design example check out. One qualification concerns the phrase “Part 171 minimum floor.” The guaranteed quantity is the GH radius of at least $28.8095$ in the cited first pass. The physical minimum floor $27.484263$ follows **on the event** $\lambda_1(H)\ge0.954\,\mathrm{GH}(H)$. The probability of that event in the physical pass is open. If a block has minimum exactly $27.484263$, (3) rules out 99% conditional uniqueness. This is a probability statement over the plant. [Part 114](wall1_idea_drift.md) · [Part 171](wall1_budget_reallocation.md)

**Width and tail direction.** I recomputed the physical lengths at slope $s_b$ from the full $1023$-term GSA and multiplied the last $d$ lengths to obtain the terminal covolume. Independent 90-decimal interval arithmetic reproduced every displayed table interval. At $b=406$ the heads are $24.76651584\ldots$ for $d=405$ and $24.96211963\ldots$ for $d=406$. Each is the norm of the first remaining basis vector after projection off the prefix, hence an upper bound on the minimum for a block realizing that head. Both are below their respective thresholds in (3).

The independent-sign expansion gives $V=2\operatorname{tr}M^2$, $\mathbb EY^3=8\operatorname{tr}M^3$, and $\mathbb EY^4\le3V^2+48\operatorname{tr}M^4$. In the last inequality the simple four-cycles have identical signed coefficients on both sides, and the remaining trace walks have nonnegative weights. Expanding $f$ gives $-x^4+2x^3+(188/25)x^2+(312/125)x-288/125$, with $D=54756/625$. Substitution at $V=15\cdot405/4$ puts the lower bound on $\Pr(W>2/5)$ in $(0.02137350588,0.02137350589)$. This proves the strict failure claim uniformly in the projection when the head meets (3). Part 103 uses lower-tail Cantelli to bound *success* when the squared minimum is below the mean of $R^2$. At $d=505$ its necessary floor is $27.45375948\ldots$. The fourth-moment argument in (3) raises this to $27.85510537\ldots$. At width 406, Part 147 reports a design-side **upper-bound term** exceeding $2^{457}$ for a penultimate unit-minimum event. The present failure lower bound concerns the terminal plant conditional on a short physical head. [Part 103](wall1_width_scan.md) · [Part 147](wall1_uncovered_lines.md)

**Width 506 and the dual sum.** The sums of the higher-height zero modes are $4.46272\cdot10^{-125}$ at $d=505$ and $4.60614\cdot10^{-126}$ at $d=506$, rounded to six significant digits. For $H=2\mathbb Z$, $k=2$ and $w=1/2$, the CBD coefficient is exactly one and the matched Gaussian coefficient is $e^{-3\pi^2}$. Independently summing Part 172's 408 raw exit bounds reproduced its quoted enclosure. That number bounds a probability over designs. A dual minimum can enter a packing bound for the Gaussian-damped series in (2), but verifying a sufficiently small bound for that series remains a separate obligation. Part 173's cap-saturation calculation concerns a separate per-mark ratio. The width-506 physical GSA case remains open. [Part 172](wall1_transference.md) · [Part 173](wall1_gated_theta.md)

**Fixed-block event.** On $Z\le a$, the strict horizontal floor handles ties at height zero. At height one the one-sided linear tail has exponent $-\|h\|^2/12$. For $2\le k\le K$, a hit contributes at least one to the closed-ball count in $ky+H$, including when $r_k=0$. Its unconditional first moment is exactly $A_k$ and is at most $M_k(t)$ for every $t>0$ on a physical graph. Thus either bound covers the hit intersected with the cap, with $p_a$ paid once. Taking the union over the three height tests bounds the complement of the signed-plant event in `allHeightsUniquenessCriterion`. Part 39 averages over designs for a prescribed coordinate deletion, and Part 101 bounds a minimum over designs. The Lean theorem `failure_le_errGeom` uses its own theta-product error. `recordedBlock_impossible` assumes that error and a simultaneous prefix allowance. Formula (1) is a paper bound on the same fixed-block failure event. [Part 39](wall1_projected_reference.md) · [Part 94](wall1_threshold.md) · [Part 101](wall1_qary_rogers.md) · [Criterion](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessCriterion.lean) · [Profile bound](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessProfile.lean) · [Profile obstruction](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProfileObstruction.lean)

**Physical and exact controls.** At the zero design the ordered orthogonal basis has 512 unit secret directions and 511 error directions of length 3329. Leaving $d$ error directions gives exactly $H=3329\mathbb Z^d$. Since $k\sqrt a+r_k\le B<3329$ on all four rows, every height charge on the cap vanishes. The largest value of (1) is $0.002173814$ rounded up, at $d=405$. This certifies the terminal test for that basis alone. Independent enumeration of the $4096$ sign tuples also reproduced both residue histograms, the $2458/4096$ ball count, and all three reported centered moments. The separate one-dimensional example gives $14/64$ height-two hits.
