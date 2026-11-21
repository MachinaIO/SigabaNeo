# The first tour from a graph basis

For the $qI$-first order, an unread graph column supplies a uniform element of a **marked subgroup** of the retained torus, at physical height one. The subgroup itself has a deterministic update given the selected vector. This gives a finite recursion for the full path law. At $(m,n,q)=(511,512,3329)$, a simultaneous 99% lower bound on the retained minimum in its own GH units can be at most 0.203553 at width 406 and 0.182568 at width 506. The obstruction occurs with probability one in the initial window. The terminal-only question is different.

## Filtration and append law

Use independent uniform columns over $\mathbb Z/q$, with fixed integer representatives. Reveal a column only when it enters the window. Start with the first $b$ columns, choose a primitive shortest vector of the projected window, freeze its direction, retain the entire orthogonal quotient and slide by one. Fix ties, for example by lexicographic order on the ambient coordinates of all signed minimizers. Stop after the last full window. The basis update within a window must preserve its integral span. This models exact forward calls without lookahead. A BKZ implementation with preliminary global LLL, swaps across the right boundary, or decisions based on the suffix needs a separate filtration argument.

After processing $t$ original columns, let $M_t$ be their integer span, $F_t$ their real span and $S_t\subset F_t$ the span of the frozen directions. Then $E_t=F_t\cap S_t^\perp$ has dimension $r=b-1$, and the retained lattice is $\Lambda=P_{E_t}M_t$. Indeed primitive shortest-vector completion and projection remove exactly one integral generator at every step. The projected next raw column $x$ is the sum of $P_{E_t}x$ and $P_{F_t^\perp}x$. Its displacement is the former modulo $\Lambda$, and its height is the norm of the latter. These formulas also follow by composing the successive projections, whose removed directions are mutually orthogonal.

Until all $m$ horizontal axes have entered, appending the next $q$-axis has zero displacement and height $q$. Thereafter $F_{m+j}=\mathbb R^m\oplus\mathbb R^j$ in the used coordinates. For $x=(a,e_{j+1})$ the new unit coordinate contributes the entire perpendicular vector and zero displacement. Write $P=P_{E_t}$ and $T=E_t/\Lambda$. Conditional on the revealed columns and all past reducer choices,
$$
 U=[P(a,0)]\sim\mathrm{Unif}(H),\qquad
 H=\mathrm{im}\big((\mathbb Z/q)^m\longrightarrow T,\quad z\longmapsto[P(z,0)]\big).
$$
The map is well-defined since $qP(e_i,0)\in\Lambda$, and all fibers have equal size. In a basis of $\Lambda$, the columns of the integer matrix $C$ representing these $m$ vectors generate $H$ modulo $q$ after division by $q$. A nonzero Smith factor $s$ contributes $q/\gcd(q,s)$ to the order. At the first graph append $H=T[q]$ when $m\ge b$, since successive cubic windows freeze coordinate axes. Later, full torsion is a condition on $C$, not a consequence of freshness.

For any other fixed order the same two projections give the exact joint law by enumerating the $q^m$ representatives of an unread graph column with equal weight. A deterministic input column has a point-mass conditional law. A missing horizontal axis can contribute to the perpendicular vector, so even the original GS height may be random. For example a first graph column $(a,1)$ has height $\sqrt{1+a^2}$ for $m=n=1$. Reduction preserves that input GS height at the append, but its value need not be fixed before the reveal. The subgroup proof needs the projected period relations. Changing representatives with horizontal axes still unread can change the prefix itself.

## Transition and loss of randomness

Work in physical units. For $u\in H$ form $W=\Lambda+\mathbb Z(\tilde u+h e)$ with $e$ the new orthogonal unit axis. Any representative works. Select $v$ by the fixed rule, let $Q$ project perpendicular to $v$ within the window, and set
$$
 \Lambda'=QW,\quad D'=\det(\Lambda)h/|v|,\quad H'=Q_*H.
$$
Here $Q_*:T\to v^\perp/\Lambda'$ is induced by inclusion followed by projection and is well-defined since $Q\Lambda\subset\Lambda'$. It carries every old horizontal generator to its new projection, proving the update throughout the graph phase. Average these outputs with mass $1/|H|$ each. The reported shape is $(D')^{-1/r}\Lambda'$; with normalized coordinates the input height must likewise be $h/\det(\Lambda)^{1/r}$ and one must retain the scale for the next append. Retain ambient frames for coordinate-dependent ties. This is the marked kernel $K_h$; physical lattice, subgroup and frame suffice in the graph phase. In particular subgroup order can only decrease. For example, on a first zero graph draw the vertical unit vector is uniquely shortest up to sign ($q>1$), and the full old torsion survives. If a horizontal axis is selected instead, its torsion line dies. The kernel can be computed by rational projections in original coordinates, comparing squared lengths exactly.

Erasing the subgroup does not specify this prescription. For example take $\Lambda=2\mathbb Z^r$, $h=1$, and compare $H=0$ with the subgroup generated by the first unit coordinate modulo $\Lambda$. The nonzero displacement selects a diagonal of length $\sqrt2$ and yields a rectangular quotient with one side $\sqrt2$ and the others 2, whereas the zero displacement returns the cube. This tests the marked kernel on its abstract state space. A special marginal recursion on reachable states would require a posterior on the marks.

For fixed parameters and ties the finite recursion gives a computable, time-dependent law. To compute a survival probability exactly, discard each branch at its first violation and sum the remaining masses, starting with the deterministic cubic quotient for $m\ge b$. This sums conditional probabilities over actual histories without treating successive minima as independent. Exact comparison at a quantile can equivalently order the algebraic scores $\lambda_1^{2r}/\det(\Lambda)^2$ before applying the common GH factor. Finite-time shape laws have TV distance one from nonatomic Haar for $r\ge2$. This does not decide weak approximation of a particular observable or invariance under an artificially chosen Haar initialization with a distribution on marks.

Even full torus refresh cannot give a useful uniform one-step lower quantile on arbitrary inputs. At determinant one take two orthogonal sides $\epsilon$ and the other $r-2$ sides $\epsilon^{-2/(r-2)}$, $r>2$. At fixed $h>\epsilon$ a shortest vector is horizontal of length $\epsilon$, and an independent perpendicular side of that length survives. The normalized output minimum is at most $\epsilon(\epsilon/h)^{1/r}$ for every displacement. On the larger marked space there is also no global Doeblin minorization at $h=1$: with trivial subgroup, any rectangular lattice with all sides longer than one returns itself, giving disjoint absorbing states. Neither construction estimates the frequency of such states on the graph path.

A less expensive conditional bound than quotient enumeration uses only torus ball counts. Put $D=\det(\Lambda)$, $s=\lambda_1(W)$ and $R=(cG_r(Dh)^{1/r}/\alpha)^{r/(r+1)}$, where $\alpha=\sqrt3/2$. The lift bound proved below gives $Y'\ge\alpha s^{1+1/r}/(G_r(Dh)^{1/r})$. Thus failure implies $s<R$. If $\lambda_1(\Lambda)\ge R$, only nonzero vertical layers matter. By sign symmetry one may use positive layers. Since $kU$ is uniform on $kH$, the conditional failure probability is at most
$$
 \min\left(1,\sum_{1\le k<R/h}
 \frac{\#\{w\in kH:\operatorname{dist}_T(w,0)<\sqrt{R^2-k^2h^2}\}}{|kH|}\right).
$$
Otherwise use the upper bound one. This accounts even for layers divisible by $q$. Calling the resulting state function $p_t$, the probability of any graph-phase failure before the end is bounded by the sum of $\mathbb E[\mathbf1_{\text{survival through }t}p_t]$ over graph appends, plus the initial failure probability. This follows by partitioning by the first failure. Evaluating these counts on the surviving states is the outstanding probabilistic estimate.

## A simultaneous certificate

Let $G_r=V_r^{-1/r}$ with $V_r$ the unit ball volume. For the cubic prefix every retained ratio $Y=\lambda_1/(G_r\det(\Lambda)^{1/r})$ equals $1/G_r$. To give a rigorous lower endpoint as well, put $\alpha=\sqrt3/2$. If $s$ is the shortest window length, every nonzero quotient vector has a lift with parallel component at most $s/2$, so its norm in the quotient is at least $\alpha s$. At a graph append $s\ge\min(1,\lambda_1(\Lambda))$ by perpendicular height. Thus after $j$ graph columns the physical minimum is at least $\alpha^j$ by induction. The GH radius of the retained lattice is at most its covering radius (a covering ball must have volume at least the covolume). Orthogonal projection bounds the latter by the covering radius of $M_{m+j}$ in its span. Backward rounding in its original GS basis leaves orthogonal errors at most half each GS length, hence this radius is at most $\sqrt{mq^2+j}/2$. Consequently, simultaneously over all full windows, with probability one,
$$
 \min_t Y_t\ \ge\ \min\{1/G_r,\ 2\alpha^n/\sqrt{mq^2+n}\}.
$$
This pathwise estimate incurs no multiplication of probability losses. It gives a weak numerical floor. Writing $c_*$ for the largest threshold with $\Pr(\min_tY_t<c_*)\le0.01$, the certified brackets are

| Width | Lower bound on $c_*$ | Upper bound on $c_*$ |
|---|---:|---:|
| 406 | $2.7554\cdot10^{-37}$ | 0.203553 |
| 506 | $2.7554\cdot10^{-37}$ | 0.182568 |

The upper endpoints round the exact cubic obstruction outwards. Determining the best 1% constants inside these brackets remains open here. The finite recursion was not enumerated at rank 1023. The brackets concern rank-$r$ quotients throughout the first pass, including the initial cubic phase. For a terminal-only test the same deterministic floor applies and the cubic upper endpoint does not follow.

In subsequent tours all graph columns have already been revealed. Given the original matrix and deterministic reducer history the next displacement is known, and a coarser filtration requires the posterior of the reused columns. Part 47's independent plant, Part 52's asymptotic transfer, Part 104's fresh-selector counterexample and Part 105's single Haar-block density address distinct laws. In particular the Haar calculation cannot remove the cubic obstruction in this fixed order. [Wall 1](../PROOF_GAP.md) · [Marked reducer](wall1_markov_reducer.md) · [Selector chain](wall1_chain_law.md) · [Haar selection](wall1_selection_law.md)

## Interval checks

```python
from mpmath import iv
iv.dps = 60
I = iv.mpf
volume = [I(1), I(2)]
for k in range(2, 506):
    volume.append(2 * iv.pi * volume[k-2] / k)
floor = 2 * (iv.sqrt(3)/2)**512 / iv.sqrt(I(511)*3329**2 + 512)
assert I('2.7554e-37') < floor < I('2.7555e-37')
for r, lo, hi in [(405, '0.203552', '0.203553'),
                  (505, '0.182567', '0.182568')]:
    cubic = volume[r]**(I(1)/r)
    assert floor < I(lo) < cubic < I(hi)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT, for the specified qI-first, no-lookahead tour with the ambient-coordinate lexicographic SVP
tie rule.

**What was verified.**

* **Height one.** The F^⊥ component of (a_j, e_j) is e_j.
* **Conditional uniformity.** The history is a function of a_1..a_{j−1}, ties included, and the displacement map factors through
  (Z/q)^m. A tie rule that inspected a_j would break this.
* **Recursion.** The update H' = Q_*H is exact.
* **Cubic obstruction.** The bound V_{b−1}^{1/(b−1)} is exact, and strictness matters at the cubic value.
* **Deterministic floor.** The bound (√3/2)^j combined with the covering radius is valid.

**Certified enclosures.**

| Quantity | Value |
|---|---|
| Cubic upper bound, b = 406 | 0.2035524700… |
| Cubic upper bound, b = 506 | 0.1825670712… |
| Deterministic floor, both widths | 2.7554285823…·10⁻³⁷ |

**Not computed.** The actual simultaneous and terminal 99% thresholds.
