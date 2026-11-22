# Which uncovered lines contribute to the terminal charge?

At width 506, in the marginal restart law of Part 117, the probability that the penultimate minimum is at most one is below $2^{-135.60}$. Projective lines having a nonzero class with a representative of length at most $0.954$ times the old Gaussian-heuristic radius contribute less than $3.114918\cdot10^{-6}$ to the horizontal charge on the other histories. The entire residual positive-height first moment **on horizontal wins** is below $9.35974\cdot10^{-10}$. All three bounds include the history average. The horizontal void on longer lines passing the old-plane test and the positive-height multiplicity on nonhorizontal wins remain open.

## Laws and normalizations

Use the exact forward pass, unit graph heights, the inherited signed ambient lexicographic tie rule, and $q=3329$. All probabilities concern the uniform design. The CBD(3) plant is independent and does not enter these counts. Write $d=\beta-1$, $m$ for the number of surviving raw horizontal rows, $T$ for the number of graph selections *before* the terminal draw in the experiment in question, and $D_0=q^m$. The width-506 restart has $(d,m,T,c)=(505,400,406,.954)$, with 105 independent graph columns at initialization. In the original passes use $(405,405,511,.925)$ and $(505,505,511,.954)$, starting from the cube after the deterministic cubic freezes. Each experiment uses 512 graph columns in total. The $0.00977696$ budget applies to the **restarted 506** law. Part 117 transfers a terminal event to the original pass with additive error below $0.00022304$. Its event coupling alone does not transfer an unbounded plane count with the same error. [First-tour law](wall1_first_tour.md) · [Restart coupling](wall1_idea_round2.md) · [Plane count](wall1_plane_count.md)

At a state let $L,H,D,x_0,t$ be its old lattice, mark, covolume, signed winner, and minimum. Set $h=G_dD^{1/d}$, $G_d=V_d^{-1/d}$, and $R(s)=cG_d(D/s)^{1/d}$. Let $I$ denote the indicator that $\lambda_1(\pi_{x_0^\perp}L)<R(t)$, and $b$ the horizontal-win indicator on the fresh draw. A plane is charged when it is saturated, contains the actual winner of length $s$, and has area below $sR(s)$. Let $N_+$ count the charged planes with nonzero height image. The target is
$$
 \mathcal C=\mathbb E[Ib]+\mathbb E[(1-Ib)N_+].
$$
A plane through the winner corresponds to one primitive unoriented line in the retained quotient. We use that bijection throughout. [Part 120 and audit](wall1_plane_count.md) · [History averages and audit](wall1_averaged_charge.md)

## 1. Linearity on fixed raw lines

Let $V=\mathbb F_q^m$, let $A$ denote the old design, and write $\phi_A:V\twoheadrightarrow H_A$ for the displacement map. For a marked line $P$, let $b_A(P)$ count the nonzero scalars beaten at some height as in Part 146. For every **fixed raw** line $J\le V$ choose a generator $u_J$. On $\phi_A(J)\ne0$ put $P_J=\phi_A(J)$. Formula (3) of Part 146 gives two contributions on $t>1$.
$$
\begin{split}
 h_{\rm empty}
 &=\frac{q-1}{q^m}\sum_J
   \Pr[I=1,\ t>1,\ \phi_A(J)\ne0,\ b_A(P_J)=0],\\
 h_{\rm partial}
 &=q^{-m}\sum_J\sum_{a\ne0}
   \Pr[I=1,\ t>1,\ \phi_A(J)\ne0,\ 0<b_A(P_J)<q-1,
              \ b(au_J)=1].
\end{split}                                                    \tag{1}
$$
Here $b(z)$ tests the terminal draw with prescribed raw value $z$. Indeed, the zero fiber loses when $t>1$. Each nonzero raw vector lies on exactly one raw line. If the mark has rank $r$, precisely $q^{m-r}$ raw lines map onto any given marked line, by counting the preimages of a fixed generator. This proves (1) with a fixed denominator even when the rank varies with the selected history. The third contribution is $\Pr(I=1,t\le1)$. [Projective void and signed ties](wall1_subspace_void.md)

**Exact design probabilities.** On a proposed history all projections are fixed. For a prescribed draw $z$, a height $k>0$ at the terminal window has old components $P_E(x,y)$ with
$$
                       Ay=x-kz\pmod q.
$$
It beats $x_0$ when $\|P_E(x,y)\|^2+k^2<t^2$, or at equality if one of its signed lifts precedes $x_0$. It suffices to test $1\le k\le(q-1)/2$, including both signs, by Part 146. The kernel test is the existence of a lift with $k=1$ and zero old projection. For the old-plane test use $Ay=x$, $0<\|\pi_{x_0^\perp}P_E(x,y)\|<R(t)$. At each earlier step require presence of the proposed winner and absence of every preceding candidate in that prefix. For each projected point take the union over all its admissible raw residue pairs. Rational projections give discrete projected integer lattices, finitely many points in each bounded ball, and finitely many residue pairs per point. In particular equality of projected points does not entitle one to choose an arbitrary lift for a presence or exclusion test.

These rules give a finite Boolean combination of raw linear tests for every summand of (1), including the union over all nonzero $a$ needed to distinguish empty and partial lines. For required pairs $AY=X$ its mass is zero unless $\ker Y\subseteq\ker X$, and otherwise equals $q^{-m\operatorname{rank}Y}$, since every row is prescribed on the input span. Expand unions and exclusions by inclusion–exclusion, or group by spans as in Part 146, and sum over disjoint winner histories. This gives an exact finite computation. The raw projections are rational, and all squared lengths and squared covolumes on a fixed flag are rational. At the two recorded odd ranks, $V_d$ is a nonzero rational multiple of $\pi^{(d-1)/2}$. Thus a positive algebraic length cannot equal the old-plane or terminal GH cutoff, by transcendence of $\pi$. Interval refinement decides those strict comparisons. Winner ties are rational comparisons. A single rank weight for the terminal lifts omits the old-plane and earlier winner tests. Part 105's Haar selection law does not evaluate any of these design-conditioned voids. Part 117 supplies a marginal coordinate-graph law at restart, followed by adaptive projections. [Fixed-subspace count](wall1_finite_family.md) · [Ambient counts](wall1_qary_gap.md) · [One-step Haar law](wall1_selection_law.md) · [Modular exclusions and audit](wall1_subspace_void.md)

## 2. How much mass can short lines carry?

We use a Gaussian count that remains valid after further projections along any predetermined old flag. Let $\Gamma=P_F M$ have rank $r$ and covolume $D_\Gamma$, with mark $H_F$ projected to the same quotient. Its extension by the mark is $K=P_F\mathbb Z^N$, since adding horizontal integer vectors to the raw graph $M$ generates every coordinate unit. Thus $\det K=D_\Gamma/|H_F|$, and $K^*=F\cap\mathbb Z^N$. For $z>0$ write $\theta(z)=\sum_{n\in\mathbb Z}e^{-\pi z^2n^2}$. Then
$$
 \frac{1}{|H_F|}\sum_{y\in K}e^{-\pi\|y\|^2/z^2}
 \le \frac{z^r\theta(z)^r}{D_\Gamma}.                              \tag{2}
$$
Indeed Poisson summation gives $z^r/D_\Gamma$ times the dual theta series. Some $r$ coordinate rows together give an injective map on $F$. Dropping the other coordinates shortens vectors and injects $K^*$ into $\mathbb Z^r$. This proves (2), also for $r=0$. For a nonzero height $k\bmod q$, averaging the shifted $\Gamma$-sum over the uniform marked draw gives exactly the left side, since multiplication by $k$ permutes the mark. [Mark extension and duality](wall1_dual_cusp.md)

Call a marked line short at radius $u$ if **some nonzero class on it** has a representative of norm at most $u$. This excludes short vectors already in $L$ whose class is zero. Distinct short lines furnish disjoint pairs of opposite representatives. Even charging all $q-1$ scalars on each short line, their total conditional mass is at most
$$
    \frac{q-1}{2D}\,e^{\pi u^2/z^2}z^d\theta(z)^d.                  \tag{3}
$$
This follows from (2) by majorizing the closed ball indicator. No independence among heights or lines is used. Put $u=ch$, $z=u\sqrt{2\pi/d}$, and $J_d=\Gamma(1+d/2)(2e/d)^{d/2}$, where the gamma function here is Euler's. The bound becomes $(q-1)J_dc^d\theta(z)^d/2$.

For numerical lower limits on $z$, let $a=d/(d+1)$, let $C^2=56.2142$ at 506 and $45.6963$ at 406, and put
$$
 L_n=a^n m\log q-(d+1)(1-a^n)\log C .
$$
On every history the covolume $D_n$ after $n$ selections satisfies $\log D_n\ge L_n$. Indeed, the window determinant is $D_{n-1}$, its shortest length is at most $CD_{n-1}^{1/(d+1)}$ by the Hermite bound, and one divides $D_{n-1}$ by that length. This also proves the bound directly for the marginal restart. The numerical caps used here are rounded upwards. [Finite-rank Hermite certificates](wall1_hermite_caps.md) · [Determinant recursion](wall1_idea_drift.md)

| Terminal law | Lower bound on old $h$ | Upper bound on the mass of all short lines at $ch$ |
|---|---:|---:|
| 506 restart | 31.9321 | $3.114918\cdot10^{-6}$ |
| 506 original | 29.0201 | $3.114918\cdot10^{-6}$ |
| 406 original | 12.4232 | $4.205866\cdot10^{-9}$ |

In particular, on $1<t\le ch$ **every nonempty line is short**. A beating lift gives a nonzero horizontal class on that line of norm at most $\sqrt{t^2-1}$. On this stratum the conditional horizontal-win probability is at least $1-|H|^{-1}$ minus the table entry, and the contribution outside the zero fiber and short lines is entirely on empty lines. The term $|H|^{-1}\le1/D$ follows from $\det K\le1$, since its dual is integral. This identifies when long empty lines dominate conditionally. The distribution of $I,t/h$ needed to infer their unconditional weight is still unknown. For example, on the full-span family of Part 146 put $Q=q^{400}$. Of the nonzero displacements, $Q-1-401(q-1)$ lie on empty lines and $401(q-3)$ survive on partial lines. Dividing by $Q$ gives their respective conditional charges. The family itself contributes less than $Q^{-510}$ to the design average. [Full-span family](wall1_subspace_void.md)

## 3. A separate bound at the unit threshold

**Proposition.** At the penultimate state the 506 restart satisfies $\Pr(t\le1)<2^{-135.60}$. The direct bound for the original 506 pass is $2^{-33.84}$. Both bound the entire first term $\Pr(I=1,t\le1)$.

First note the strict endpoint property. A nonhorizontal winner cannot leave a quotient vector of length at most one. Such a vector, made primitive if necessary, would lift to a plane of area at most $s$. Its height image is $j\mathbb Z$, and its old primitive kernel vector $x$ gives area at least $j\|x\|\ge t\ge s$. Equality forces $j=1,\|x\|=s=t$, and the plane lies over the single horizontal direction $x$. The old-coordinate part of the nonhorizontal winner is parallel to $x$ and has length strictly smaller than $t$, so the earlier signed choice of $x$ wins that tie. This contradicts the selection rule. In particular, a short fresh vector alone cannot certify entry into the unit-minimum event.

For the probability bound let $v_1,\ldots,v_T$ be the successive physical orthogonal winners and append the signed shortest vector of the penultimate lattice as $v_{T+1}$. Suppose its length is at most one. Let $i$ be the arrival index of the **last suffix coordinate used anywhere** in these vectors, if one is used. After and including its arrival, all $k=T-i+2$ directions belong to successive projections of the one window at $i$. Indeed the removed directions have no component in any later raw coordinate. A lift with zero projection on these later coordinate axes has zero raw coefficients there, by the identity graph input block. The window at $i$ therefore supplies lifts of the entire remaining flag. In particular $k\le d+1$.

Let $s_1,\ldots,s_k$ be these flag lengths. In the projected span of any tail of length $l$, lifts of the $l$ winners generate a rank-$l$ sublattice of determinant equal to the product of their lengths by Gram–Schmidt. Its first length is a shortest vector, since it was a global minimizer in a lattice containing that sublattice. If $g_l\ge\gamma_l$ is a Hermite cap, the first length is at most $\sqrt{g_l}$ times the geometric mean of all $l$ lengths. The log of that geometric mean exceeds the log mean of the last $l-1$ by at most $\log g_l/[2(l-1)]$, by moving the first term to the left. Starting with $s_k\le1$ gives the explicit cap on the head of each tail
$$
 B_l=\sqrt{g_l}\prod_{u=2}^{l}g_u^{1/[2(u-1)]},\qquad B_1=1.       \tag{4}
$$
This argument only concerns a flag already present in one window.

Suppose the first $j$ directions of the flag have zero $i$-th coordinate and the next direction uses that coordinate, $0\le j<k$. The first $j$ must be the deterministic signed successive shortest vectors **in the old lattice alone**, because that lattice is available at all these selections and each chosen direction belongs to its corresponding projection. Thus given the history *before* draw $i$, these $j$ old projections may be tested without seeing the new column. If any of their lengths exceeds its cap from (4), the event is impossible. Otherwise the remaining rank is $r=d-j$, with old covolume at least
$$
 D_* =\exp(L_{i-1})\Big/\prod_{p=0}^{j-1}B_{k-p}.
$$
Some nonzero-height vector relative to column $i$ must now have length at most $u=B_{k-j}$. All relevant $B_l<q$ at these dimensions, so every possible positive height acts bijectively on the projected mark. Counting both signs by using positive heights only, applying (2), and using $\sum_{n\ge1}e^{-\pi n^2/z^2}\le\int_0^\infty e^{-\pi x^2/z^2}dx=z/2$, gives the unconditional union-bound term
$$
 E_{ij}=\frac{e^{\pi u^2/z^2} z^{r+1}\theta(z)^r}{2D_*},
 \qquad z=\max(1,u\sqrt{2\pi/(r+1)}).                               \tag{5}
$$
In applying (5) we impose no restrictions on the unread later columns and do not condition the uniform $i$-th column on its being the last used one. This is the distinction that permits a Part 117 type estimate in an adaptive suffix.

If no suffix coordinate is used, $T+1\le d$ is necessary. This is possible only in the restart among our three laws. The restart graph then has minimum at most $B_{T+1}<q$. Each nonzero candidate in that ball has nonzero input residue if it belongs, hence membership probability $q^{-m}$. Counting sign pairs with enclosing unit cubes gives the extra term $E_0=V_d(B_{T+1}+\sqrt d/2)^d/(2q^m)$. Use $E_0=0$ when dimension precludes the flag. Summing (5) over the possible indices proves the proposition with the following evaluations.

| Law | Number of $(i,j)$ terms | Largest term at $(i,j)$ | $\log_2$ of the evaluated upper sum |
|---|---:|---:|---:|
| 506 restart | 83,027 | $(218,0)$ | $(-135.601,-135.600)$ |
| 506 original | 128,270 | $(318,0)$ | $(-33.848,-33.847)$ |
| 406 original | 82,620 | $(327,0)$ | $(461.020,461.021)$ |

In the restart $E_0<2^{-1036}$. At 406, the largest individual bound already exceeds $2^{457}$. In this estimate the loss occurs when the latest used column supplies the very first direction of a long old flag. At 406 a separate upper bound is $1-[(1+2d)/q^d]^{511}$. To see this, take all 511 centered raw columns of length at most one. If the first $n$ raw graph columns form a matrix $B$ and their span has been frozen, the old lattice consists of projections of $(qz,0)$ perpendicular to the graph of $B$. Their squared lengths are $q^2z^\top(I+BB^\top)^{-1}z$, by orthogonal projection onto the graph complement. The old minimum is at least $q/\sqrt{1+n}$ since $\|B\|_{\rm op}^2\le n$. Each new raw column has projected length at most $\sqrt2$. Heights of magnitude at least two are longer, and adding a nonzero old vector at height one leaves horizontal length at least $q/\sqrt{1+n}-1>\sqrt2$. Thus the fresh graph column wins up to sign at every step, proving the induction. The resulting old minimum exceeds one on the entire cylinder of the stated probability. This supplies no budget-sized unit estimate there. The positive lower bound from the many-zero family in Part 144 is compatible with the 506 result. [Unit-minimum family and audit](wall1_horizontal_core.md)

## 4. Residual planes on horizontal and nonhorizontal wins

**Horizontal winner.** Uniformly over terminal histories, the conditional expectation of $b(1-I)N_+$ is bounded by the last column below. This expectation retains the probability of winning. Conditioning *on* a win would change the measure.

| Terminal law | Lower bound on output GH | Upper bound on $\mathbb E[b(1-I)N_+\mid A]$ |
|---|---:|---:|
| 506 restart | 31.6943 | $9.35974\cdot10^{-10}$ |
| 506 original | 28.8095 | $9.35974\cdot10^{-10}$ |
| 406 original | 12.3365 | $1.42158\cdot10^{-12}$ |

*Proof.* Discard states with $I=1$ or with no possible horizontal win, where the charge vanishes. Force projection off the fixed old winner $x_0$. The quotient is an extension of $\Gamma=\pi_{x_0^\perp}L$ by a unit-height column whose displacement is uniform on the projected mark. Here $\operatorname{rank}\Gamma=d-1$ and $\delta=\det\Gamma=D/t$ is also the determinant of the forced quotient. A true positive-height plane on a horizontal win gives a primitive quotient vector, signed to have positive height. Drop primitivity and the terminal winner test to bound its joint first moment. Every contribution has height $1\le j<R= cG_d\delta^{1/d}$. The old projected $q$-axes span the old projected space, so $\lambda_1(\Gamma)\le q$. Since $I=0$ we have $R\le\lambda_1(\Gamma)\le q$. Even at equality the strict radius excludes $j=q$. All heights in the sum therefore preserve uniformity. From (2) and the same integral over positive heights used in (5), the result is bounded by
$$
 \frac{e^{\pi R^2/z^2}z^d\theta(z)^{d-1}}{2\delta}
 =\frac{J_d c^d}{2}\theta(z)^{d-1},
 \qquad z=R\sqrt{2\pi/d}.                                           \tag{6}
$$
Since a horizontal win is possible, $\log\delta\ge L_{T+1}$ on at least one actual continuation, hence for this fixed $\delta$. Monotonicity of $\theta$ gives the table. There is no division by the probability of a horizontal win. ∎

**Nonhorizontal winner.** All witness planes now have positive height. Incidence and winner exclusions can still be retained exactly by the finite design tests in §1: for each prescribed terminal winner enumerate the primitive lines in its projected window below $R(s)$, counting each once. Equivalently use Part 120's saturated-plane filter, including its average on the fiber of $jU$. An upper bound that can actually be evaluated results from dropping the plane's incidence with the selected subspace in the *dual* Gaussian sum below. It is far above the budget.

Write $\Lambda$ for the actual final rank-$d$ quotient, $\delta=\det\Lambda$, $f=\exp(L_{T+1}/d)$, $N=m+512$, and $z_0=q^{m/N}$. On each draw even the sum of *both* charges is at most the number of primitive unoriented lines of $\Lambda$ below $cG_d\delta^{1/d}$. If $Ib=1$, at least one horizontal witness exists and the residual is zero, and otherwise the charged planes inject into those lines. Poisson-majorize the entire ball at scale $z=z_0\delta^{1/d}/f\ge z_0$. Its prefactor after dividing by two is independent of $\delta$. The dual of the projected lattice consists of the vectors of the raw graph dual $M^*$ in the retained space. Dropping this last constraint and using $z\ge z_0$ gives
$$
 \mathcal C\ \le\
 \frac12 e^{\pi(cG_df/z_0)^2}(z_0/f)^d\,
 \mathbb E_A\sum_{\xi\in M^*}e^{-\pi z_0^2\|\xi\|^2}.               \tag{7}
$$
Here the raw graph has $m$ rows and 512 independent columns, including the restart columns. The zero horizontal residue in its dual contributes $\theta(z_0)^N$. For a nonzero horizontal label, the 512 vertical residues are independent uniform field elements, by the row count. More explicitly take the horizontal fine-grid coordinates $p/q$, $p\in\mathbb Z^m$. When $p\not\equiv0$, each required vertical numerator is uniform modulo $q$. Summing over $p$ gives the second term
$$
 \left[\theta(z_0/q)^m-\theta(z_0)^m\right]
                      \left[\theta(z_0/q)/q\right]^{512}.
$$
By one-dimensional Gaussian Poisson summation the bracketed contribution times its factor is at most $\theta(q/z_0)^N$, since $z_0^N=q^m$. Using the two upper bounds in (7) gives $\log_2\mathcal C<1316.021$ in the 506 restart, $<1725.762$ in the 506 original, and $<1555.430$ at 406. The count in (7) can exceed one on a single draw. The two ambient-dual terms in the majorant are each almost one. The large factor is $(z_0/f)^d$. The estimate allows the full ambient dual at the smallest admissible determinant after projection. It does not show that actual low-determinant histories carry that mass. [Dual inheritance and its audit](wall1_dual_cusp.md)

## 5. Verification

The numerical bounds use the exact Hermite values in dimensions 1 through 8 and 24 and Blichfeldt's $g_l=(2/\pi)\Gamma(2+l/2)^{2/l}$ otherwise in (4). The respective exact caps are $1,2/\sqrt3,2^{1/3},2^{1/2},8^{1/5},(64/3)^{1/6},64^{1/7},2$ and (4). All displayed upper estimates for $\theta(x)$ use $1+2v/(1-v^3)$, $v=e^{-\pi x^2}$, from the gaps between consecutive positive squares. [Wen and Chang, Table I and equation (10)](https://www.cs.mcgill.ca/~chang/pub/WenC18.pdf)

The following pseudocode reproduces the sum column of §3. Evaluate real operations by outward-rounded interval arithmetic (36 decimal digits were used) and skip an empty range. In all comparisons defining the maximum the interval endpoints select the same branch.

```text
P[0] = 0
for l = 1,...,d+1:
    logB[l] = log(g[l])/2 + sum(log(g[u])/(2*(u-1)), u=2,...,l)
    P[l] = P[l-1] + logB[l]
sum_bound = E0
for i = 1,...,T:
    k = T-i+2
    if k > d+1: continue
    for j = 0,...,k-1:
        r = d-j
        u = exp(logB[k-j])
        log_det_lower = L[i-1] - P[k] + P[k-j]
        z = max(1, u*sqrt(2*pi/(r+1)))
        v = exp(-pi*z*z)
        sum_bound += exp(pi*u*u/z^2 + (r+1)*log(z)
                         + r*log(1+2*v/(1-v^3)) - log_det_lower)/2
```

**Exact small checks.** Scratch enumeration used integer graph congruences and rational orthogonal projections. With one row over $\mathbb F_3$, two restart columns and two suffix appends before the terminal draw, all 81 old designs and 243 final continuations were tested. The penultimate minimum was at most one on nine old designs. The last-used-coordinate pairs $(i,j)$ were $(2,1)$ six times and $(1,2)$ three times. In all nine the preceding winner was horizontal and the $j$ earlier vectors agreed with the signed old-only flag. To enumerate a projected ball of squared radius $a$, lift to the raw integer ball of squared radius $a+\sum\|v_i\|^2/4$ by successively rounding along the frozen primitive generators, newest first. All shortest-vector searches used $a=q^2$. Among the other 72 old designs, 39 had two surviving terminal displacements and 33 had none. Testing the signed height-one beaters reproduced these counts.

Two additional exact fiber checks used $L=t\mathbb Z\oplus5\mathbb Z$ and the raw map $(a,b)\mapsto(0,b)+L$ on $\mathbb F_5^2$. At $t=2$, the single marked line is partial. Each of the five nonkernel raw lines has two surviving scalars, giving 10 horizontal wins among 25 draws in (1). At $t=1$, all 25 wins are horizontal. With strict squared quotient cutoff $5/2$, $I=0$ and direct plane enumeration gives 15 incidences, precisely the three feasible second-coordinate classes $0,1,-1$ with five raw lifts each. Enumerating the positive-height layers after forcing the old winner gives the same first moment $15/25$. These examples test the counting and tie conventions at small rank.

## Remaining budget

In the marginal 506 restart, let $h_{\rm long}$ be the two terms of (1) restricted to lines with *every* nonzero class longer than $ch$, and let $F_{\rm nh}=\mathbb E[(1-b)N_+]$. The three estimates yield
$$
 h_{\rm long}+F_{\rm nh}\ \le\ \mathcal C\ <\ h_{\rm long}+F_{\rm nh}
       +2^{-135.60}+3.114918\cdot10^{-6}+9.35974\cdot10^{-10}.
$$
Thus $h_{\rm long}+F_{\rm nh}\le0.0097738441$ would suffice. **Conjecture (Part 120, open).** The full charge $\mathcal C$ is at most $0.00977696$. The slightly stronger sufficient inequality is unproved here. The largest evaluated upper bound needed in this decomposition is the first moment on nonhorizontal wins, for which (7) gives $2^{1316.021}$ at restart. For the long-line charge, at least $r=\dim H$ distinct independent marked lines contain projected coordinate generators of length at most one, all short at the tabulated radii. This gives $h_{\rm long}\le 1-[1+m(q-1)]/q^m$ since $[1+r(q-1)]/q^r$ decreases with $r\le m$. This improvement over one is negligible. Estimating (1) still requires the frequency of empty extensions and the scalar coverage of partial extensions on old-plane histories. The preceding bounds identify which configurations could exhaust the budget, without identifying the largest term in the true average.

## Audit

**Verdict — MINOR CAVEATS.** All five quantitative claims hold under their stated laws. The one clarification concerns the interpretation of the 10 horizontal wins in the $t=2$ toy example. The long-line horizontal charge and the positive-height first moment on nonhorizontal wins remain open.

**Penultimate minimum.** Fix the history just before column $i$ arrives. Until a winner first uses that coordinate, every vector in the proposed suffix flag is the signed old-only minimizer in the corresponding projection. Thus the first $j$ projections are available before revealing column $i$. The last-used-coordinate argument puts all $k$ directions in projections of one window. Applying Hermite to each tail gives (4), with $B_l<1385<q$ for every relevant $l$. For a possible first nonzero height, (5) consequently averages a permutation of the mark. Summing these unconditional upper bounds over $(i,j)$ needs no independence of the suffix events. The unit endpoint also holds. Equality in the plane-area bound forces the nonhorizontal winner's old component to be a scalar multiple of an old shortest vector with scalar of magnitude less than one. At the first nonzero old coordinate, the earlier sign of that old shortest vector precedes both candidate signs. The designated old winner precedes or equals it.

Independent 192-bit interval arithmetic used $V_0=1$, $V_1=2$, $V_l=2\pi V_{l-2}/l$, iterated the log-determinant lower bound one draw at a time and summed (5) with outward rounding. The entries below enclose the base-two logarithms of the upper sums and their largest individual terms. The extra restart term has $-1036.066<\log_2 E_0<-1036.065$.

| Penultimate law | Terms | $\log_2$ upper sum | Largest $(i,j)$ | $\log_2 E_{ij}$ there |
|---|---:|---:|---:|---:|
| 506 restart | 83,027 | $(-135.600381,-135.600380)$ | $(218,0)$ | $(-139.445,-139.444)$ |
| 506 original | 128,270 | $(-33.847276,-33.847275)$ | $(318,0)$ | $(-37.723,-37.722)$ |
| 406 original | 82,620 | $(461.020369,461.020370)$ | $(327,0)$ | $(457.013,457.014)$ |

At 406 the single term $(327,0)$ already exceeds one. The separate small-column cylinder guarantees a minimum above one on its stated mass, since its projected old minimum is at least $q/\sqrt{512}$. Neither argument certifies a budget-sized upper bound on the unit event there.

**Line and plane counts.** Each fixed nonkernel raw line maps bijectively onto its marked image. Its $q-1$ raw vectors are disjoint from those of every other raw line. Equation (1) retains $I$ inside each history average, and the zero fiber loses on $t>1$. The design rank weight applies after all necessary lift alternatives, exclusions and winner ties have been included. Part 101's ambient count and Part 105's Haar law supply no further conditioning. For (3), opposite short representatives give two distinct points per short marked line. For (6), on $I=0$ the strict cutoff gives $1\le j<R\le q$. Projecting off the fixed old winner and dropping the winner test then bounds the joint first moment $\mathbb E[b(1-I)N_+]$. Both arguments use the projected mark extension in (2).

Independent enclosures for the 506 restart are $(3.11491718,3.11491719)\cdot10^{-6}$ for (3) and $(9.35972710,9.35972712)\cdot10^{-10}$ for (6). For (7), the zero horizontal dual residue contributes $\theta(z_0)^N$. Each nonzero residue has 512 independent uniform vertical residues, and Poisson summation bounds their total contribution by $\theta(q/z_0)^N$. Dropping the retained-space restriction bounds the full charge and hence $F_{\rm nh}$. The base-two logarithms of the resulting majorants lie in $(1316.020779,1316.020780)$ at restart, $(1725.761106,1725.761107)$ in the original 506 pass and $(1555.429430,1555.429431)$ in the original 406 pass. The old and output GH floors and the upper roundings in both original-law tables also check out.

**Budget and transfer.** The identity $1-Ib=b(1-I)+(1-b)$ partitions the residual multiplicity on each draw. On $Ib=1$ the horizontal indicator pays once regardless of plane multiplicity. Its histories split into $t\le1$ and $t>1$, with the latter's winning displacements partitioned by short and long marked lines. At the proposed remaining allowance, the sum of all upper bounds is
$$
 0.0097738441+0.000003114918+0.000000000935974+2^{-135.60}
 =0.009776959953974+2^{-135.60}<0.00977696.
$$
Part 120 allows this combined charge or the sufficient equal allocation $2\times0.00488848$. Its expectation uses the marginal $400\times105$ restart graph and the fresh suffix. Part 117 adds $B(105)\in(0.000223039937819,0.000223039937820)$ once to the terminal failure probability. This gives original failure below $0.01$ if the remaining allowance is proved. A transfer of plane multiplicity itself would require control on the disagreement event.

**Exact enumeration and clarification.** A fresh scratch script enumerated graph-congruent integer lifts and compared exact squared lengths followed by signed projected ambient coordinates. Among 81 designs, nine had $t\le1$ and a preceding horizontal winner. Six had $(i,j)=(2,1)$ and three had $(1,2)$, with the old-only flag reproduced in each case. Among the other 72 designs, 39 admitted two horizontal continuations and 33 admitted zero. Across all 243 continuations this gives $9\cdot3+39\cdot2=105$ horizontal wins. A separate signed height-one test agreed on every continuation.

In the $\mathbb F_5^2$ example with $t=2$, the enumerated $10/25$ is the raw horizontal-win probability $w$. Its contribution in (1) is $I\,10/25$. Here $\lambda_1(\pi_{x_0^\perp}L)=5$, so identifying $10/25$ itself with a charge in (1) requires $R(t)>5$. At $t=1$ with the stated squared cutoff $5/2$, the independent count gives 25 horizontal wins, $I=0$, and 15 residual plane incidences.
