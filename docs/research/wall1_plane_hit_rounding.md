# Two rounding inequalities for the penultimate plane hit

**The two rounding inequalities fail to exclude a plane hit at width 506 (case iii).** In the marginal restart for plain LWE $(511,512,3329)$ with CBD(3), every draw that passes the retained-length gate also passes the necessary plane test supplied by rounding. On every such draw the plane cutoff exceeds the rounding lower bound by a factor greater than 1.13637. On band draws outside the large-GH exit the factor exceeds 1.14270. Thus removing rare histories cannot make this particular test exclude the remaining draws. An independent first moment does pay for the bottom of the band, through $0.97$ times window GH. The probability of the selected plane hit over the rest of the band remains open.

## The two tests at arbitrary rank and depth

Use the marginal uniform graph restart with $m$ outputs, $j$ initial inputs, prime modulus $q$, retained rank $d=m+j\ge2$, window rank $b=d+1$, and $T\ge1$ selections through the draw under study. Put $D_0=q^m$, $V_n=\pi^{n/2}/\Gamma(1+n/2)$, and $G_n=V_n^{-1/n}$. Just before draw $T$ the old lattice $M$ has determinant $D_-=D_{T-1}$. Appending a uniform mark at height one gives a window $W$ of the same determinant and Gaussian heuristic length $g=G_b D_-^{1/b}$. Its designated signed shortest vector $v$ has length $s=\rho g$. In $L=P_{v^\perp}W$, write $x$ for the signed shortest vector, $t=\|x\|$, and $p=\lambda_1(P_{x^\perp}L)$. Then
$$
 h=G_d(D_-/s)^{1/d}=g\left(\frac{V_b}{\rho V_d}\right)^{1/d},
 \qquad r(h)=\sqrt{1+c^2h^2},\qquad R(t)=ch\,t^{-1/d}.
$$
Here $c=477/500$ in the application. Write $B_{\rm v}$ for a win of nonzero fresh height with $\rho$ in the specified band, $1<t\le r(h)$, and $p<R(t)$. “Old plane” here means a plane in $L$ before draw $T+1$. Its lifts can use the coordinate appended at $T$. At the real instance $m=400,j=105,T=406$, and the closed band is $[0.954,1.097193]$. It contains the strict residual (b) of Part 151. The plant and the 407th draw do not enter. [Restart law](wall1_first_tour.md) · [Part 151 and audit](wall1_penultimate_tail.md)

**Proposition 1.** Put $\alpha=\sqrt3/2$. The two comparisons give $t\ge\alpha s$ and $p\ge\alpha t$. Thus at fixed $g,\rho$ the following are necessary scalar conditions for $B_{\rm v}$ are
$$
 1<t\le r(h),\qquad \alpha\rho g\le t,\qquad
 t<(ch/\alpha)^{d/(d+1)}.                                      \tag{1}
$$
In particular a hit requires
$$
 g<g_{\rm crit}(\rho):=
 \frac{c^d V_b}{V_d\alpha^{2d+1}\rho^{d+2}}.                    \tag{2}
$$
These are necessary tests. A solution of (1) alone gives no lattice witness.

*Proof.* A shortest nonzero vector is primitive. Projection along it therefore gives a lattice with determinant divided by its length, by extending the vector to a lattice basis. Lift $x$ and subtract a nearest integral multiple of $v$. Its squared length is at most $t^2+s^2/4$. Shortestness of $v$ bounds the same squared length below by $s^2$. Apply the same comparison in $L$ to a lift of a shortest vector of $P_{x^\perp}L$, obtaining $t^2\le p^2+t^2/4$. Ties satisfy both weak lower bounds. Combining the second comparison with the strict plane test gives the strict upper bound in (1). Equivalently $\alpha^d t^{d+1}s<c^d V_b g^{d+1}/V_d$. Substitution of $t\ge\alpha s$ and $s=\rho g$ gives (2). ∎

For a band with lower edge $l>0$, an explicit sufficient condition for extinction at fixed rank and depth is
$$
 G_b q^{(m/b)a^{T-1}} C^{-(1-a^{T-1})}\ \ge\ g_{\rm crit}(l),
 \qquad a=d/b,\quad C=2G_b.                                   \tag{3}
$$
Indeed, the open ball of radius half the shortest length embeds modulo the window lattice, so each winner satisfies $s_i\le C D_{i-1}^{1/b}$. Iterating $D_i=D_{i-1}/s_i\ge D_{i-1}^a/C$ gives the left side of (3) as a floor for $g$. The right side is the maximum of (2) on the closed band. For fixed $m>0,d,T$ the floor diverges with $q$. When $l=c$, multiplying (2) by $\rho$ also gives the fixed-rank bound $s<V_b/(cV_d\alpha^{2d+1})$. [Toy scaling statement](wall1_selected_scaling.md)

## What the tests exclude at width 506

**Proposition 2.** At $q=3329$, on every history and draw with $1<t\le r(h)$,
$$
  R(t)/(\alpha t)>1.13637 .
$$
If also $g<203.888$ and $\rho\ge0.954$, this improves to $R(t)/(\alpha t)>1.14270$.

*Proof.* The determinant floor uses Part 151's $C_{506}=\sqrt{56.2142}$. Each window contains $q$ times the new unit axis and satisfies its rank-506 Hermite bound. Start at $L_0=400\log q$ and iterate
$$
 L_i=\max\{L_{i-1}-\log q,\ (505/506)L_{i-1}-\log C_{506}\}.
$$
Then $D_i\ge e^{L_i}$. Also $D_i\le q^{400}$, since the wedge of integral raw lifts of the $i$ selected directions has norm $\prod_{k=1}^i s_k\ge1$. Thus
$$
 32.18553<g<3337.640,\qquad 32.02610<h<3376.98454 .
$$
The two floors use steps 405 and 406 respectively. Since $R(t)/t$ decreases with $t$, substitute $t=r(h)$. The resulting lower bound is
$$
 f(h)=\frac{ch}{\alpha(1+c^2h^2)^{(1+1/d)/2}}.
$$
Its logarithmic derivative has the sign of $d-c^2h^2$, negative throughout this interval. At the exact ceiling $G_d q^{400/d}$, $f\in(1.13637758,1.13637760)$. On the stated good histories $h<203.888(V_b/(cV_d))^{1/d}<203.02272$. Evaluating $f$ at that first upper expression gives $(1.14270642,1.14270644)$. ∎ [Part 151 determinant bounds](wall1_penultimate_tail.md)

The same scale mismatch appears before observing $t$. In the closed band $[0.954,1.097193]$, even the *smallest* $g_{\rm crit}$, at the upper edge, lies in $(2.82986,2.82987)\cdot10^{31}$. At the lower edge it lies in $(1.75482,1.75484)\cdot10^{62}$. The former exceeds the all-history GH ceiling by a factor greater than $8.47\cdot10^{27}$. Inverting (2) at $g=203.888$ gives the necessary upper ratio $1.25245766\ldots$, which only increases as $g$ decreases. The *first* comparison still enforces $\alpha\rho g\le r(h)$, the source of Part 151's upper band edge. For example, at $\rho=1$, the scalar choice $t=\alpha g>1$ satisfies this first comparison for every admissible $g$, since $ch/(\alpha g)>1.09680$. Proposition 2 shows why the plane comparison adds no exclusion once the actual length gate holds. These statements concern scalar feasibility and do not assert that this example of scalar values occurs on a reachable history.

## What the first moments pay for

Let $S$ be the history before draw 406, $H(S)$ its finite mark group, and $k$ the absolute winning height. For $w g<q$, the uniform-mark first moment gives
$$
 \Pr(k>0,\ s\le wg\mid S)
 \le M(w,g)=\tfrac12 J_b w^b\Theta(wg\sqrt{2\pi/b})^d,
 \quad J_b=\frac{e^{b/2}(2\pi/b)^{b/2}}{V_b},\quad
 \Theta(z)=1+\frac{2e^{-\pi z^2}}{1-e^{-3\pi z^2}}.               \tag{4}
$$
For completeness, count all positive heights up to $wg$. Each permutes the mark since the group has exponent dividing $q$ and the height lies strictly below $q$. The Gaussian sum on a uniform old coset averages to the sum on $K=P_E\mathbb Z^{910}$ divided by $|H(S)|$, where $K/M=H(S)$ and $E$ is the retained space. Poisson summation at scale $z$ makes this at most $z^d\Theta(z)^d/D_-$. Indeed $K^*=E\cap\mathbb Z^{910}$ injects into some $d$ integer coordinates by a length-nonincreasing restriction, and the one-dimensional dual Gaussian sum is bounded by $\Theta(z)$ by a geometric series. Sum the positive height weights by the integral $z/2$, majorize the ball indicator by the Gaussian times $e^{\pi(wg/z)^2}$, and set $z=wg\sqrt{2\pi/b}$. [Part 142 and audit](wall1_dual_cusp.md) · [Part 151](wall1_penultimate_tail.md) · [Gaussian Poisson identity, equation (1)](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/transference.pdf)

**Void and two disjoint charges.** For the strict band put $A=\{\lambda_1(M)>cg\}$, $V=\{s>cg\}$. Then $V\subseteq A$, and on $A\setminus V$ a vertical winner has length at most $cg$. Equation (4) gives $M(c,g)<8.938011\cdot10^{-10}$, uniformly, using the step-405 GH floor. On $A$ the total variation distance of the mark law from its restriction conditioned on $V$ equals $1-\Pr(V\mid S)$, hence is at most this same number. For a closed lower band use weak inequalities for $A,V$. For either convention and any event $C$ of the same draw, $0\le\Pr(A\cap C\mid S)-\Pr(V\cap C\mid S)\le \mathbf 1_A\,8.938011\cdot10^{-10}$ by containment. This comparison precedes conditioning on a vertical win. The void supplies no small multiplier on $A$. [Part 153 and audit](wall1_neargh_vertical.md)

1. Charge $g\ge203.888$ at most $1/816000$. In detail, let $R_0=q^{-1}[(q^{510}/(408000V_{910}))^{1/910}-\sqrt{910}/2]\in(0.19999458051,0.19999458052)$. A nonzero raw dual point of norm below $R_0<1$ has a nonzero residue in its 400 output coordinates after scaling by $q$. Each candidate costs $q^{-510}$ by the independent columns. Enclosing the integer points in unit cubes gives expected count at most $1/408000$, and both signs occur. Off this exit the selected dual, a sublattice of the raw dual, has minimum at least $R_0$. The rank-505 Hermite cap gives $g\le G_b(\exp(1016.893214923/505)/R_0)^{505/506}<203.887618$. [Part 153 large-GH exit](wall1_neargh_vertical.md)
2. On $g<203.888$, charge the lower band $0.954\le\rho\le0.97$ less than $4.038879\cdot10^{-6}$. This follows directly from (4) at $w=0.97$, even discarding the lower endpoint and both quotient tests in that upper estimate. At $w=1$, the factor $J_b/2$ alone exceeds 19.94. This particular count loses all probability control before the middle of the band. The Part 147/151 small-$t$ moment also misses the scalar range here. Every vertical band win has $t\ge\alpha c g>26.59131$, while its audited small-$t$ majorant has already reached one at radius $1.20928$. [Part 147](wall1_uncovered_lines.md) · [Part 151 and audit](wall1_penultimate_tail.md)

Write $P_{\rm mid}$ for the *unconditional* mass on $g<203.888$, $0.97<\rho\le1.097193$, with a vertical win and both quotient tests. Equivalently, average the proportion of marks passing all these tests over histories with an indicator for $g<203.888$. The old minimum automatically clears $cg$ there. The rigorous consequence is
$$
 \Pr(B_{\rm v})\le 1/816000+4.038879\cdot10^{-6}+P_{\rm mid}.
$$
Thus $P_{\rm mid}+\Pr(H_{\rm old})\le0.00899473323$ suffices for the shared $0.0089999976$ allowance, where $H_{\rm old}$ is Part 151's residual (a). The void comparison incurs no additional charge in this inequality. Part 154's rounded-lift counts are on the next draw and do not evaluate $P_{\rm mid}$. [Part 151 decomposition](wall1_penultimate_tail.md) · [Part 154 and audit](wall1_winner_exchange.md)

## Exact checks and the remaining gap

Two exhaustive one-draw graph enumerations used integer congruences and rational orthogonal projections. The “rounding survives” column counts gated draws with $R(t)>\alpha t$, before measuring the actual shortest projected length $p$.

| $(m,j,T,q)$ | Designs | Vertical band | Also length gate | Rounding survives | Actual plane hits |
|---|---:|---:|---:|---:|---:|
| $(2,2,1,5)$ | 15625 | 3420 | 1980 | 212 | 4 |
| $(1,2,1,17)$ | 4913 | 1150 | 430 | 86 | 2 |

To reproduce, enumerate all $m\times(j+1)$ matrices over the field. In each graph list all nonzero raw vectors of squared norm at most three. Minimize squared length and then signed ambient coordinates, first in this list and then in its nonzero rational projections. To test the plane, project the same list off both directions. For exhaustiveness put $S_*=(1.097193g)^2$, $h_*=(q^m/(0.954g V_d))^{1/d}$ and $r_*^2=1+c^2h_*^2$. In both rows the maximum of $S_*, r_*^2+S_*/4, c^2h_*^2+r_*^2/4+S_*/4$ is strictly below four. Any candidate capable of passing the relevant gates, including a shorter competing minimum, has a raw lift within the list by rounding newest first. All six hits had $(s^2,t^2,p^2)=(2,3/2,4/3)$. Nonrational threshold comparisons used 65-decimal-digit outward intervals and separated strictly. The real-instance quantities above used 70-decimal-digit outward arithmetic with $V_0=1,V_1=2,V_n=2\pi V_{n-2}/n$. [Toy selected counts](wall1_selected_scaling.md)

**Open estimate.** The toy $4/1980$ decomposes into 212 draws surviving the scalar plane test and four actual hits. At width 506 the first of these filters retains every gated draw. A quantitative estimate for how frequently the selected quotient actually contains a short vector is still needed.

For scale, let $I$ indicate all the $P_{\rm mid}$ gates except the plane hit. The half-ball volume at $R(t)$ divided by the actual quotient determinant $D_-/(st)$ is
$$
 B_{\rm vol}=\frac{V_{d-1}}{2V_d}\,c^{d-1}\frac{t^{1/d}}{h}.
$$
On the gate $B_{\rm vol}<7.0080\cdot10^{-12}$ by $t\le r(h)<q$ and the step-406 floor for $h$. **Conjectural sufficient condition.** The estimate $P_{\rm mid}\le10^8\mathbb E[I B_{\rm vol}]$ would give $\Pr(B_{\rm v})<0.000707$, leaving more than $0.0082929$ for (a). The factor $10^8$ specifies one sufficient finite-width target. Neither the rounding proof nor the exact small enumerations establish this comparison for a selected quotient. The rigorous probability bound above still contains $P_{\rm mid}$.

## Audit

**Verdict — SOUND.** At width 506 every draw passing the retained-length gate satisfies the necessary rounding inequality. The actual plane hit still requires $p<R(t)$. All stated numerical bounds and both toy rows check out. The only correction is editorial. In Proposition 1, read “the following scalar conditions are necessary for $B_{\rm v}$.”

**Rounding and strictness.** Rounding a lift along each successive shortest vector gives $t^2\ge3s^2/4$ and $p^2\ge3t^2/4$, including ties. Combining the latter with $p<R(t)$ makes the upper bound on $t$ in (1) strict. Substituting the former gives $\alpha^{2d+1}\rho^{d+2}g<c^dV_b/V_d$, as in (2). Iterating $D_i\ge D_{i-1}^{d/b}/(2G_b)$ yields (3), including its exponent of $2G_b$.

An independent 300-bit outward-rounded interval calculation used the factorial and half-integer factorial formulas for the ball volumes. The step-405 floor for $g$ lies in $(32.1855367820,32.1855367821)$ and the step-406 floor for $h$ in $(32.0261018832,32.0261018833)$. Thus $c^2h^2>d$ throughout, so $f$ decreases. At the all-history ceiling for $h$, the minimum ratio guaranteed by $f$ lies in $(1.13637758665,1.13637758666)$. At the upper bound for $h$ on $g<203.888$, $\rho\ge0.954$, it lies in $(1.14270643045,1.14270643046)$. These give the claimed margins of $13.637\%$ and $14.270\%$, respectively.

**Exact enumeration.** A separate enumeration applied the graph congruences to the signed integer vectors of squared norm at most three and compared projected lengths and signed ambient ties exactly. Reverse rounding bounds the required raw squared norm by less than $3.356$ in the first row and $3.503$ in the second. All nonrational threshold comparisons separated in interval arithmetic. Of the 15,625 first-row designs, 3,420 won vertically in the band, 1,980 also passed the length gate, 212 survived rounding, and four had a plane hit. The corresponding counts in the 4,913 second-row designs were 1,150, 430, 86, and two. All six hits gave $(s^2,t^2,p^2)=(2,3/2,4/3)$.

**First moment, exit, and budget.** At $w=0.97$, $wg<q$ even at the all-history GH ceiling. Since $\Theta$ decreases, the step-405 floor gives a uniform upper majorant in $(4.03887847527,4.03887847528)\cdot10^{-6}$, including $\rho=0.97$. The same check at $w=c$ gives a majorant below $8.938011\cdot10^{-10}$. For the exit, counting both signs divides the raw-dual first moment $1/408000$ by two. Off the raw-dual hit, $R_0\in(0.1999945805175,0.1999945805176)$ gives a GH ceiling in $(203.8876174449,203.8876174450)$. This covers equality in the charged event $g\ge203.888$.

Subtracting $1/816000$ and $0.000004038879$ from Part 151's shared $0.0089999976$ leaves $0.0089947332308039215\ldots$. Rounding down gives the stated sufficient allowance for $\Pr(H_{\rm old})+P_{\rm mid}$. The middle-band event already enforces $s>0.97g>cg$ on the same draw, so this calculation never replaces a mark law by its law conditioned on the void. It incurs no total-variation charge. The half-ball bound also checks, but the factor $10^8$ multiplying its gated expectation is conjectural. The unconditional middle-band mass and the inherited horizontal contribution remain open.
