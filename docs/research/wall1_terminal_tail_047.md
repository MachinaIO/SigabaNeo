# A physical radius of 26 at the terminal restart

Let $F=\{\lambda_1(H_{407})\le26\}$ in the unconditioned width-506 restart. In the retained lattice $M=H_{406}$, take its designated signed shortest vector $x$ and put
$$
 J=\{\lambda_1(P_{x^\perp}M)\le26\}.
$$
**On every history through draw 406, the probability that $F$ disagrees with $J$ is below $3.210\cdot10^{-14}$.** The remaining probability is the frequency of a short plane through the old minimum. The estimates below do not prove $\Pr(F)<4.3\cdot10^{-7}$. They identify the configuration that would have to account for almost all of any violation at that scale.

Here $q=3329$, $Q=q^{400}$, $b=506$, $d=505$, and $r=26$. The restart has 105 initial graph columns and 407 independent suffix columns. All lengths are physical. The ratio $26/54.95253\simeq0.4731$ uses the full-row **model** determinant. The pathwise terminal GH floor only gives $r/\mathrm{GH}(H_{407})<0.817933$. Part 139's cube obstruction concerns a ratio, and its audit distinguishes the physical minimum there. The independent CBD(3) plant enters only in the score implication below. [Restart and scale audit](wall1_restart_passes_test.md) · [Part 109](wall1_terminal_mixing.md) · [Part 139 and audit](wall1_lyapunov.md)

## Last draw: one exceptional ball covers every origin

Fix the history and its finite mark group $G$. For $U$ uniform on $G$, the window is $W=(M,0)+\mathbb Z(\tilde U,1)$. Let $v$ generate its designated winning line, $s=\|v\|$, and $P_v$ denote projection off that line. From any lift of a nonzero quotient point of length $p\le r$, subtract a nearest integer multiple of $v$ to obtain $w$. Pythagoras and global shortestness give
$$
 s^2\le\|w\|^2=p^2+\delta^2s^2,\qquad |\delta|\le\tfrac12,
 \qquad s,\|w\|\le A:=2r/\sqrt3=30.0222139978\ldots .
 \tag{1}
$$
The same argument in $M$ gives $\|x\|\le A$ on $J$. All inequalities permit equality. [Winner exchange, including rounding ties](wall1_winner_exchange.md)

For a vertical winner orient $v=(v_h,k)$ with $k>0$ and set $l=v_h-k\tilde U\in M$. Subtracting $(j/k)v$ from a lift of height $j$ gives a horizontal vector $a\in M+\mathbb Z l/k$ with the same projection. The exact isometry gives
$$
 \|A_va\|^2=\|a\|^2-\langle v_h,a\rangle^2/s^2 .
$$
Thus the entire test is an ellipsoid in that refinement. Its axial semiaxis is $rs/k$ along $v_h$ and its transverse radius is $r$ (an ordinary ball if $v_h=0$). Old points already within $r$ survive every vertical projection. Longer old points can enter by the displayed inner-product test, and new classes occur for $k>1$. All three possibilities cost the **same draw** in an existence bound: on $F$, (1) makes the positive-height winner itself a point of the ball of radius $A$. This handles shortened vectors even when their old representatives lie outside that ball. [Lean theorems verticalWinner_isometry and winnerCompression_norm_sq](../../SigabaNeo/Lib/Lattices/Research/Wall1/VerticalWinnerIsometry.lean) · [Part 150, cylinder count](wall1_shortened_lines.md)

For a horizontal winner, the signed old rule gives $v=x$ up to sign. Fresh height survives projection unchanged. A short point with a lift of height zero gives $J$. A short point of nonzero height has a rounded lift of the same height and length at most $A$ by (1). Conversely, $J$ implies $F$ on **every** horizontal win, including a tie. On a vertical win with $J$, shortestness gives $s\le\|x\|\le A$ even if $F$ fails. With $N_+(A)$ counting incoming window points of strictly positive height and norm at most $A$, sign symmetry therefore gives
$$
 F\mathbin\triangle J\ \subseteq\ \{N_+(A)>0\}.
 \tag{2}
$$

The surviving old test is also an exact cylinder test. A reduced lift $u\in M\setminus\mathbb Rx$ has $|\langle u,x\rangle|\le\|x\|^2/2$ and $\|u\|^2-\langle u,x\rangle^2/\|x\|^2\le r^2$. Its existence is equivalent to $J$. Hence $J$ requires two independent old points of lengths at most $A$ and a plane of area at most $Ar<780.578$. This includes an old lift longer than 26 that enters the ball only after the last projection. Part 151's one-vector majorant already reaches one at physical radius $1.209272$. The old-vector lengths required here are outside its useful range. [Part 151 and audit](wall1_penultimate_tail.md)

### Conditional count at a fixed physical radius

Write $D_i=\det H_i$, $V_n=\operatorname{vol}B_n(1)$ and $g_i=(D_i/V_{506})^{1/506}$. From $L_0=\log Q$ iterate
$$
 L_i=\max\{L_{i-1}-\log q,\ (505/506)L_{i-1}-\tfrac12\log(56.2142)\}.
$$
Then $\log D_i\ge L_i$, since the winning length is at most both $q$ and $\sqrt{56.2142}\,D_{i-1}^{1/506}$. In particular $g_{406}>31.9457118986$ and $g_{405}>32.1855367820$. [Part 114](wall1_idea_drift.md) · [Part 151, sharpened recurrence](wall1_penultimate_tail.md)

For a fixed physical $0<R<q$, multiplication by each integer $1\le j\le R$ permutes $G$. The conditional positive-height mean is therefore the number of points of $K\times\mathbb Z_{>0}$ in the ball divided by $|G|$, where $K$ is the full marked preimage and $|G|\det K=D_i$. The integral dual $K^*$ injects by coordinate restriction into $\mathbb Z^d$ with no increase in norm. Set $z=R\sqrt{2\pi/b}$ and $\Theta(z)=1+2e^{-\pi z^2}/(1-e^{-3\pi z^2})$. Gaussian majorization and positive-height summation give $e^{b/2}z^b\Theta(z)^d/(2D_i)$. At $(i,R)=(406,A)$ this is below $4.4980\cdot10^{-13}$ by itself. [Marked Gaussian count](wall1_uncovered_lines.md)

For the sharper values use the proof of Part 161, Theorem 2, with $z$ at the actual physical radius. Its equation (3) defines $C(z)$ with $z$ in place of $z_m$, $T=8$, $\delta=1/2$ and 4096 bins. The proof gives
$$
 \mathbb E[N_+(R)\mid\text{history through }i]\le C(z)(R/g_i)^{506}.
 \tag{3}
$$
The $e^{b/2}z^b/D_i$ prefactor is the only determinant dependence. The original ratio interval and large-$g$ restriction ensured a lower bound on $z$ and invertibility of eligible heights. Here $z$ is specified and $R<q$ on every history. We re-evaluated the sum at each radius. [Part 161, equations (1)–(3) and audit](wall1_band_plane_hits.md)

| Incoming state | Fixed radius $R$ | Upper bound for $C(z)$ | Upper bound from (3) |
|---|---:|---:|---:|
| After 406 | $52/\sqrt3$ | 1.422743743939 | $3.209079\cdot10^{-14}$ |
| After 405 | $26\sqrt{3/2}$ | 1.422743743939 | $0.006373625$ |

Equations (2) and (3) prove the conditional discrepancy. In particular, if $p=\Pr(J)$ and $\epsilon=3.209079\cdot10^{-14}$, then $(1-\epsilon)p\le\Pr(F)\le p+(1-p)\epsilon$. The mass of $F$ outside a **horizontal win with an old witness** is also at most $\epsilon$, by (1) and the height-preserving argument. These estimates count the event once, regardless of how many points witness it.

## What survives one step earlier

On $J$, consider the window at draw 406. Its winner, a lift of $x$, and a lift of a shortest point of $P_{x^\perp}M$ form a rank-three flag **in this one window**. Successive shortest choices are primitive in each quotient. Taking inverse images gives a saturated rank-three lattice. In it the three projected choices are still shortest, and size reduction of the lifts leaves the Gram–Schmidt lengths unchanged. The second Korkin–Zolotarev inequality for this basis gives $s_{406}^2\le(3/2)\lambda_1(P_{x^\perp}M)^2$. Hence the second row of the table charges all of $J$ with a vertical winner at 406. Its physical cutoff $31.84337$ (rounded) is below the audited $31.86368$ cutoff, but its upper charge still exceeds the entire target. This application uses the two old directions together. It only requires a KZ basis in their rank-three inverse image. [Pendavingh and van Zwam, equations (1.3) and (7.10)](https://research.tue.nl/files/2066021/Metis197411.pdf)

If draw 406 selects horizontally, force its signed old winner before reading that mark. In the resulting append window, a designated $x$ using column 406 must have length at most $A$ on $J$. The Gaussian count above now has dimension 505 and determinant at least $e^{L_{406}}$ on feasible horizontal histories. Its joint charge is below $1.344\cdot10^{-13}$. If $x$ is also horizontal relative to column 406, it can be forced before that same draw. A witness using that column after the second projection then has norm at most 26 in dimension 504 and determinant at least $e^{L_{406}}/A$. Its joint charge is below $3.946\cdot10^{-44}$. In both calculations discard forced states failing the displayed deterministic gates, then average the uniform projected mark without conditioning on winning. The remaining horizontal case has **three directions lifted from the lattice before draw 406**. Its probability and the actual mass of the rank-three flag on 406 vertical wins remain unknown. [Forced horizontal comparisons](wall1_inherited_witness.md) · [Rank and determinant bookkeeping](wall1_penultimate_tail.md)

## How long are the old raw lifts?

The fixed cutoff permits a stronger ancestry statement. Let $\mathcal M\subset\mathbb Z^{911}$ be the unprojected graph on the first 511 columns. The 406 removed directions and the forced old $x$ span a rational subspace $T$ in this raw space. The old quotient in $J$ is $P_{T^\perp}\mathcal M$. For an old point $y$ each raw lift belongs to a coset of $\mathcal M\cap T$, and
$$
 \min_{\substack{u\in\mathcal M\\P_{T^\perp}u=y}}\|u\|^2
 =\|y\|^2+\operatorname{dist}(P_Tu_0,\mathcal M\cap T)^2
$$
for any one lift $u_0$. Thus a single shortest lift suffices to test accumulated shortening. [Part 160, Proposition 1 and audit](wall1_shrunken_lifts.md)

For $R=250<q$, each nonzero integer candidate sign pair of norm at most $R$ has raw graph membership probability at most $1/Q$: either it has a nonzero input residue or it cannot belong. Bound the number of candidate sign pairs by half a Gaussian sum, adding zero only to this numerical majorant. With $n=911$ and $z=R\sqrt{2\pi/n}$, one-dimensional Poisson summation gives
$$
 \Pr(\exists\,0\ne u\in\mathcal M:\|u\|\le250)
 \le e^{n/2}z^n\Theta(z)^n/(2Q)<4.249\cdot10^{-12}.
$$
Outside this event **every** raw lift of **every** old witness of length at most 26 loses more than $1-(26/250)^2=0.989184$ of its squared norm. This concerns the accumulated frozen span, including the forced horizontal winner. The last projection alone only needs a lift of length at most $30.02222$ in $M$.

Let $J_{\rm deep}$ require $J$, absence of the raw event above, and the Part 172 dual floors through 406. Averaging (2) and applying the audited simultaneous exit gives
$$
 |\Pr(F)-\Pr(J_{\rm deep})|
 <3.210\cdot10^{-14}+4.249\cdot10^{-12}+8.147\cdot10^{-14}
 <4.363\cdot10^{-12}.
$$
The dual floor controls the exit. On its complement the section estimate in Part 172 still involves a rank-503 dual section for a plane in $M$. It supplies no evaluated small probability for $J_{\rm deep}$. This localizes the potentially dominant configuration even on dual-good histories. Its actual frequency and the relative frequencies of its two origins at draw 406 have not been determined. [Part 172, Proposition 1 and exit audit](wall1_transference.md)

## Unconditional numerical bounds and the score

One unconditional bracket obtained here is
$$
 2^{-1909215}<\Pr(F)<1-2^{-1123284}.
$$
For the lower bound, if exactly 104 of the 512 raw columns are nonzero then every width-506 coordinate window contains a zero column. A unit axis of a zero column is always selected, so one survives among the 105 final columns. This event has probability $\binom{512}{104}(1-Q^{-1})^{104}Q^{-408}$, with base-two logarithm in $(-1909214.209,-1909214.206)$. [Coordinate deletion argument](wall1_horizontal_core.md)

For the upper bound, the Part 151 last-used-column flag estimate **does** control radius 26 early in this restart. At suffix time $T=167$ its majorant is below $2^{-6.6195}$. If the last 240 independent columns are zero and the minimum at 167 exceeds 26, each new unit axis is the unique shortest line and the lattice is preserved. Hence
$$
 1-\Pr(F)\ge (1-2^{-6.6195})Q^{-240}>2^{-1123284}.
$$
For reproducibility, use Part 151 equation (3) with $T=167,u=26$, its audited $B_l,P_l$ and the recurrence above. The largest $uB_l$ is between 2930.65 and 2930.66, below $q$. For $k=T-i+2$, $0\le j<k$, $n=506-j$, use the physical scale $z=uB_{k-j}\sqrt{2\pi/n}$ in the same Gaussian argument. The summand is
$$
 \tfrac12 e^{n/2}z^n\Theta(z)^{n-1}
 \exp(-L_{i-1}+j\log u+P_k-P_{k-j}).
$$
Adding $V_{505}(uB_{T+1}+\sqrt{505}/2)^{505}/(2Q)$ gives a base-two logarithm in $(-6.61957,-6.61956)$. This finite bound on an early prefix leaves the terminal probability essentially unrestricted. [Part 151, flag proof](wall1_penultimate_tail.md) · [Hermite caps and pseudocode](wall1_uncovered_lines.md)

**Open.** A bound on $\Pr(J)$ at the $4.3\cdot10^{-7}$ scale is still needed. R50 proves $C(E,H)\ge 0.74921186\,N_H(26)$, so $\mathbb EC\ge 2(0.74921186)(1-\epsilon)\Pr(J)$. The proposed Markov proof requires $\mathbb EC\le6.469\cdot10^{-7}$. Bounds (1)–(3) estimate the existence of one short point. The expectation of the signed point count and the contributions from other radii and shifted plant heights remain open. [R49 fixed-block test](wall1_test_acceptance.md) · [R50 height-zero audit](wall1_restart_passes_test.md)

Numerical checks used outward interval arithmetic at 45–55 decimal digits with $V_0=1$, $V_1=2$, $V_n=2\pi V_{n-2}/n$. An independent rational check used $W=\{(c,h,j):c\equiv ah+bj\pmod q\}$ for all pairs $(a,b)$ at $q=5,7,11$. At toy cutoff $r^2=3/2$, precisely five draws at each prime had $F\ne J$, all with a positive-height point in the predicted ball. At $q=5,r^2=5$, ten of the 25 pairs satisfied both events and fifteen satisfied only $F$. For each vertical winner, subtracting $(j/k)v$ and applying the compression norm identity reproduced the projected squared length for every enumerated lift. Enumeration through squared norm $2q^2$ suffices since the projected $q$-axes span, the quotient minimum is at most $q$, and rounding adds at most $q^2/4$. The probability estimates here are paper results.

## Audit

**Verdict — SOUND.** The last-draw comparison, the raw-lift statement and both sides of the unconditional bracket hold for the unconditioned width-506 restart with the signed ambient tie rule. No numerical correction is needed. The frequency of the old-plane event at the requested scale remains open.

**Last draw.** Nearest-integer reduction of any lift of a nonzero quotient witness preserves its projection and gives a nonzero window vector. Shortestness then yields both bounds in (1), including equality. On a vertical win, $F$ puts the winner in the exceptional ball, and $J$ puts it there by $s\le\|x\|\le A$. On a horizontal win, the old signed selector agrees with the window selector, so $J$ implies $F$. If only $F$ holds, every lift of the short witness has nonzero fresh height, which rounding along the horizontal winner preserves. Taking the positive sign proves (2) with a single count. This also covers witnesses that first meet the physical cutoff under projection. Since $J$ is known through draw 406, the two conditional error estimates give the stated bounds in terms of $p$.

**Numerical checks.** An independent 72-decimal-digit outward interval calculation used factorial formulas for the ball volumes, all 407 determinant updates, and separate 4096-bin sums at the two physical radii. The resulting first-moment bounds lie in $(3.20907863,3.20907865)\cdot10^{-14}$ after 406 and $(0.00637362446,0.00637362448)$ after 405. For the latter application the primitive successive selections give a basis of the saturated rank-three inverse image. Its first and third squared Gram–Schmidt lengths satisfy the second KZ inequality even in the presence of shortest-vector ties. The forced-horizontal Gaussian bounds in dimensions 505 and 504 are below $1.344\cdot10^{-13}$ and $3.946\cdot10^{-44}$, respectively. These are joint charges obtained before imposing the horizontal win. [Pendavingh and van Zwam, second KZ inequality](https://doi.org/10.1137/060658795)

**Raw lifts.** The first 511 columns give raw dimension $400+511=911$. Below $q$, a nonzero candidate with zero input residue cannot belong to the raw graph. Each other candidate belongs with probability $1/Q$, and its negative gives the same event. The sign-pair Gaussian bound lies in $(4.24859833,4.24859835)\cdot10^{-12}$. Off this one event every lift of every nonzero old witness has length strictly above 250. Orthogonality gives a strict fractional squared-length loss greater than $1-26^2/250^2=0.989184$ across the full removed span, including $x$. Adding the Part 172 simultaneous exit once gives the claimed $4.363\cdot10^{-12}$ comparison with $J_{\rm deep}$.

**Unconditional bracket.** Summing all 14,195 early-prefix terms and the initial-graph term gives a base-two logarithm in $(-6.619565,-6.619564)$, with maximum tested radius in $(2930.65135,2930.65136)$. Given a prefix minimum above 26, each independent zero append adds an orthogonal unit axis as the unique shortest line. Removing it preserves that prefix lattice. The certified complement contribution $(1-2^{-6.6195})Q^{-240}$ has base-two logarithm in $(-1123283.838,-1123283.837)$, which gives the strict upper bound. For the lower bound, 104 nonzero columns leave a zero axis among the final 105 after coordinate deletion. The stated binomial event has base-two logarithm in $(-1909214.208,-1909214.207)$.

**Exact checks and scope.** A separate integer enumeration compared signed shortest vectors and squared projected lengths by clearing denominators in the ball through squared norm $2q^2$. At $r^2=3/2$, each of $q=5,7,11$ had exactly five $F$-only pairs, zero $J$-only pairs, and a positive-height point in the exceptional ball for every discrepancy. At $q=5$, $r^2=5$, ten pairs met both tests and fifteen met only $F$. The vertical compression identity held for every enumerated lift on a vertical win. The uniform error bounds the difference between two existence probabilities. The old-plane probability, the signed multiplicities needed for the Part 182 score mean, and the shifted-height contributions still require separate estimates.
