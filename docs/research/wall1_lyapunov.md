# Potential functions and supermartingales for the selected final block

This note asks whether a scalar or low-dimensional functional Φ of the reduced state can be shown to have a usable conditional
drift under the exact first-pass kernel, and whether that drift then gives a terminal tail bound. The aim is to avoid the full
history law (Parts 106–112). The setting is plain LWE $(m,n,q)=(511,512,3329)$, CBD(3), and the exact no-lookahead first pass of
[Part 108](wall1_first_tour.md), with full width $b\in\{406,506\}$ and retained rank $r=d=b-1$. Six results.

1. **Exact potential duality and coarsening (Theorems 1–2, rigorous).** Every Azuma, Freedman, optional-stopping or Margulis-function
   argument is a superharmonic majorant of the terminal indicator. A potential that depends on a statistic π of the history is
   exactly as strong as an adversary who may pick, at every step, the worst reachable history with the same value of π.
2. **What the per-step statement must be (Theorem 3, rigorous).** Suppose an argument's step hypotheses are pathwise facts (Parts
   108–110, 114) together with statements about the kernel applied to non-atomic input laws (Part 105, Part 107, Siegel/Rogers
   means). Then the argument cannot bound δ below 1 at any ratio above $1/G_r$ (0.20356 at 406, 0.18257 at 506). The reason: the
   zero-draw kernel satisfies all of these hypotheses and freezes the cube. A valid step hypothesis must therefore be a counting
   statement about the uniform draw on the marked subgroup $H$ at the actual singular state. By Part 109 it cannot hold uniformly
   over reachable states. After the first pass there is no fresh randomness, and drift arguments with respect to the natural
   filtration collapse to pathwise bounds.
3. **Exact one-step geometry (Theorem 4, rigorous).** When the winner has vertical index $k\ge1$, the new retained lattice is
   isometric to $A_v(\Lambda+\mathbb Z\lambda/k)$, where $A_v$ contracts by $k/s$ along the horizontal part $v_h$ of the winner and
   $v_h$ is Voronoi-reduced. So the BKZ step is a random rank-one "diagonal flow", which is the structure that Eskin–Margulis–Mozes
   (EMM) Margulis functions exploit. Dually, $\Lambda'^*$ is a section of a lift of $\Lambda^*$, so physical dual minima never
   decrease below $\min(\lambda_1(\Lambda^*),1)$.
4. **Log-determinant supermartingale with a probabilistic cap (Theorem 5, rigorous identity; conditional corollary).** There is an
   exact Fourier formula, over the dual retained lattice, for the conditional second moment of the vertical count. It needs no union
   over sublattices. If the cap $s_t\le\kappa\,G_bD_{t-1}^{1/b}$ holds on every step, Part 114's deterministic floor 28.8095 improves
   to 34.099 at κ = 1.05 (b = 506). The ratio target then drops from 0.954 to **0.8052**. The per-step condition is a dual one: no
   anomalously short inherited dual vectors.
5. **The EMM route (Proposition 6, conditional; Conjecture E).** Under a direction-spread hypothesis (DS), the vertical-winner step
   contracts rank-one potentials of exponent $p=\theta r$ by a factor $\le 0.259M$ at θ = 1/2 and $s=30$. Horizontal-winner steps
   are deterministic and need rank-two incidence control. This is exactly the Part 120/126 obstruction, now located inside a
   Margulis-function scheme.
6. **Impossibility and barrier results (Propositions 7–9).**
   * The deterministic Rankin-vector recursion is the worst case and reproduces Part 110.
   * Rank-one Voronoi protection is vacuous, because $s\le\lambda_1(\Lambda)$.
   * A Bernstein/Freedman argument on a log-ratio potential needs almost-sure one-step increments below **0.01534** on its good
     set at the 0.954 target, or below 0.0686 at the 0.81 target.
   * Additive window-count potentials reduce to the terminal probability itself.

No new value of δ is proved. The note reduces the potential-function route to two explicit conditional statements, (C1) and (C2) in
§7.

## 0. Setting

This section follows [Part 108](wall1_first_tour.md) and [Part 109](wall1_terminal_mixing.md). Write $E$ for the real span of the
retained lattice $\Lambda$ (rank $r$, determinant $D$), $H\subset E/\Lambda$ for the marked finite subgroup, and $e\perp E$ for the
new unit axis. At a graph append the column has height $h=1$, and its displacement $U$ is uniform on $H$ given the whole past. The
window is $W=\Lambda+\mathbb Z(\tilde U+e)$ with determinant $D$. The reducer selects a primitive shortest vector $v$, of length
$s=\lambda_1(W)$, with fixed ties, and sets $\Lambda'=Q_vW$, $D'=D/s$, $H'=(Q_v)_*H$. The marked state is $x=(\Lambda,H)$ together
with the frame (needed for ties).

From a fixed start the reachable set $\mathcal R_t$ is **finite**, since every step averages over $|H|\le q^r$ draws, and its states
are rational. All expectations below are finite sums. Write $G_j=V_j^{-1/j}$ and

$$Y(\Lambda)=\frac{\lambda_1(\Lambda)}{G_rD^{1/r}},\qquad B_c=\{Y(\Lambda_T)<c\},\qquad \delta_c=\Pr[B_c].$$

The physical variant is $\{\lambda_1(\Lambda_T)<F\}$, with $F=27.4538$ at 506. The Lean reduction (`reductionError`, PROOF_GAP Lean
list) needs the design fraction δ of final blocks failing "minimum ≥ L and GS floor ≥ g". The minimum half is the subject here. The
GS-floor half is touched only through the dual lemma 4(d).

## 1. Potential duality

**Theorem 1.** Let $(X_t)_{t\le T}$ be a Markov chain with finite reachable sets $\mathcal R_t$ and kernels $K_t$, and let $B\subset\mathcal R_T$.

(a) Suppose $\Phi_t:\mathcal R_t\to[0,\infty]$ satisfies $\Phi_T\ge\mathbf 1_B$ and $\Phi_t\ge K_t\Phi_{t+1}$ on $\mathcal R_t$
(superharmonic majorant). Then $\Pr[X_T\in B]\le\mathbb E\,\Phi_0(X_0)$. The function $h_t(x)=\Pr[X_T\in B\mid X_t=x]$ is such a
majorant, and it is the least one pointwise. So the best potential bound equals δ.

(b) (Killing.) Let $G_t\subset\mathcal R_t$, and suppose the superharmonic inequality holds only on $G_t$, in the killed form
$\Phi_t\ge K_t(\Phi_{t+1}\mathbf 1_{G_{t+1}})$, with $\Phi_T\ge\mathbf 1_B$ on $G_T$. Then
$\Pr[B]\le\mathbb E[\Phi_0(X_0)\mathbf 1_{G_0}]+\sum_{t\le T}\Pr[X_t\notin G_t,\ X_j\in G_j\ (j<t)]$.

(c) Several standard arguments produce such majorants:
* Foster–Lyapunov/Margulis: if $K\Phi\le\kappa\Phi+\beta$ and $\Phi\ge\psi(Y)$ with ψ decreasing, take
  $\Psi_t=[\kappa^{T-t}\Phi+\beta(1-\kappa^{T-t})/(1-\kappa)]/\psi(c)$.
* Azuma–Hoeffding, Freedman and Bernstein: their exponential supermartingales, divided by their threshold value, are majorants on
  the chain augmented by the running sums.
* Optional stopping: a stopped supermartingale is a majorant of the stopped chain, as in (b).

*Proof.* (a) $\Phi_t(X_t)$ is a supermartingale, so $\Pr[B]\le\mathbb E\Phi_T(X_T)\le\mathbb E\Phi_0(X_0)$. The function $h$
satisfies the inequalities with equality. Backward induction gives $\Phi_t\ge h_t$: if $\Phi_{t+1}\ge h_{t+1}$, then
$\Phi_t\ge K_t\Phi_{t+1}\ge K_th_{t+1}=h_t$. (b) Partition by the first exit time. On the event of never exiting before $t$, the
killed process $\Phi_t(X_t)\mathbf 1\{X_j\in G_j\ \forall j\le t\}$ is a supermartingale. (c) For Ψ, $K\Psi_{t+1}\le[\kappa^{T-t}\Phi+\beta(\kappa-\kappa^{T-t})/(1-\kappa)+\beta]/\psi(c)=\Psi_t$,
and $\Psi_T=\Phi/\psi(c)\ge\mathbf 1_{B}$. The exponential cases are the textbook supermartingale inequalities, read on the augmented
chain. ∎

[wall1_potential](wall1_potential.md) records the time-averaged drift budget. Theorem 1 is the terminal counterpart: only
**majorants of $h_T=\mathbf 1_B$** matter, and averaged drifts give terminal bounds only through them.

## 2. Coarsening: low-dimensional potentials are adversarial

Let $\pi_t$ be any function of the history $\omega_{\le t}=(X_0,\dots,X_t)$, with values in a finite set. A *π-potential* is
$\Phi_t=F_t(\pi_t(\omega_{\le t}))$ satisfying Theorem 1(a) along every reachable history. Define the **π-adversary values**

$$V_T(p)=\max_{\pi_T(\omega)=p}\mathbf 1_B(\omega),\qquad V_t(p)=\max_{\pi_t(\omega_{\le t})=p}\ \mathbb E\big[V_{t+1}(\pi_{t+1})\,\big|\,\omega_{\le t}\big],$$

with maxima over reachable histories.

**Theorem 2.** Every π-potential satisfies $F_t\ge V_t$ on the range of $\pi_t$, and $V$ is itself a π-potential. Hence the best
π-potential bound on δ is $V_0(\pi_0(x_0))$. Moreover, along the true chain,
$V_0\ge\Pr[\pi_t\in\{p:V_t(p)=1\}]$ for every $t$.

*Proof.* At $T$, $F_T(p)\ge\mathbf 1_B(\omega)$ for every ω in the fiber, so $F_T\ge V_T$. If $F_{t+1}\ge V_{t+1}$, then for each
history in the fiber of $p$, $F_t(p)\ge\mathbb E[F_{t+1}\mid\omega_{\le t}]\ge\mathbb E[V_{t+1}\mid\omega_{\le t}]$. Taking the
maximum gives $F_t(p)\ge V_t(p)$. $V$ satisfies the superharmonic inequality by the definition of the maximum. The last claim
follows because $V_t(\pi_t)$ is a supermartingale along the true chain. ∎

**Corollary 2.1 (time-only potentials).** Take $\pi_t=t$. Any argument of the form "each step fails with conditional probability at
most $\varepsilon_t$, uniformly over reachable states" is of this type. Part 109 gives a reachable state at $T-1$ (the cube after
511 zero draws) every one of whose successors lies in $B_c$ for $c\ge0.21$ (both widths). So $V_{T-1}=1$ and $V_0=1$.

**Corollary 2.2 (criterion for a statistic).** Suppose that at some time $t$ a value $p$ of $\pi_t$ is shared with a reachable
history all of whose continuations fail. Then any π-potential bound is at least $\Pr_{\rm true}[\pi_t=p]$.

*Reading.* Parts 109, 110, 125 and 126 lose because their bookkeeping is a coarse statistic. By Theorem 2 they are then worst case
over the fibers of that statistic. A successful potential must keep enough of the state that no fiber of positive true mass contains
a doomed history. For a Markov potential ($\pi_t=X_t$) the fibers are single states and the theorem is empty. So Markov-state
potentials are the only class not ruled out a priori.

## 3. What the per-step conditional statement must be

**Theorem 3.**

(a) *(Haar-null modification.)* Let $\mathcal R=\bigcup_t\mathcal R_t$, a finite set of rational marked states. Define $K^0$ by
$K^0(x)=\delta_{T(x,0)}$ (the zero draw, $0\in H$) for $x\in\mathcal R$, and $K^0=K$ off $\mathcal R$. Then $K^0$ satisfies:
* every pathwise statement about $K$, i.e. every statement of the form "$P(x,y)$ for all $x\in\mathcal R$ and $y\in\operatorname{supp}K(x)$",
  because $T(x,0)$ is an actual successor;
* every statement about $\int K(x,\cdot)\,\nu(dx)$ for laws ν with $\nu(\mathcal R)=0$. This includes Part 105's density bound and
  joint law, Part 107(i)–(ii), and every Siegel or Rogers mean over Haar input.

(b) Start from the cubic retained lattice $q\mathbb Z^r$ with full marks (the state at the first graph append in Part 108). Under
$K^0$ the retained lattice is constant. So $Y(\Lambda_T)=1/G_r$, which is $0.2035525$ at 406 and $0.1825671$ at 506, with
probability one. Any proof whose step hypotheses are of the two kinds in (a) cannot give $\delta_c<1$ for $c>1/G_r$.

(c) *(Selectors.)* The same holds for every kernel $K^\sigma(x)=\delta_{T(x,\sigma(x))}$ with $\sigma(x)\in H$. Hence a valid step
hypothesis must constrain the **uniform** measure on $H$ at the actual state, for example
$|H|^{-1}\#\{u\in H:\ \Phi_{t+1}(T(x,u))>\cdots\}\le\cdots$. By Part 109 (Corollary 2.1) no such hypothesis with failure below 1
holds uniformly on $\mathcal R_{T-1}$ at $c\ge0.21$. It must be restricted to a good set $G_t$, and the exits must be charged as
in Theorem 1(b).

(d) *(Later tours.)* Let $\mathcal F_t\supseteq\sigma(A)$, as for any tour after all columns have been revealed. Then each conditional
kernel is a point mass. A supermartingale is then pathwise nonincreasing, and $\Phi_0\ge\Phi_T\ge\mathbf 1_B$ forces
$\mathbb E\Phi_0\ge\delta$ with no reduction. A nontrivial drift needs a filtration $\mathcal G_t\not\supseteq\sigma(A)$, and its
kernel is a posterior law of $A$.

*Proof.* (a) Reachable lattices are orthogonal projections of sublattices of $\mathbb Z^{1023}$ along rational directions, so they
have rational Gram matrices. There are finitely many reachable states, so ν-null sets contain $\mathcal R$ for every non-atomic ν.
(b) If $\lambda_1(\Lambda)>1$ and $U=0$, then $W=\Lambda\oplus\mathbb Ze$, the unique shortest pair is $\pm e$, $Q_e$ is the
identity on $E$, and $H'=H$. For the cube, $\lambda_1=q>1$. The final ratio $q/(G_rq)$ is computed in the table of Part 108. (c) The
argument of (a) applies verbatim. Part 109 exhibits the doomed state. (d) This is immediate. ∎

**Answer to "randomization over A/s alone?".**
* *First pass.* Conditional on the history, the step law is exactly uniform on $H$ (fresh columns of $A$). So randomization over $A$
  is the *only* source available, and it is also sufficient to define the step statement. The statement must be non-uniform.
* *s.* δ is a function of $A$ (the design), so randomization over $s$ plays no role for δ.
* *Later tours.* There is nothing fresh, and a drift requires a posterior law.

## 4. Exact one-step geometry

Let $v=\lambda+k(\tilde U+e)$ with $\lambda\in\Lambda$ and $k\ge0$ (sign fixed). Put $v_h=\lambda+k\tilde U\in E$, so
$s^2=|v_h|^2+k^2$.

**Theorem 4.**

(a) *(Vertical winner, $k\ge1$.)*
* $v_h$ is the shortest element of $k\tilde U+\Lambda$. Hence $|\langle\mu,v_h\rangle|\le|\mu|^2/2$ for every $\mu\in\Lambda$.
* For every sublattice $\Delta\subseteq\Lambda$, the projection $P_\Delta v_h$ lies in the Voronoi cell of Δ, so
  $|P_\Delta v_h|\le\mu(\Delta)$ (covering radius).
* The order of $\lambda/k$ modulo Λ is exactly $k$, and $\Lambda'\cong A_v(\Lambda+\mathbb Z\lambda/k)$ (isometric), where
  $$A_v=I_E-(1-k/s)\,\hat v_h\hat v_h^{\top},\qquad |A_vx|^2=|x|^2-\langle x,v_h\rangle^2/s^2 .$$
* For any rank-$i$ sublattice $M$ of $E$, $\operatorname{covol}(A_vM)^2=\operatorname{covol}(M)^2\big(1-(1-k^2/s^2)|P_M\hat v_h|^2\big)$.

(b) *(Horizontal winner, $k=0$.)* Here $v=x_0\in\Lambda$ with $s=\lambda_1(\Lambda)$, and
$\Lambda'=\pi\Lambda+\mathbb Z(\pi\tilde U+e)$, where π projects $E$ onto $x_0^\perp$.

(c) *(Rankin recursion.)* Let $a_i$ be the minimal covolume of a rank-$i$ sublattice, with $a_0=1$. Then
$$a_{i+1}(W)=\min\Big(a_{i+1}(\Lambda),\ \min_{\Delta}\operatorname{covol}(\Delta)\,\rho_\Delta(U)\Big),\qquad a_i(\Lambda')\ge a_{i+1}(W)/s,$$
where Δ runs over primitive rank-$i$ sublattices of Λ, and $\rho_\Delta(U)\ge1$ is the vertical minimum of the projected window
$\pi_{\Delta^\perp}W$. In particular $a_i(\Lambda')\ge\min(a_i(\Lambda),a_{i+1}(\Lambda))/s$.

(d) *(Dual.)* $W^*=\{(\xi,\,j-\langle\xi,\tilde U\rangle):\xi\in\Lambda^*,j\in\mathbb Z\}$ and $\Lambda'^*=W^*\cap v^\perp$. Hence
$\lambda_1(\Lambda'^*)\ge\min(\lambda_1(\Lambda^*),1)$, and $\lambda_1(\Lambda'^*)\ge\lambda_1(\Lambda^*)$ when $k\ge1$. For $k=1$,
$\Lambda'^*\cong A_v^{-1}\Lambda^*$ with $|A_v^{-1}\xi|^2=|\xi|^2+(s^2-1)\langle\xi,\hat v_h\rangle^2$. Normalized dual minima,
$\lambda_1(\Lambda^*)D^{1/r}$, shrink by at most the factor $s^{-1/r}$ per step (0.99329 at $s=30$, $r=505$), unless they are capped
by the new vertical dual vector.

*Proof.*

(a) *Voronoi facts.* For $\mu\in\Lambda$, $v\pm\mu\in W$ and $|v\pm\mu|^2=|v_h\pm\mu|^2+k^2\ge s^2$, so $|v_h\pm\mu|\ge|v_h|$. For
δ ∈ Δ, $|P_\Delta v_h-\delta|^2-|P_\Delta v_h|^2=|\delta|^2-2\langle\delta,v_h\rangle\ge0$.

*The map $A_v$.* Since $v\notin E$, $Q_v|_E:E\to v^\perp$ is a linear bijection. Moreover $|Q_vx|^2=|x|^2-\langle x,v_h\rangle^2/s^2$,
because $\langle x,v\rangle=\langle x,v_h\rangle$. The same holds for $A_v$, since $(1-k^2/s^2)/|v_h|^2=1/s^2$. Two injective maps with
equal Gram forms differ by an isometry. If $v_h=0$, then $v=e$, $s=1$ and $A_v=I$.

*The lattice $\Lambda'$.* From $k(\tilde U+e)=v-\lambda$ we get $Q_v(\tilde U+e)=Q_v(-\lambda/k)$, so
$Q_vW=Q_v(\Lambda+\mathbb Z\lambda/k)$. If $g=\gcd(k,c(\lambda))>1$, with $c(\lambda)$ the content, then $v/g\in W$, contradicting
primitivity. So the index is $k$, and $\det\Lambda'=(k/s)(D/k)=D/s$.

*Covolume formula.* $\det(B^{\top}(I-\epsilon\hat u\hat u^{\top})B)=\det(B^{\top}B)(1-\epsilon|P_M\hat u|^2)$, by the
matrix-determinant lemma, with $\epsilon=1-k^2/s^2$.

(b) The vector $e$ is orthogonal to $x_0$, so $Q_{x_0}$ fixes $e$ and acts as π on $E$.

(c) Let $M\subseteq W$ be primitive of rank $i+1$. If $M\subseteq\Lambda$, then $\operatorname{covol}M\ge a_{i+1}(\Lambda)$.
Otherwise the vertical coordinate $M\to\mathbb Z$ is nonzero, and its kernel $\Delta=M\cap\Lambda$ is primitive of rank $i$. Write
$M=\Delta\oplus\mathbb Zw$ with $w=\mu+m(\tilde U+e)$ and $m\ge1$. Then
$\operatorname{covol}M=\operatorname{covol}\Delta\cdot(m^2+|\pi_{\Delta^\perp}(\mu+m\tilde U)|^2)^{1/2}$. A primitive rank-$i$
sublattice of $\Lambda'$ has full preimage of rank $i+1$ containing $v$, with covolume multiplied by $s$.

(d) The description of $W^*$ is direct: $(\xi,t)$ pairs integrally with Λ and with $\tilde U+e$ exactly when $\xi\in\Lambda^*$ and
$t+\langle\xi,\tilde U\rangle\in\mathbb Z$. For primitive $v$, the dual of the projection is the orthogonal section. A vector
$(\xi,t)$ has length at least $|\xi|$, and $(0,j)$ has length $|j|$. For $k\ge1$, the dual of $A_v(\Lambda+\mathbb Z\lambda/k)$ is
$A_v^{-1}(\Lambda+\mathbb Z\lambda/k)^*\subseteq A_v^{-1}\Lambda^*$, and $A_v^{-1}$ only lengthens. Finally
$\det\Lambda'^*=s/D$. ∎

These identities were checked numerically in ranks 2 and 3 (exact SVP by enumeration, 276 windows, including $k=2$). The checks
covered the isometry $Q_v|_E\sim A_v$, the identity $Q_v(\tilde U+e)=Q_v(-\lambda/k)$, and the Voronoi inequality. No violations
occurred once the enumeration box contained the true minimizer.

**Proposition 7 (the deterministic skeleton is the worst case).**
* Iterating 4(c) gives $a_1(\Lambda_T)\ge D_T\min_{j\ge0}a_{1+j}(\Lambda_0)/D_0$, which is the Part 109/110 type floor. All the
  loss sits in replacing $\rho_\Delta(U)$ by 1.
* Rank-one Voronoi protection is vacuous. By 4(a), a vector $x$ with $|x|<2s\sqrt{1-s^{-2/r}}$ cannot shrink in normalized length
  under a $k=1$ step; this threshold is $0.2313s$ at $s=30$. But $s=\lambda_1(W)\le\lambda_1(\Lambda)$, so no such $x$ exists.
* Protection in rank $i$ is non-vacuous only when $\mu(\Delta)/s<\sqrt{1-s^{-2i/r}}$. Since $\mu(\Delta)\ge\lambda_1(\Lambda)/2\ge s/2$,
  this needs $i\ge r\log(4/3)/(2\log s)\approx21$ at $s=30$.

So a rank-one cusp excursion in the retained lattice happens only through the window minimum: $\lambda_1(\Lambda')\ge\alpha s$ with
$\alpha=\sqrt3/2$. The relevant scalars are $s_t/\mathrm{GH}(W_t)$ and the horizontal-winner cascade.

## 5. A log-determinant supermartingale with a probabilistic cap

Part 114's exact recurrence $D_t=D_{t-1}/s_t$ turns any cap $s_t\le\kappa G_bD_{t-1}^{1/b}$ into the terminal GH floor

$$h_T\ \ge\ G_d\,q^{a^T}(\kappa G_b)^{-(1-a^T)/a},\qquad a=d/b,\ T=512 .$$

Part 114 used the deterministic Hermite cap $\kappa=\sqrt{\gamma_b}/G_b$. The table below uses smaller caps that hold only with high
probability. The $\kappa=1$ row is Part 114's zero-error value.

| κ | $h_T$ floor, b = 506 | $F/h_T$, b = 506 | $h_T$ floor, b = 406 | $F/h_T$, b = 406 |
|---:|---:|---:|---:|---:|
| 1.00 | 35.1775 | 0.78044 | 15.5046 | 1.5854 |
| 1.02 | 34.7358 | 0.79036 | 15.2855 | 1.6081 |
| 1.05 | 34.0992 | 0.80511 | 14.9703 | 1.6420 |
| 1.10 | 33.1019 | 0.82937 | 14.4779 | 1.6978 |

The cap is automatic whenever $\lambda_1(\Lambda_{t-1})\le\kappa G_bD_{t-1}^{1/b}$, because $s_t\le\lambda_1(\Lambda_{t-1})$; this
covers the cubic phase, where $s=q$. Otherwise $s_t\le(1+\rho^2)^{1/2}$ as soon as the displaced coset $\tilde U+\Lambda$ meets the
open ball $B_\rho$. Fix $\rho<\kappa G_bD^{1/b}$ with $1+\rho^2\le\kappa^2G_b^2D^{2/b}$.

**Theorem 5 (exact second moment).** Let $\varphi=\mathbf 1_{B_{\rho-\varepsilon}}*\psi_\varepsilon$, where $\psi_\varepsilon\ge0$
is symmetric, has unit mass, is supported in $\bar B_\varepsilon$, and has absolutely summable $\hat\psi_\varepsilon$ on $\Lambda^*$
(for example a normalized $\mathbf 1_{B_{\varepsilon/2}}*\mathbf 1_{B_{\varepsilon/2}}$). Put $P(u)=\sum_{\mu\in\Lambda}\varphi(u+\mu)$
and $H^\perp=\{\xi\in\Lambda^*:\langle\xi,h\rangle\in\mathbb Z\ \forall h\in H\}$. For $U$ uniform on $H$,

$$\mathbb E P(U)=\frac1D\sum_{\xi\in H^\perp}\hat\varphi(\xi),\qquad
\operatorname{Var}P(U)=\frac1{D^2}\sum_{c\in\Lambda^*/H^\perp,\ c\ne0}\Big|\sum_{\xi\in c}\hat\varphi(\xi)\Big|^2 .$$

Consequently, if $\mathbb EP>0$,
$$\Pr_U\!\big[s>\sqrt{1+\rho^2}\big]\le\operatorname{Var}P/(\mathbb EP)^2=:\varepsilon(x).$$

*Proof.* φ is continuous with compact support, and $|\hat\varphi|\le|\hat{\mathbf 1}_B||\hat\psi|$ is summable over $\Lambda^*$. So
Poisson summation gives $P(u)=D^{-1}\sum_{\xi\in\Lambda^*}\hat\varphi(\xi)e(\langle\xi,u\rangle)$, absolutely. Character
orthogonality on the finite group $H$ gives $|H|^{-1}\sum_{h}e(\langle\xi-\xi',h\rangle)=\mathbf 1\{\xi-\xi'\in H^\perp\}$. Grouping
by cosets of $H^\perp$, the zero coset reproduces $(\mathbb EP)^2$. If $P(U)>0$, some point of $\tilde U+\Lambda$ lies within ρ of
the origin, which gives a layer-one window vector of length $<\sqrt{1+\rho^2}$. Chebyshev finishes the proof. ∎

The diagonal of the coset sum reproduces the Poisson term $\approx D/\operatorname{vol}B_\rho=(\mathrm{GH}(\Lambda)/\rho)^r$, which is
about $e^{-23}$ at κ = 1.05. The other terms are governed by short vectors of $\Lambda^*$, through the decay of
$\hat{\mathbf 1}_{B_\rho}(\xi)/\operatorname{vol}B_\rho=\Gamma(\tfrac r2+1)(2/z)^{r/2}J_{r/2}(z)$ with $z=2\pi\rho|\xi|$. At the end
of the pass ($\rho\approx35$), dual vectors of physical length $\ge1$ contribute less than $e^{-37}$ each. The danger is only
inherited short dual vectors, and by Theorem 4(d) the dual is physically monotone: inheritance is the *only* way to keep them.

**Corollary 5.1 (conditional GH floor).** For every κ,

$$\Pr\big[h_T<G_dq^{a^T}(\kappa G_b)^{-(1-a^T)/a}\big]\le\sum_{t=1}^{T}\mathbb E\big[\min(1,\varepsilon_t(X_{t-1}))\big],$$

with $\varepsilon_t:=0$ when $\lambda_1(\Lambda_{t-1})$ is already below the cap. This is Theorem 1(b) with $G_t$ = "cap holds so
far". The right-hand side is a sum of **one-step** quantities, each a function of the current dual lattice and marks only. No union
over sublattices and no history law enters. Evaluating it still needs the law of $(\Lambda_{t-1}^*,H_{t-1})$. That is condition
(C1) in §7, which is a dual cusp-escape statement.

## 6. The Margulis-function (EMM) route

For rank-$r$ Λ with determinant $D$, put $\nu_i(\Lambda)=a_i(\Lambda)/D^{i/r}$, and take a candidate
$\Phi=\sum_{i<r}w_i\nu_i^{-p_i}$. Then $B_c\subseteq\{\Phi\ge w_1(cG_r)^{-p_1}\}$. Theorem 1(c) gives:

**Conditional terminal bound.** If $K\Phi\le\kappa\Phi+\beta$ on a good set $G_t$, then
$$\delta_c\le\text{exit}+\big(\kappa^T\Phi(x_0)+\beta/(1-\kappa)\big)(cG_r)^{p_1}/w_1 .$$
Calibrate $\beta$ on the bulk scale $G_r^{-p_1}$ and take $p_1=\theta r$. The terminal factor is then $c^{\theta r}$, which is
$6.85\cdot10^{-6}$ at $c=0.954$ and θ = 1/2. So $\beta/(1-\kappa)$ may be as large as about $10^3G_r^{-p_1}$.

**Proposition 6 (vertical steps, given direction spread).** Let $k=1$. By Theorem 4(a), exactly
$$\nu_i(\Lambda')=s^{i/r}\min_\Delta\nu_i(\Delta)\big(1-(1-s^{-2})|P_\Delta\hat v_h|^2\big)^{1/2}.$$

Suppose (DS$_M$): for each near-minimal Δ of rank $i$, the conditional law of $\hat v_h$ given the state and $\{k=1\}$ satisfies
$\mathbb E[g_\Delta(\hat v_h)]\le M\,\mathbb E_{\rm unif}[g_\Delta]$ for $g_\Delta=(1-|P_\Delta\hat v|^2)^{-p/2}$. Then the factor by
which a single Δ's contribution to $\nu_i^{-p}$ changes is at most

$$M\,s_{\min}^{-ip/r}\,\frac{B(i/2,(r-i-p)/2)}{B(i/2,(r-i)/2)}\qquad(p<r-i),$$

because $|P_\Delta\hat v|^2\sim\mathrm{Beta}(i/2,(r-i)/2)$ under the uniform law. Here $s_{\min}$ is a lower bound for $s$ on
$\{k=1\}$, which the lower tail of the vertical count supplies (Part 109's layer bound). Divided by $M$, for $i=1$ and $p=\theta r$
at $r=505$:

| $s$ | θ = 0.25 | θ = 0.5 | θ = 0.75 |
|---:|---:|---:|---:|
| 20 | 0.5463 | 0.3167 | 0.2124 |
| 30 | 0.4936 | 0.2586 | 0.1567 |
| 35 | 0.4750 | 0.2394 | 0.1396 |

The sharp use of DS$_M$ is the top-$1/M$ quantile average of $g$, which is smaller still. So constant-factor direction hypotheses of
Part 105 type ($M\le2$) would suffice for the vertical branch at every exponent.

*Proof.* Combine the exact formula with $1-(1-s^{-2})\beta\ge1-\beta$, and use
$\mathbb E(1-\beta)^{-p/2}=B(i/2,(r-i-p)/2)/B(i/2,(r-i)/2)$. ∎

Vertical steps with $k\ge2$ refine by index $k$ (Theorem 4(a)). The new vectors are projections of layer-one vectors, of length
$\ge\alpha s$. Their effect on $\nu_i$ for $i\ge2$ costs at most a factor $k$, and needs a bound on $\Pr[k\ge2\mid x]$. This is not
small: the layer-volume heuristic $(1-k^2/s^2)^{r/2}$ gives $\Pr[k\ge2]\approx0.35$ at $s\approx30$ (heuristic).

**Horizontal steps carry no randomness.** By 4(b) and 4(c),
$a_i(\pi\Lambda)=\min_{M\ni x_0,\ \mathrm{rk}M=i+1}\operatorname{covol}M/s$. So in a horizontal step $\nu_1(\Lambda')$ is controlled
only by planes through the old shortest vector. Bounded growth of the EMM combination needs
$\min_{M\ni x_0}\nu_2(M)\gtrsim\nu_1(\Lambda)^2$, uniformly on the good set. By submodularity
($\operatorname{covol}(\Delta_1\cap\Delta_2)\operatorname{covol}(\Delta_1+\Delta_2)\le\operatorname{covol}\Delta_1\operatorname{covol}\Delta_2$),
EMM's weights $\varepsilon^{i(r-i)}$ can absorb this only when horizontal winners are rare *on states with a bad rank-two/rank-one
ratio*. That is a correlation between the event "λ₁(Λ) is below the vertical minimum" and plane incidence, which is precisely the
history-averaged horizontal term of Part 120. Horizontal winners are not rare in the bulk: by a Haar heuristic (not a proof), λ₁(Λ) falls below
$\mathrm{GH}_W\approx0.997\,\mathrm{GH}(\Lambda)$ with probability ≈ 0.12. Part 112 also warns that SVP void conditioning
correlates positively.

**Conjecture E (EMM inequality on a good set).** There exist $p_i$ (with $p_1\approx r/2$), weights $w_i$, κ < 1 and
$\beta\le10^2G_r^{-p_1}$ such that $K\Phi\le\kappa\Phi+\beta$ on a set $G_t$ whose exit probability over the restart's 407 steps is
below 0.005. Proved here: the exact geometry (Theorem 4) and the vertical-branch factor under (DS) (Proposition 6). Open: (DS)
itself on reachable states, and the horizontal/rank-two correlation.

## 6'. Barriers for other natural Φ

**Proposition 8 (Bernstein barrier).** Let $\Phi=-\log Y$ (or any log-ratio potential), with target margin $\lambda=\log(1/c)$ from
a typical value near 0. Freedman's inequality with almost-sure increment bound $M$ and predictable variance $V$ gives at best
$\exp(-\lambda^2/(2(V+M\lambda/3)))\ge\exp(-3\lambda/(2M))$. So to reach failure $p$ the increments must satisfy
$M<3\lambda/(2\log(1/p))$ on the good set. At $p=0.01$ this is $M<0.01534$ for $c=0.954$, $0.0343$ for $c=0.9$, and $0.0686$ for
$c=0.81$ (the Corollary 5.1 target).

The per-step normalization alone moves $\log\nu_1$ by $(\log s)/r\approx0.0067$. A horizontal winner moves it by
$\log(\lambda_1(\pi\Lambda)/\lambda_1(\Lambda))$, which on Haar-like states has an Exp-type tail on scale O(1/r), but is
unconstrained otherwise. So Freedman is not excluded, but it needs a good set on which **every** step changes λ₁ by less than
1.5%, or less than 7% at the relaxed target. Its exit probability is again a terminal-type quantity.

**Proposition 9 (window counts and profile functionals).**
* Let $N_t=\#\{j\le t:\text{window }j\text{ has ratio}<c\}$. The terminal event concerns window $T$ alone. Any majorant built from
  $N$ has $\Phi_{T-1}\ge\Pr[\text{window }T\text{ bad}\mid X_{T-1}]$, so it is $h_{T-1}$ itself: no gain.
* Functionals of the GS profile (the log-potential $\sum(N-i)\log\|b_i^*\|$, sliding-window log-volumes, deficits relative to GSA)
  are functions of $(D_t,s_1,\dots,s_t)$. On the minimum they act only through $h_T$, and Corollary 5.1 captures them optimally
  among cap-type arguments. Part 114 shows that no profile datum forces a terminal minimum. By Theorem 2 the profile route can only
  add the worst case over profile fibers.
* Linear (counting) potentials $\Phi=\sum_xf(|x|)$, and sublattice counts, were shown to amplify in Parts 110, 124 and 126.

## 7. The exact remaining gap

The potential route to δ for the first pass at b = 506 reduces to two conditional statements. Both are needed, and both are
one-step statements in the sense of Theorem 3(c), restricted to a good set with charged exits.

* **(C1) Dual cusp escape (GH floor).** Show that $\sum_t\mathbb E[\min(1,\varepsilon_t(X_{t-1}))]\le\eta_1$, with $\varepsilon_t$ the
  exact Fourier ratio of Theorem 5 at κ = 1.05. Given Theorem 4(d), (C1) is a statement that the inherited short dual vectors of the
  restart are expanded away. On $k=1$ steps they evolve by $A_v^{-1}$, which lengthens them by
  $\sqrt{1+(s^2-1)\cos^2}$. If $\hat v_h$ were uniform on the sphere (heuristic, stronger than (DS)), normalized dual lengths would grow with probability ≈ 0.93 per step at $s=30$, $r=505$. The dual dynamics
  is monotone, so (C1) looks substantially easier than the primal problem. Unproved.
* **(C2) Ratio at the relaxed target.** If (C1) holds, then $\lambda_1(\Lambda_T)\ge F$ follows from $Y_T\ge0.8052$ (instead of
  0.954). This requires either Conjecture E, or a Freedman good set (Proposition 8, increments < 0.0686). In both cases the open
  ingredient is the same: on reachable states, horizontal winners must be negatively correlated with short planes through the old
  shortest vector. This is the Part 120/126 horizontal term, now isolated as the *only* non-random branch of the step (Theorem 4(b)).
  The vertical branch has an exact random-flow form, and (DS) suffices for it.

At b = 406 even (C1) with κ = 1 leaves $F/h_T=1.585>1$, so the first pass cannot reach the floor (as in Part 114). Later tours need
a posterior filtration (Theorem 3(d)).

## Reproducible checks

```python
from mpmath import mp, mpf, log, exp, pi, loggamma, beta
mp.dps = 40
logV = lambda j: (j/2)*log(pi) - loggamma(1 + mpf(j)/2)
G = lambda j: exp(-logV(j)/j)
q, T = 3329, 512
F = {406: mpf('24.5807'), 506: mpf('27.4538')}
for b in (406, 506):
    d = b - 1; a = mpf(d)/b
    print(b, float(1/G(d)))
    for kap in ('1.0', '1.02', '1.05', '1.10'):
        hT = G(d) * q**(a**T) * (mpf(kap)*G(b))**(-(1 - a**T)/a)
        print(' ', kap, float(hT), float(F[b]/hT))
for c in ('0.954', '0.9', '0.81'):
    lam = log(1/mpf(c)); print(c, float(3*lam/(2*log(100))))
r = 505
for s in (20, 30, 35):
    for th in ('0.25', '0.5', '0.75'):
        p = mpf(th)*r
        print(s, th, float(s**(-p/r) * beta(mpf(1)/2, (r-1-p)/2) / beta(mpf(1)/2, mpf(r-1)/2)))
print(float(mpf(30)**(-mpf(1)/r)), float(mpf('0.954')**(r/2)))
```

The rank-2/3 enumeration check of Theorem 4 was run with numpy. Draw a random basis $B$ and displacement $u$. Enumerate the window's
shortest vector, keeping only primitive minimizers with $k\ge1$. Then compare $|Q_v x|$ with $|A_v x|$ for basis vectors and for
$\lambda/k$, check $Q_v(u+e)=Q_v(-\lambda/k)$, and test $|\langle\mu,v_h\rangle|\le|\mu|^2/2$ for small $\mu$.

[Wall 1](../PROOF_GAP.md) · [First tour](wall1_first_tour.md) · [Terminal mixing](wall1_terminal_mixing.md) ·
[Determinant drift](wall1_idea_drift.md) · [Selection law](wall1_selection_law.md) · [Plane count](wall1_plane_count.md) ·
[Band moments](wall1_band_moments.md)

## Audit

Independent audit (Claude, review sub-agent). The audit checked the note against PROOF_GAP Wall 1 (Parts 103, 105, 107–111, 114, 120,
125, 126, 134–136) and against [first_tour](wall1_first_tour.md), [terminal_mixing](wall1_terminal_mixing.md),
[idea_drift](wall1_idea_drift.md) and [band_moments](wall1_band_moments.md). All numerics were recomputed with fresh mpmath scripts
(50 digits). Theorem 4 was re-tested with a separate numpy enumeration in ranks 2–3 (584 primitive windows: up to 216 vertical, 3 of them
with k = 2, and 368 horizontal).

**Verdict: MINOR CAVEATS, with one substantive correction (Proposition 7, first bullet).** Theorems 1–5, Corollaries 2.1 and 5.1,
and the conditional status of the 34.10 / 0.805 improvement are sound. No claimed value of δ depends on the corrected statement.

### Confirmed

* **Theorem 1.** (a) is correct: the least majorant is h, and the best potential bound is δ. In (b), the killed process
  Φ_t·1{X_j ∈ G_j, j ≤ t} is a supermartingale, as claimed. In (c), the Foster–Lyapunov majorant Ψ_t meets its recursion with
  equality. This needs Φ ≥ 0, ψ decreasing and Y < c ⇒ ψ(Y) ≥ ψ(c), all of which hold.
* **Theorem 2 and Corollary 2.1.** The adversary value V is the least π-potential, and V_t(π_t) is a supermartingale along the true
  chain. Corollary 2.1 matches Part 109 (terminal_mixing l. 55). After 511 zero draws from the cube, **every** final draw gives
  ratio < 0.21 at both ranks.
* **Theorem 3 (zero-draw barrier).** At the first graph append, Part 108 gives the deterministic state Λ = qZ^r with H = T[q].
  Under U = 0 we have W = Λ ⊕ Ze. Since λ1(Λ) = q > 1, ±e is the unique minimal pair whatever the tie rule. Q_e is the identity
  on E, so (Λ, H) is fixed for all 512 graph appends. The all-zero history is reachable under the true kernel: each draw has
  probability |H|^{-1} = q^{-r} > 0. So K^0 is a selector of actual successors.
  * K^0 satisfies every universally quantified pathwise statement over 𝓡.
  * It agrees with K off the finite set 𝓡, so it satisfies every statement about non-atomic input laws.
  * Hence Y_T = 1/G_r with probability one: 0.2035524700 at 406 and 0.1825670712 at 506. This matches Part 108's cubic constants.
  * K^0 is of course *not* Part 108's exact law, which is uniform on H. That is exactly the point: the hypothesis classes in (a)
    cannot tell the two apart. (c) and (d) are correct as stated.
* **Theorem 4.** All parts were re-derived by hand.
  * (a) Order of λ/k is k ⇔ v primitive. The identities Q_vW = Q_v(Λ + Zλ/k), (1 − k²/s²)/|v_h|² = 1/s² and det = D/s hold, and so
    does the matrix-determinant covolume formula.
  * (b) The horizontal-winner formula is correct.
  * (c) The Rankin recursion is correct. Δ = M ∩ Λ is primitive in Λ because M is primitive in W.
  * (d) W* and Λ'* = W* ∩ v^⊥ are as stated. The bound λ1(Λ'*) ≥ min(λ1(Λ*), 1), improved to λ1(Λ*) when k ≥ 1, holds because
    (0, j) ⊥ v forces jk = 0. The k = 1 dual-length formula and the factor 30^{−1/505} = 0.993288 are correct.
  * Numerics. These all held in every non-degenerate window to 1e−9: the isometry Q_v|_E ~ A_v on the generators of Λ + Zλ/k, the
    identity Q_v(Ũ + e) = Q_v(−λ/k), the Voronoi inequality, det Λ' = D/s, the rank-1 covolume formula, dual monotonicity, the k = 1
    dual formula, and a_1(Λ') ≥ min(a_1, a_2)(Λ)/s. One apparent failure, a horizontal window with s ≠ λ1(Λ), came from the
    enumeration box in the audit script, not from the note.
* **Theorem 5 and Corollary 5.1.**
  * The Poisson/character computation is exact. Cosets of H^⊥ ⊂ Λ* index the characters of H.
  * Absolute summability holds: |1̂_{B_{ε/2}}|² decays like |ξ|^{−(r+1)}.
  * P(U) > 0 gives a layer-one vector of length < √(1 + ρ²), because supp φ ⊂ open B_ρ. The Chebyshev step is correct.
  * Corollary 5.1 is Theorem 1(b) with exits charged by min(1, ε_t). On the good event, Part 114's recurrence D_t = D_{t−1}/s_t
    gives the floor deterministically.
* **Table in §5.** Recomputed values:
  * κ = 1: 35.17751 / 0.780436 at b = 506, and 15.50464 / 1.585377 at b = 406. This matches Part 114's zero-error column.
  * κ = 1.05: 34.09923 / 0.805115 at 506, and 14.97026 / 1.641969 at 406.
  * κ = 1.02 and κ = 1.10 also agree.
  * The Hermite caps reproduce 28.80953 (506) and 12.33656 (406).
  * The note's "0.8052" is an outward rounding of 0.805115. That direction is acceptable, since a larger ratio target is harder to
    meet.
* **Conditional status of the improvement.** The note states the improvement 28.81 → 34.10 and 0.954 → 0.805 conditionally
  throughout: "if the cap … holds on every step" (summary item 4), "conditional corollary", "If (C1) holds" (§7). This is correct
  wording. Nothing in the note proves the cap.
* **Other constants.**
  * Freedman: 3λ/(2 log 100) = 0.015339 (c = 0.954), 0.034318 (0.9), 0.068636 (0.81).
  * Proposition 6 table: all nine entries agree to 4 digits, e.g. 0.258584 at s = 30, θ = 1/2.
  * 0.954^{252.5} = 6.854·10⁻⁶.
  * Voronoi threshold: 0.23134·s.
  * Rank-i protection: i ≥ 21.36.
  * Dual-growth probability under a uniform direction: 0.93055.
  * Poisson term at κ = 1.05 at the end of the pass: ρ ≈ 35.71, log term −23.3, so e^{−23} is right. At κ = 1 the log term is
    +1.36, so the cap at κ = 1 is not a high-probability event even heuristically.
* **Labels.** The heuristic numbers 0.12, 0.35 and 0.93 are each marked heuristic. Conjecture E, (DS) and (C1) are marked
  conjecture, hypothesis or unproved. (C2) is presented as requiring Conjecture E or a Freedman good set, both open.

### Issues and corrections

1. **(Substantive) Proposition 7, first bullet, and summary item 6 overclaim.** Iterating 4(c) from the cube gives
   a_1(Λ_T) ≥ q·D_T/D_0 = q^{1−r}D_T, since min_j a_{1+j}(qZ^r) = q. With Part 114's Hermite lower bound on D_T at 506
   (h_T ≥ 28.8095), this is about **10^{−1412} × own GH**. It is not "the Part 109/110 type floor" (3.3·10⁻⁸ and 5.3·10⁻⁶ × GH). It
   is even far weaker than Part 108's trivial α^j floor. Part 109/110 floors come from the subunit-run / √3/2 lift mechanism, which
   the Rankin recursion does not see: the recursion divides by s_t at every step.
   * The phrase "the deterministic skeleton is the worst case" is also unjustified. A pathwise lower bound is not shown to be
     attained.
   * Correction: "Iterating 4(c) gives a valid but very weak pathwise floor (≈ 10^{−1412} × GH at 506). Part 109/110's floors
     instead use the lift bound λ1(Λ') ≥ αs. In both, the slack is the replacement of ρ_Δ(U) by 1." Also, j in min_j ranges over
     j ≤ r − 1.
2. **Proposition 6: "M ≤ 2 would suffice … at every exponent" is false for the stated bound.**
   * At θ = 0.25 the factor is 2 × 0.5463 = 1.093 > 1 at s = 20. At s = 30 it is 0.987, which is marginal.
   * The sharper quantile form is not computed.
   * Part 105 bounds the density of the projected *shape* of a Haar block, not the conditional law of v̂_h given a reachable state.
     "Part 105 type" is an analogy only.
   * s ≥ s_min on {k = 1} is an extra hypothesis. Part 109's layer bound gives a probability, not a sure lower bound, so the
     shortfall must be charged as an exit.
   * Prop 6 bounds the change of a single Δ's term. A max-type ν_i^{−p} needs a sum over near-minimal Δ, which EMM supply by
     counting.
3. **Proposition 8 is a barrier for the Bernstein form only.** The Bennett form of Freedman's inequality,
   exp(−(V/M²)·h(λM/V)) with h(u) = (1+u)log(1+u) − u, goes to 0 as V → 0 at fixed M. So with small predictable variance, the
   increment cap M is not forced below 3λ/(2 log(1/p)).
   * The constants 0.01534 / 0.0686 are correct for the stated Bernstein-type bound.
   * The barrier should read "Freedman–Bernstein with V ≳ Mλ/3". Read that way, the real requirement is a joint (M, V) condition on
     the good set.
4. **Scope of Theorem 3.** The zero-draw kernel freezes the *ratio*, but the physical minimum stays q = 3329 ≫ F, and h_T = G_r·q.
   So K^0 obstructs only ratio-type events B_c, and through them the (C2) route as framed. A proof of the physical event
   {λ1(Λ_T) < F} that couples h_T and Y is not excluded by K^0 alone.
   * The summary's wording "cannot bound δ below 1 at any ratio above 1/G_r" is accurate. Readers should not extend it to the
     physical δ of the Lean reduction.
   * Also, the rationality argument in the proof of (a) is unnecessary: finiteness of 𝓡 already makes it ν-null for every
     non-atomic ν.
5. **Heuristic paragraph after Theorem 5 is not labelled.**
   * The e^{−23} Poisson term and the per-vector "< e^{−37}" are correct as numbers. The audit gets amplitude ratios e^{−56.6} at
     |ξ| = 1 and e^{−39.1} at |ξ| = 0.85, at κ = 1.05.
   * But the bulk dual GH at the end of the pass is ≈ 0.88 < 1. So "short dual vector" in the dangerous sense means short relative
     to ≈ 0.88, not physical length < 1.
   * "The danger is only inherited short dual vectors" is a heuristic reading, not a consequence of Theorem 4(d), and should be
     labelled as such.
6. **Minor.** "i ≥ … ≈ 21" should be i ≥ 22, since the threshold is 21.36. The Reproducible-checks snippet reproduces every number
   it targets.

No attack parameters were optimized or searched.
