# Reducer variants: which output laws can be analysed

**Scope.** Plain LWE $(m,n,q)=(511,512,3329)$ with CBD(3) error and secret. The full embedding is $L_A$, of rank $d=1024$ and
covolume $q^{511}$, with plant $u=(e,s,1)$. Its height-zero part is $L_0$, of rank 1023. The question is whether some block-reduction
variant with oracles of rank about 406–512 has an output law that can be *proved* to recover $u$. Several variants are covered: slide
(GN08, ALNS20, Li–Walter), self-dual BKZ and DBKZ (MW16), BKZ with re-randomization between tours, BKZ on sampled sub-designs,
terminal-only reduction, and the two-step "reduce, then exact final block" strategy. For each one the note checks whether the
obstructions of Parts 106 (no selector-uniform bound), 111 (no density) and 112 (no negative association) still apply, and
whether worst-case guarantees can be combined with the uSVP gap.

**Verdict in one paragraph.** (i) The worst-case route is closed for every block size $2\le\beta\le566$, for *any* argument that uses
only the block Hermite inequalities and the gap. This holds even with the exact (unknown) Hermite constants (Theorem B). That is a
proof-method barrier, sharper than the Stage 1 "no admissible β" table. (ii) Obstruction 111 is universal: every reducer, randomized
or not, has an atomic terminal law (Lemma U1). Re-randomization by symmetries of the ensemble does nothing (Lemma U2). (iii) Slide-type
predicates contain bad bases, by two new exact lemmas. With approximate twins (Li–Walter Definition 1), any slack in the dual twin
test lowers the terminal own-GH ratio by an explicit factor (Lemma S1). With exact twins (ALNS20 Definition 3.1, $k\ge n/2$), the fixed
points are parametrized by a rank-$(k+1)$ sublattice $Q$. The terminal ratio is an *exact* function of $\det Q$ and one dual minimum
(Lemma S2), and the densest $Q$ always gives a passing basis. So no predicate-only analysis can reach the 0.954 target unless it proves
a density lower tail for the *selected* $Q$. (iv) The most promising variant is the exact-twin two-block slide of ALNS20 at oracle rank
512 on the plant-free lattice, inside Part 47's decoupling. Its success reduces *exactly* to two statistics of one selected sublattice.
Neither statistic is bounded here, and Part 112 still applies to any tour-chaining proof of them.

Convention: $\gamma_k$ is Hermite's constant for squared norms, $V_k$ the unit-ball volume, and $G_k=V_k^{-1/k}$, so that
$\mathrm{GH}(\Lambda)=G_k\det(\Lambda)^{1/k}$. Unless stated otherwise, every number below is rigorous (mpmath, 30–40 digits). Numbers
marked **[heur]** use the "GH in every block" heuristic or a Haar mean-one cutoff and are given only as illustration.

## 1. The gap of the actual lattice

**Event $E$.**

* (a) $\lambda_2(L_A)\ge 440$ (every vector outside $\mathbb Zu$ has norm at least 440);
* (b) $36.756<\|u\|\le 41.7253$, i.e. $1350<\|u\|^2-1\le1740$.

**Proof.** (a) Take $z=(x,y,t)$ with $\|z\|\le R=440$. If $y-ts\not\equiv0$, then $\Pr_A[z\in L_A]=q^{-511}$, because
$(x-te)+A(y-ts)\equiv0$ and $A(y-ts)$ is uniform. If $y\equiv ts$, then $\|y-ts\|_\infty\le R+3R<q$ forces $y=ts$. In the same way
$x=te$, so $z=tu$. The Gaussian/Poisson majorant of the integer-point count (the same formula as $F_m(R)$ in
[jw_slide](wall1_jw_slide.md), with $N=1024$) gives failure $<2^{-11.80}$. (b) Chernoff bounds with the exact CBD(3) moment generating
function of $X^2$, over 1023 coordinates, give $\Pr[\|u\|^2-1>1740]<0.00582$ and $\Pr[\|u\|^2-1\le1350]<0.00866$. Hence
$\Pr[E]>1-0.0148$. Part (a) alone, together with the upper tail of (b), holds with probability $>0.9939$. ∎

On $E$ the following deterministic bounds hold:

* gap $g=\lambda_2/\lambda_1\ge 440/41.7253=10.5452$;
* Hermite threshold $\lambda_2/\det(L_A)^{1/d}\ge440/57.2423=7.6866$;
* an upper bound on the gap. Projecting along $u$, $\lambda_1(\pi_{u^\perp}L_A)\le\sqrt{\gamma_{1023}}(\det L_A/\|u\|)^{1/1023}$. Since
  $\lambda_2^2\le\lambda_1(\pi_{u^\perp}L_A)^2+\|u\|^2/4$, Blichfeldt's $\gamma_{1023}\le122.22$ gives $\lambda_2\le633.47$ and
  $g\le17.2343$.

## 2. Worst-case guarantees cannot be combined with this gap

**Sufficient criterion (standard).** Suppose a reducer guarantees $\|b_1\|\le\alpha\lambda_1$ with $\alpha<g$. Then $b_1\in\mathbb Zu$,
and primitivity forces $b_1=\pm u$. Likewise, a guarantee $\|b_1\|\le\alpha_H\det^{1/d}$ suffices when $\alpha_H<7.6866$.

| Guarantee (theorem) | factor | β = 406, $\gamma\ge$ MH | β = 506, $\gamma\ge$ MH | β = 506, Part 98 cap |
|---|---|---:|---:|---:|
| BKZ, Schnorr / repo `reduced_approx_factor` | $\gamma_\beta^{(d-1)/(\beta-1)}$ | 3154 | 991.9 | 3505 |
| slide, GN08 Eq. (2), ALNS20 Thm 1.1 ($d\ge2k$), δ = 1 | $\gamma_\beta^{(d-\beta)/(\beta-1)}$ | 129.9 | 32.91 | 62.36 |
| Hermite: slide / DBKZ (MW16; ALNS20 Eq. (1)) | $\gamma_\beta^{(d-1)/(2(\beta-1))}$ vs 7.69 | 56.16 | 31.49 | 59.21 |

"MH" is the Minkowski–Hlawka lower bound $\gamma_k\ge(2\zeta(k)/V_k)^{2/k}$ (24.276 at 406, 30.143 at 506). The guarantees are increasing
in $\gamma$, so evaluating them at MH gives the most optimistic value any proof of these theorems could reach. Every entry exceeds
$g=10.55$ (respectively 7.69). For $k\ge n/2$, ALNS20 Thm 1.2 gives
$\delta_S=\delta^2\sqrt{\gamma_k}(\delta^2\gamma_{q})^{\frac{q+1}{q-1}\frac{n-k}{2k}}$ with $q=n-k$. At $n=1024$ and δ = 1 it falls
below 10.545 only from oracle rank $k=774$ even with MH values, and never for $k\le1022$ with Blichfeldt values (11.06 at $k=1022$). So
the worst-case approximation route needs oracle rank in the high 700s at the very least. This agrees with Stage 1. The next theorem
shows that this is a barrier for the *method*, not just for the current constants.

**Theorem B (profile-only barrier).** Let $\ell_1,\dots,\ell_d$ be log Gram–Schmidt lengths. A *profile certificate* at width β is a
proof that derives $b_1=\pm u$ from the following constraints only:

* (P1) $\sum\ell_i=\log\det L_A$;
* (P2) for every overlapping (possibly truncated) block of length $l\le\beta$, $\ell_{\rm head}\le\frac12\log\gamma_l+$ the block mean,
  with the *true* $\gamma_l$;
* (P3) no capture: $\ell_1\ge\log\lambda_2$, and $\lambda_2^2\le g_i^2+\frac14\sum_{j<i}g_j^2$ for every $i$ (size reduction);
* (P4) for some index $t$ (the plant's last nonzero coefficient), $g_j\le\|u\|$ for every block head $j\in[\max(1,t-\beta+1),t]$.

On $E$, for every $12\le\beta\le566$, the system (P1)–(P4) has a real solution. The same holds for $2\le\beta\le11$ using the known
values $\gamma_2,\dots,\gamma_8$ and the laminated-lattice bounds $\gamma_9\ge2$, $\gamma_{10}\ge2.059$, $\gamma_{11}\ge2.14$. Hence no
profile certificate exists at any width $\beta\le566$. That includes the estimator range 406–506.

*Proof.* Put $\rho=\log\gamma^{\rm MH}_\beta/(\beta-1)$ and $\rho_h=\log(\lambda_2/\|u\|)/(d-\beta)$. Take $t=d$.

1. **Head.** Set $\ell_1=\log\lambda_2$ and decrease linearly with slope $\rho_h$ to $\ell_{d-\beta+1}=\log\|u\|$.
2. **Tail.** After index $d-\beta+1$, stay at or below $\log\|u\|$: first flat, then decreasing with slope at most ρ. The flat length
   moves the tail sum continuously over $(-\infty,505\log\|u\|]$.
3. **(P1).** It is satisfiable because head sum + $505\log\|u\|\ge4335.0>4144.43=511\log q$ in the worst corner of $E$ (checked at all
   four corners).
4. **(P2).** Every step decreases by at most $\max(\rho_h,\rho)$, so a block of length $l$ has head minus mean at most $\rho(l-1)/2$.
   Mordell's inequality ($\gamma_l^{1/(l-1)}$ is nonincreasing) gives $\rho\le\log\gamma_l/(l-1)$ for every $l\le\beta$, because
   $\gamma_\beta\ge\gamma^{\rm MH}_\beta$.
5. **Requirement.** Hence $\rho_h\le\rho$ is all that is needed, i.e. $(\gamma_\beta^{\rm MH})^{(d-\beta)/(\beta-1)}\ge\lambda_2/\|u\|$.
   On $E$ the right side is at most 17.2343. The left side is at least 17.2343 for every β in $12..566$ (checked one β at a time; it
   first drops below at β = 567). For β ≤ 11 the left side is at least $2^{1015/8}$.
6. **(P3).** $f(i)=e^{-2\rho_h(i-1)}+\frac14\sum_{j<i}e^{-2\rho_h(j-1)}$ is increasing, because $e^{-2\rho_h}>3/4$, and $f(1)=1$. In the
   tail, $\frac14\sum_{j\le d-\beta}g_j^2\ge\frac14\lambda_2^2(1-g^{-2})/(2\rho_h)\gg\lambda_2^2$.
7. **(P4)** holds by construction. ∎

*Reading.* The obstruction is not the size of $\gamma_\beta$. The profile inequalities allow a total drop of
$\gamma_\beta^{(d-\beta)/(\beta-1)}\approx33$ over the $d-\beta$ indices before the plant's block, while the gap is only 10.5–17.2. A
proof below width 567 must use more than profile inequalities and the gap, i.e. information about which basis the algorithm outputs.
Part 37 ([capture_depth](wall1_capture_depth.md)) gives actual integral bases with gap 1.1. Theorem B is the profile-level version at
the true gap; it does not construct an actual lattice basis. Worst-case lattice lower bounds for BKZ (Ajtai 2008, *Theory of
Computing* 4) are exponential with unspecified constants and do not bear on 10.5.

## 3. Universal lemmas: what randomization can and cannot change

**Lemma U1 (obstruction 111 is universal).** Let $R$ be any reducer, deterministic or randomized, with coins $C$ independent of the
input. Its terminal block is $\pi_{S^\perp}L_A$ for a saturated sublattice $S\subset L_A$. Then the law of the normalized terminal shape
is purely atomic, hence singular to Haar on $X_\beta$, for *every* $R$.

*Proof.* There are finitely many designs $A$ and a countable support for $u$. For each $(A,u)$ there are countably many saturated $S$.
The terminal shape is a function of $(A,u,S)$, so its law is a countable mixture of point masses. Haar has no atoms
([chain_law](wall1_chain_law.md) §C, Part 111). ∎

So no $L^2$/density or spectral-gap chaining (Part 111) can be used for *any* variant, randomized or not, from any starting basis. Proofs
must bound the specific terminal event: by first moments over $S$, by predicates, or by finite exact recursions.

**Lemma U2 (symmetry no-op).** Let $\mathcal G$ be the group generated by row permutations, column permutations with sign flips
applied consistently to $(A,s)$, and row sign flips applied to $(A,b)$ (signed permutations of both index sets). The joint law of
$(A,u)$ is $\mathcal G$-invariant. Hence, for any reducer $R$, running $R$ on $g\cdot(A,b)$ for an independent uniform $g\in\mathcal G$,
then mapping the output back, has the same success probability as $R$.

*Proof.* $A$ is uniform, and CBD is symmetric and i.i.d. Each $g$ is an isometry of the embedding that maps $L_{A,b}$ to
$L_{gA,gb}$ and $u$ to $gu$. Success is invariant under isometries. ∎

The only randomizations not covered by U2 are basis changes within the same lattice: random unimodular transforms of retained blocks,
random rotations, re-randomized enumeration seeds. These leave every projected lattice unchanged. They act only through *which*
saturated $S$ is selected. By [chain_law](wall1_chain_law.md) §C, the conditional law given the parent stays countably supported, at
total variation exactly 1 from any fresh Haar shape. **Fresh randomization between tours therefore cannot import Haar statistics.**
Its only possible effect is to change the selection kernel $p_L(S)$.

**Scope of Parts 106 and 112.** Part 106 rules out bounds uniform over the selector. Part 112 rules out FKG-type chaining of
SVP-conditioned events. Neither touches two other proof modes: (a) *predicate-uniform* bounds (sup over all bases passing a static
test, Parts 86–92), and (b) *weighted-selection* bounds $p_L(S)=w(S)/Z(L)$, which give
$\Pr[\mathrm{bad}]\le\mathbb E[\sum_Sw(S)1_{\rm bad}(S)]/z+\Pr[Z<z]$ ([random_block_reducer](wall1_random_block_reducer.md)). Mode (b)
needs a sampler for $w$ on a rank-$\ge517$ sublattice family. No such sampler exists with the cost profile of a block-reduction
algorithm, so (b) is not a reducer variant. The rest of this note tests mode (a) on the slide family. There the right obstruction is the
*predicate ceiling*.

## 4. Slide reduction: the predicate contains bad bases

Use the plant-free lattice $L=L_0$, of rank $n=1023$ (Part 47), with two blocks: a prefix $P=L_{[1,k]}$, an extension
$Q=L_{[1,k+1]}$, and a terminal block $T=\pi_{P^\perp}L$ of rank $b=n-k$. Put $R=\pi_{b_1^\perp}Q$ (rank $k$, the dual-twin block), and
let $x_0\in R^*$ be its reversed-dual first vector, so $\|x_0\|=1/\|b^*_{k+1}\|$. The own-GH ratio is
$\rho(B)=\lambda_1(T)/\mathrm{GH}(T)$; Part 114's target at 506 is 0.954.

**Lemma S1 (twin-slack transfer; Li–Walter Definition 1, $p=2$).** Let $B$ satisfy Li–Walter Definition 1 with twin factor $a$ and exact
terminal SVP:

1. $\|b_1\|\le a\det(P)^{1/k}$;
2. $\|x_0\|\le a\det(R)^{-1/k}$;
3. $b^*_{k+1}=\lambda_1(T)$;
4. size reduction.

Suppose some primitive $x\in R^*$ has $(2/\sqrt3)\|x_0\|\le\|x\|\le a\det(R)^{-1/k}$, and write $t=\|x\|/\|x_0\|$. Then there is a basis
$B'$ of $L$ that also satisfies Definition 1. It has the same $b_1$ and the same $Q$, and
$$\lambda_1(T')=1/\|x\|,\qquad \rho(B')=\rho(B)\,t^{-(b-1)/b}.$$

*Proof.* Put $P'=Q\cap x^\perp$. Since $x\perp b_1$ (as $x\in R^*$), $b_1\in P'$. Also $P'$ is saturated of rank $k$, and
$\det P'=\det Q\,\|x\|$. Complete $b_1$ to a basis of $P'$, take $b'_{k+1}$ in $Q\setminus P'$, then a basis of $T'=\pi_{P'^\perp}L$ that
starts with $w'=\pi_{P'^\perp}b'_{k+1}$, and size-reduce. Check the four conditions:

1. $\det P'\ge\det Q\,\|x_0\|=\det P$, so condition 1 is inherited.
2. Block $[2,k+1]$ is still $R$, and its reversed-dual first vector is now $\pm x$. Condition 2 is exactly the upper end of the window.
3. Take $v\in L$. If $v\in Q$, then $\pi_{P'^\perp}v\in\mathbb Zw'$, with $\|w'\|=1/\|x\|$. If $v\notin Q$, then
   $\|\pi_{P'^\perp}v\|\ge\lambda_1(\pi_{Q^\perp}L)$. Now $\pi_{Q^\perp}L$ is $T$ projected off its shortest vector $b^*_{k+1}$, so its
   minimum is at least $(\sqrt3/2)\lambda_1(T)$ (Lean `shortest_projection_gap`). That is at least $1/\|x\|$ by the lower end of the
   window. Hence $\lambda_1(T')=\|w'\|$.
4. Size reduction is applied explicitly.

Finally, $\det T'=\det L/\det P'$, and dividing gives the ratio formula. ∎

*Consequence.* Any certificate that holds simultaneously for all Definition 1 bases (Parts 88, 89, 92) is at most
$\inf_B\rho(B)\,s(B)^{-(b-1)/b}$, where $s(B)$ is the dual-twin slack among passing bases $B$ for which the window hypothesis holds. How
large the slack is depends on the implementation. With $a$ computed from the Part 98 cap ($\gamma_{506}\le56.2142$, as in Part 88),
the GH-in-every-block profile has slack $s=(\sqrt{56.2142}/G_{506})^{516/505}=1.3768$. That gives a ceiling factor
$s^{-505/506}=0.7268$, or at least $0.8663$ at the threshold $t=2/\sqrt3$ **[heur]**. With $a$ computed from $\gamma^{\rm MH}$ the slack
would be 1.0014 and the lemma would not apply. The window hypothesis can be checked on any given output. It is not proved to hold
generically.

**Lemma S2 (exact twins; ALNS20 Definition 3.1, $k\ge n/2$, δ = 1).** Take oracle rank $b$, prefix rank $k=n-b\le b$, and the
conditions:

* $b_1=\lambda_1(P)$;
* $\|x_0\|=\lambda_1(R^*)$ (exact DSVP on $[2,k+1]$);
* $b^*_{k+1}=\lambda_1(T)$;
* size reduction. ALNS20's auxiliary 1/3-LLL clause on the DSVP block is omitted; it serves efficiency.

(a) **Exact identity.** Every such basis has
$$\rho=\frac{\det(Q)^{1/b}}{G_b\,\det(L)^{1/b}\,\lambda_1(R^*)^{(b-1)/b}}
 =\frac{\det(Q)^{(n-1)/(bk)}\,\|b_1\|^{-(b-1)/(bk)}\,\eta_*^{-(b-1)/b}}{G_b\det(L)^{1/b}},\qquad
 \eta_*=\lambda_1(R^*)\det(R)^{1/k}.$$
(b) **Parametrization.** Let $Q$ be any saturated sublattice of rank $k+1$. Let $b_1$ be a shortest vector of $Q$, $x_0$ a shortest
vector of $(\pi_{b_1^\perp}Q)^*$, and $P=Q\cap x_0^\perp$. If $\lambda_1(\pi_{Q^\perp}L)\ge1/\|x_0\|$, then some basis with this $P$ and
$Q$ satisfies the predicate.
(c) **Densest $Q$.** The side condition in (b) holds automatically when $Q$ has minimal determinant among saturated sublattices of rank
$k+1$. So every lattice has a passing basis whose terminal ratio is (a) evaluated at its densest $Q$.

*Proof.* (a) $\lambda_1(T)=b^*_{k+1}=1/\lambda_1(R^*)$ and $\det P=\det Q/b^*_{k+1}$. Substitute, using $\det R=\det Q/\|b_1\|$.

(b) $b_1$ is shortest in $Q$, hence in $P$. Block $[2,k+1]$ is $R$, with reversed-dual first vector $x_0$ (exact). The terminal condition
follows as in S1 step 3, using the side condition.

(c) For a corank-one $P\subset Q$ and $v\notin Q$, the saturation of $P+\mathbb Zv$ has rank $k+1$. Minimality then gives
$\det(P)\|\pi_{P^\perp}v\|\ge\det Q=\det(P)\|w\|$. ∎

*Numbers at $b=512$, $k=511$, $\det L=1$.* For $\rho\ge0.954$, (a) requires:

* $\log\det Q\ge953.40$ if only $\eta_*\le\sqrt{\gamma_{511}}$ (Blichfeldt) is used;
* $\log\det Q\ge862.08$ if $\eta_*$ equals its typical value $G_{511}$.

The GH-in-every-block profile has $\log\det Q=874.21$ **[heur]**. The Haar mean-one level for saturated sublattices of rank 512 is
$\log T_*=547.87$, from Part 88's $K_j$ formula **[heur]**. At that level (c) gives $\rho\approx0.279$ **[heur]**. Markov over the Haar
count only bounds $\Pr[\exists Q:\det Q\le T]\le K T^n$, i.e. the *densest* level. So any predicate-uniform route for ALNS20 exact twins
is capped near the densest-$Q$ value. This is consistent with Part 96's exact-twin Markov ceilings (0.3850 / 0.5184) and explains them:
the ceiling comes from the predicate, not from Markov.

## 5. The other variants

| Variant | 106 | 111 | 112 | Worst case + gap | What a proof needs |
|---|---|---|---|---|---|
| Slide GN08/ALNS20, $k\le n/2$ | n/a (predicate) | applies (U1) | n/a to predicate bounds | closed (Thm B; 32.9 > 10.5) | predicate ceiling (S1); law of the selected $Q$ |
| ALNS20 $k\ge n/2$, exact twins, oracle 512 | n/a | applies | applies only to tour chaining | closed | lower tail of $\log\det Q_{\rm sel}$ ≥ 862–953 plus an $\eta_*$ quantile (S2) |
| Li–Walter two-block (506) | n/a | applies | — | closed | as above plus slack control (S1) |
| Self-dual BKZ (MW16 Def. 1) | n/a | applies | — | closed | Parts 86–87 predicate bounds; MW stabilization is open. S1 does not transfer verbatim: overlapping dual windows also see $P$ |
| DBKZ (MW16, tour-count stop) | applies | applies | applies | closed (Hermite 31.5 > 7.69) | no static predicate: full tour law |
| BKZ with fresh randomization | applies | applies (U1) | applies | closed | randomization changes only $p_L(S)$ (U2, §3) |
| BKZ on random sub-designs | applies | applies | applies | closed | random subsets are $A$-independent; only disjoint row blocks give independence (Part 132) |
| Terminal-only from a computable prefix | n/a | n/a (exact law) | n/a | — | only $A$-independent prefixes have exact laws (Parts 39–40) |
| Two-step (Part 47 decoupling) | inherits | inherits | inherits | closed | null-only quantile of the reduced $L_0$ |

**Sub-designs, quantified.** For a row subset of size $r$ selected adaptively from the input, Part 38 gives
$p\le(I+1)/\log_2(1/h)$, with $I\le\log_2\binom{511}{r}$. A fixed subset ($I=0$) is Part 39 (647). For $k$ disjoint *fixed* blocks,
$\Pr[\text{all fail}]\le\mathbb E_s\prod_if_{r_i}(\|s\|^2)$ (Part 132), with optimum 646 (Part 131). Randomizing the choice of the
blocks adds nothing, by U2.

**Terminal-only and progressive reduction.** The prefix laws that can be computed exactly are those of $A$-independent coordinate
prefixes (Part 39), and the surviving $q$-prefix of LLL/BKZ (Part 44: up to 105 heads at 406, 22 at 512), whose quotient is Part 39's
lattice. An HKZ prefix of rank $j$ on $L_0$ has an exact Haar recursive density (Part 46), with acceptance $2^{-j(j-1)/2}$. No exact
law on the $q$-ary ensemble is known. Choosing among $F$ fixed prefixes costs $\log_2F$ bits in Part 38, so reaching 406 needs
$F\ge2^{679}$ (Part 40). Terminal-only reduction with a law that can be computed therefore stays at 646/647.

## 6. Most promising variant, and what remains

**Candidate: the ALNS20 $k\ge n/2$ exact-twin reducer on $L_0$, with the Part 47 final SVP.** The oracle rank is 512 (rank-511 SVP and
DSVP, rank-512 terminal SVP), close to the estimator's 506. Reasons:

1. With exact DSVP the slack mechanism of S1 is unavailable.
2. Its fixed points are exactly the sublattices $Q$ with the side condition (S2(b)).
3. The terminal ratio is a closed-form function of $(\det Q,\|b_1\|,\eta_*)$ (S2(a)).
4. Part 47 removes the plant from the selection. Part 47's audited Babai bound covers lifting.
5. Uniqueness then needs the Part 94/103 tests on $H=\pi_{P^\perp}L_0$. Given $L_0$ these depend only on the *distribution* of
   $\lambda_1(T)$ and its coset geometry ([dist_unique](wall1_dist_unique.md)), with the Lean certificate `uniquenessProbability`.

**Rigorous here.** §1 (event $E$, gap 10.55–17.23, Hermite threshold 7.69); Theorem B (no profile certificate for $\beta\le566$);
U1–U2; S1 and S2 (deterministic, elementary). The ALNS20 statements quoted are taken from the paper's informal theorems 1.1 and 1.2.
The formal numbering (Definition 3.1, Theorems 3.2 and 4.2) comes from an extracted summary and should be checked against the TeX
source before it is formalized.

**Not proved, and needed:**

* (i) A lower quantile of $\log\det Q_{\rm sel}$ for the *algorithm's* output, at least 862.08 with typical $\eta_*$. This is a
  history-averaged statement about a selected sublattice, so Parts 105–128 apply in full whenever it is proved by tour chaining.
* (ii) An upper quantile of $\eta_*$ for the selected dual block. Upper bounds on a selected minimum are void events, and Part 112
  shows that SVP conditioning has no negative association.
* (iii) A $q$-ary transfer.

Termination with δ = 1 also needs either ALNS20's $(1+\varepsilon)$ slack or the outer potential argument of Part 88. With δ > 1,
S1-type slack returns once $\delta\ge2/\sqrt3$.

**Honest bottom line.** No variant in the list yields a provable success at $\beta\le512$ with current tools. What this note adds is a
precise boundary:

* worst-case and profile reasoning is impossible below 567 (Theorem B);
* randomization cannot help the law (U1, U2);
* static predicates are intrinsically capped (S1, S2).

The exact-twin ALNS reducer reduces the remaining open problem to two explicit statistics of one selected rank-512 sublattice.

## Reproduction

```python
from mpmath import mp,mpf,log,exp,sqrt,pi,loggamma,zeta,binomial
mp.dps=40; q=mpf(3329)
def logF(R,N=1024,m=511):
    t=mpf(N)/(2*R**2); z=exp(-pi**2/t)
    return t*R**2+N*log(sqrt(pi/t)*(1+2*z/(1-z)))-m*log(q)-log(2)
assert logF(mpf(440))/log(2) < -11.8
p={a:binomial(6,3+a)/mpf(64) for a in range(-3,4)}
lm=lambda l: log(sum(p[a]*exp(l*a*a) for a in p))
up=min(1023*lm(mpf(i)/4000)-mpf(i)/4000*1740 for i in range(1,400))
lo=min(1023*lm(-mpf(i)/4000)+mpf(i)/4000*1350 for i in range(1,400))
assert exp(up)<0.00582 and exp(lo)<0.00866
logV=lambda n:(mpf(n)/2)*log(pi)-loggamma(1+mpf(n)/2)
gMH=lambda n:exp((log(2*zeta(n))-logV(n))*2/n)
gBl=lambda n:(2/pi)*exp(loggamma(mpf(n)/2+2)*2/n)
ul,uh=sqrt(1351),sqrt(1741); d=1024
lam2u=sqrt(gBl(1023)*exp(2*(511*log(q)-log(ul))/1023)+uh**2/4)
gu=lam2u/ul; assert gu<17.2344
assert all(gMH(b)**(mpf(d-b)/(b-1))>=gu for b in range(12,567))
assert gMH(567)**(mpf(d-567)/566)<gu
for L2,u in ((440,ul),(lam2u,ul),(440,uh),(lam2u,uh)):
    assert 519*(log(L2)+log(u))/2+505*log(u) > 511*log(q)
```

Sources: Gama–Nguyen, *Finding short lattice vectors within Mordell's inequality*, STOC 2008; Aggarwal–Li–Nguyen–Stephens-Davidowitz,
*Slide reduction, revisited*, CRYPTO 2020, [arXiv:1908.03724](https://arxiv.org/abs/1908.03724) (Thms 1.1, 1.2, Eqs. (1)–(2));
Micciancio–Walter, *Practical, predictable lattice basis reduction*, EUROCRYPT 2016; Li–Walter,
[ePrint 2023/140](https://eprint.iacr.org/2023/140); Ajtai, *Theory of Computing* 4 (2008); repository Parts 37–47, 86–132.

## Audit

**Verdict: MINOR CAVEATS.** One proof needs a repair, which is given below. The statements and conclusions survive. §1, §2,
U1, U2, S1 and S2(a)–(c) are correct. The Theorem B proof as written is invalid for $\beta\le368$, but the theorem is true by
the repaired construction below. The S2 thresholds are off by about 0.7–0.9 nats and are mis-stated as "requires". Several
labels and citations need small fixes. Checks were run in a scratch directory (not committed). The note's reproduction script
passes as written.

**Checked and confirmed (independent mpmath, 30–40 digits).**

* §1: $\Pr_A[z\in L_A]=q^{-511}$ when $y\not\equiv ts$ ($q$ prime). The $\|\cdot\|_\infty<q$ lifting argument is valid. Failure
  is $<2^{-11.80}$. The Chernoff tails are $<0.00582$ and $<0.00866$, so $\Pr[E]>0.98524$, and (a) with the upper tail
  holds with probability $>0.9939$. $\det^{1/d}=57.24231$. Gap $\ge10.54516$, Hermite threshold $7.68662$.
  $\gamma_{1023}^{\rm Bl}=122.224$. $\lambda_2\le633.460$ and $g\le17.23423$. The worst-case corners are chosen in the
  conservative direction.
* §2 table: $\gamma^{\rm MH}_{406}=24.2764$ and $\gamma^{\rm MH}_{506}=30.1435$. The entries 3154.1 / 991.89 / 3505.4,
  129.92 / 32.906 / 62.358 and 56.161 / 31.494 / 59.206 are all reproduced. For ALNS20 Thm 1.2 at $n=1024$, the first oracle
  rank below 10.5452 with MH values is $k=774$ (10.537; at 773 it is 10.562). With Blichfeldt values the factor is 11.058 at
  $k=1022$, and its minimum over $512\le k\le1022$ is 11.056.
* Theorem B, numerically: $(\gamma^{\rm MH}_\beta)^{(d-\beta)/(\beta-1)}$ is 17.2956 at 566 and 17.1262 at 567. The four corner
  sums of (P1) at β = 506 are $\ge4335.006>4144.428$.
* ALNS20, checked against the arXiv TeX source (only v1 exists, `slidearXiv.tex`). The theorem counter is per section and
  shared, so the numbering is Thm 1.1 and Thm 1.2 (informal), Def 3.1 ($n\le2k$ slide), Thm 3.2 (property), Thm 3.3
  (correctness), Cor 3.4, Def 4.1 ($n\ge2k$), Thm 4.2. Eq. (1) is the MW factor $\gamma_k^{(n-1)/(2(k-1))}$ and Eq. (2) is GN's
  rounded factor. The note's formulas for Thm 1.1 and Thm 1.2 match the source exactly. The "1/3-LLL clause" is part of ALNS20's
  definition of δ-DSVP-reduced (§2), as the note says. The §6 remark that the numbering "should be checked" can now be removed:
  it is correct.
* Def 3.1 in note notation: ALNS $(k,q)$ corresponds to the note's $(b,k)$. Def 3.1 also requires $B_{[i,n]}$ to be
  SVP-reduced for every $i\in[q+1,\max\{k,q+1\}]$. At $n=1023$ and ALNS $k=512$ this is the single block $i=q+1$, so S2's
  predicate is exactly Def 3.1 minus the LLL clause. For general $b>k+1$ the extra conditions can be met in S2(b)/(c) by
  HKZ-reducing $\pi_{Q^\perp}L$. LLL-reducing the DSVP block keeps $b^*_{k+1}$ maximal, so the omitted LLL clause is also
  attainable.
* U1 and U2 are correct. The group in U2 consists of isometries preserving the law of $(A,s,e)$. S1 steps 1–4 were checked:
  $x\in R^*=Q^*\cap b_1^\perp$ is primitive in $Q^*$, $\det P'=\det Q\,\|x\|$, and the √3/2 projection gap is Lean
  `shortest_projection_gap` (SelectionLaw.lean:13). The ratio formula holds. The slack numbers 1.37684 / 0.72676 / 0.86627
  / 1.00140 are reproduced, and $a=(\sqrt{\gamma_{506}})^{516/505}$ is ALNS Def 4.1's η at $(n,k,q)=(1023,506,11)$.
  S2(a) was re-derived, with both forms. S2(b) and (c) are correct. The Haar mean-one level $\log T_*=547.8748$ is reproduced
  from the $K_j$ formula of Part 88.

**Issues and corrections.**

1. **Theorem B proof: step 2 is false, and the construction fails (P1) for $\beta\le368$.** In the tail every step must also
   decrease by at most ρ, or step 4 breaks. With (P4), the tail sum therefore lies in
   $[(\beta-1)\log\|u\|-\tfrac{\beta}{2}\log\gamma_\beta,\ (\beta-1)\log\|u\|]$, not in $(-\infty,\dots]$. At small β the
   head alone exceeds $511\log q$; for example at β = 12 the head sum is ≈ 4909. Checked over all four corners, the stated
   construction cannot meet (P1) for any $2\le\beta\le368$. Step 3 also checks only β = 506 (519/505 terms). **Repair.** Let
   $\ell^{\min}_i=\log\lambda_2-\rho(i-1)$ for all $i$, and let $\ell^{\max}$ be the note's head followed by a flat tail. Both
   have ℓ₁ = log λ₂, every decrement at most ρ, and satisfy (P4). (P2) and (P4) are linear, so every convex combination
   satisfies them. (P3) holds for any profile with ℓ₁ = log λ₂ and decrements at most ρ < ½log(4/3), by the same
   monotonicity argument as step 6. By the intermediate value theorem (P1) is met, provided
   $\sum\ell^{\min}\le511\log q\le\sum\ell^{\max}$. The left inequality is $(\gamma_\beta)^{(d-1)/(2(\beta-1))}\ge\lambda_2/\det^{1/d}$
   (at most 11.07 on $E$). Both inequalities and $\rho_h\le\rho$ were verified for every $2\le\beta\le566$ at all four corners.
   The minimum (P1) margin is 116.1, at β = 566. An explicit check of the convex-combination profile over all block lengths at
   β ∈ {2,…,13, 20, 50, 100, 200, 300, 368, 369, 406, 506, 566} found no violation. The single exception is a spurious
   failure at 566 when MH proxies are used for every $\gamma_l$. MH is not Mordell-monotone (its minimum ratio is at $l=12$),
   while the true constants are, so the proof's Mordell step is unaffected. **The statement of Theorem B stands.**
2. **β ≤ 11 details.** "Left side at least $2^{1015/8}$" is false for β = 10 and 11 (2.2·10³⁵ and 3.0·10³³ < 1.6·10³⁸).
   Both still exceed 17.24. The best known lattice in dimension 10 is Λ₁₀, which gives $\gamma_{10}\ge4(16\sqrt3)^{-1/5}=2.05837$,
   not 2.059. The other bounds are fine: $\gamma_9\ge2$ and $\gamma_{11}\ge2.1402\ge2.14$. Neither error affects the conclusion.
3. **S2 thresholds.** The values 953.40 and 862.08 are reproduced only if $\log\|b_1\|$ is set to $\log\sqrt{\gamma_{511}}$, a
   determinant-1 scale. But $b_1\in P$ with $\log\det P\approx\frac{511}{512}\log\det Q$, so $\|b_1\|\approx30$, not 7.9. The
   corrected values are as follows.
   * Blichfeldt bounds for both $\eta_*$ and $\|b_1\|=\lambda_1(P)\le\sqrt{\gamma_{511}}\det P^{1/511}$, solved
     self-consistently, give a **rigorous sufficient** condition $\log\det Q\ge954.34$.
   * Typical $\eta_*=G_{511}$ and $\|b_1\|=G_{512}\det Q^{1/512}$ give ≈ 862.75 **[heur]**. The note's own ρ ≈ 0.279 at 547.87
     is reproduced only under this convention.

   Upper bounds on $\eta_*$ and $\|b_1\|$ give *sufficient* conditions, so "requires" should read "suffices". ρ decreases in
   both, and no necessary threshold follows without lower bounds. The 862.08 should carry **[heur]**, in §4 and in §6(i). The
   qualitative picture is unchanged: 874.21 GH-profile **[heur]** is still between the two values, and 547.87 is far below.
4. **Heuristic scope of the "predicate ceiling".** S2(c) proves rigorously only that the densest-Q basis passes. The claim
   that this caps predicate-uniform routes near 0.28 (verdict (iii), §4, §6 "intrinsically capped") additionally needs the
   densest $Q$ of the actual $L_0$ to sit near the mean-one level. That is an *existence* (upper-tail) statement which
   Markov does not give, so it should be marked **[heur]**. "Explains" Part 96's 0.3850 / 0.5184 is too strong. Those ceilings
   are at $b=406/506$ in Part 88's normalization, while 0.279 is the own-GH ratio at $b=512$. "Consistent with" is fine.
5. **U1 scope.** Atomicity rules out density, TV and $L^2$/spectral arguments. It does not rule out weak (test-function)
   comparisons to Haar, such as the q-ary→Haar transfers used in Parts 89 and 92. The sentence "Proofs must bound the specific
   terminal event: by first moments …, by predicates, or by finite exact recursions" should allow for this.
6. **Labels.**
   * In the §2 table, "GN08 Eq. (2)" is the *rounded* factor $\gamma^{(\lceil d\rceil_\beta-\beta)/(\beta-1)}$ (exponent
     1012/505 at 506). The tabulated $(d-\beta)/(\beta-1)$ is ALNS20 Thm 1.1/Thm 4.2 only. This is harmless, since that is the
     more optimistic value.
   * ALNS20 Thm 4.2's SVP bound carries the hypothesis $\lambda_1(B_{[1,k+q]})>\lambda_1(L)$. The degenerate case is handled
     separately in Thm 1.1.
   * The note uses $k$ for the prefix rank, while ALNS uses $k$ for the block size. The verdict's "Definition 3.1, $k\ge n/2$"
     uses ALNS's $k$, and S2 uses the note's. State the mapping once.
7. **Not independently verified** (consistent with PROOF_GAP summaries, but not re-derived): Part 38's
   $(I+1)/\log_2(1/h)$, Part 46's acceptance $2^{-j(j-1)/2}$, and the Li–Walter Definition 1 text, which was checked only
   against the repo's [li_walter](wall1_li_walter.md) summary because ePrint blocked the fetch. Also not checked: whether the
   0.954 target of Part 114 transfers to the $b=512$, $L_0$ setting of S2.
