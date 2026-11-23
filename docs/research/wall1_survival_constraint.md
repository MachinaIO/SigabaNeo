# Survival of a fixed vector on the width-506 determinant path

The proposed survival test gives a pathwise stopping rule for a specified nonzero vector. It gives **no extension** of the certified $10^{-11}$ horizon. There are two separate reasons. A surviving short vector gives a *lower* bound on the later determinant, compatible with the Blichfeldt lower bound. Also, in the dominant $j=0$ term, the counted positive-height vector must **win on its arrival draw**. Freezing that winner sends it to zero. The 115 subsequent comparisons in the Part 197 example concern other directions of the same window. [Part 197, flag construction](wall1_enlarged_cutoff.md#keeping-two-directions-at-the-end-of-the-flag) · [Part 198 and audit](wall1_flag_horizon.md#audit)

| Plane area cutoff $X$ | Last certified draw $h$ | Upper bound on $\Pr(\tau_X\le h)$ | Single-draw majorant at $h+1$ |
|---|---:|---:|---:|
| $676\sqrt2$ | **164** | $8.335067\cdot10^{-13}$ | $(1.81502251,1.81502252)\cdot10^{-9}$ |
| $1352/\sqrt3$ | **171** | $5.054215\cdot10^{-12}$ | $(1.04882075,1.04882076)\cdot10^{-8}$ |

Here $\tau_X$ is the first retained state containing a saturated plane of area at most $X$, including the initial state. The last column measures where the upper-bound calculation fails. The actual hit probabilities there remain open.

## What a realized determinant path rules out

Number draws from one. Write $W_d$ for the window before the $d$th freeze, $s_d=\|w_d\|$ for its winning length, and $D_d$ for the retained covolume after the freeze. Then $D_0=3329^{400}$ and $s_d=D_{d-1}/D_d$. Given $v_i\in W_i$ of length at most $R$, write $v_{d+1}$ for its projection off $w_d$, embedded at height zero in the next window. The append and coordinate isometries preserve its norm. For $\rho_d=\|v_d\|$ and $e_d=w_d/s_d$,
$$
 \rho_{d+1}^2=\rho_d^2-|\langle v_d,e_d\rangle|^2,
 \qquad v_d\ne0\ \Longrightarrow\ s_d\le\rho_d .
$$
Hence if the image is nonzero entering every draw from $i$ through $t$, then for **every** $i\le d\le t$,
$$
 R^2\ \ge\ \left(\frac{D_{d-1}}{D_d}\right)^2+
           \sum_{u=i}^{d-1}|\langle v_u,e_u\rangle|^2.                 \tag{1}
$$
In particular its last possible nonzero entrance precedes the first draw with $D_{d-1}/D_d>R$. Equality permits ties. The test also covers selection on the final draw tested. Multiplication yields
$$
 \left(\frac{D_{i-1}}{D_t}\right)^{1/(t-i+1)}
 \le \max_{i\le d\le t}s_d\le R,\qquad
 D_t\ge\frac{D_{i-1}}{\prod_{d=i}^{t}\rho_d}
      \ge\frac{D_{i-1}}{R^{t-i+1}}.                                  \tag{2}
$$
These are necessary tests on the *realized* path. They follow directly from global shortestness in each window and orthogonal projection. [Part 108 transition](wall1_first_tour.md#transition-and-loss-of-randomness) · [Lean restart path](../../SigabaNeo/Lib/Lattices/Research/Wall1/TerminalRestartPath.lean) · [Lean freeze and covolume](../../SigabaNeo/Lib/Lattices/Research/Wall1/TerminalChainState.lean)

Part 183 supplies $D_t\ge\exp L_t$. Together the two estimates give $D_t\ge\max(\exp L_t,D_{i-1}/R^{t-i+1})$. A contradiction from (2) would require an **upper** bound on $D_t$ below the second entry, or an observed ratio in (1) that is too large. The GH floor $(\exp L_t/V_{506})^{1/506}$ bounds a determinant scale from below. It supplies no lower bound on an individual winning length. Part 198's restricted moment of $1/D_{i-1}$ is evaluated before column $i$ is read. Replacing that denominator by a future, survival-conditioned determinant changes the conditional count. [Part 183 floor](wall1_terminal_tail_047.md#conditional-count-at-a-fixed-physical-radius) · [Part 198 determinant moment](wall1_flag_horizon.md#a-moment-bound-for-the-realized-determinant)

**Counterexample in the support of the specified restart.** Take one of the 105 initial graph columns to be zero and all other initial columns to have residue equal to the first horizontal unit vector. Take the first suffix residue to be the second horizontal unit vector. Its graph vector $v$ has norm $\sqrt2$. In this integer window the only unit line is the input axis of the zero column. Indeed, a horizontal unit fails the graph congruence, and a unit input axis belongs precisely for a zero column. Freezing this line simply deletes its orthogonal coordinate. Take all remaining suffix residues to be zero. Inductively the newly appended input axis is the unique unit line, and each freeze deletes it. Thus $v$ survives all 406 freezes at its original length, $s_d=1$, and $D_d=3329^{400}$ throughout. This disproves a uniform lifetime shorter than the tour even for a fresh vector of length $\sqrt2$. The example concerns the unconditional pathwise implication. It gives no estimate of first-hit mass on the raw and dual good event.

## Which vector the radial sum counts

Fix a hit at $h$ and its lifted flag, let $i$ be the last suffix coordinate used anywhere in the flag, and put $k=h-i+1+b$ for terminal rank $b$. The index $j$ counts winners starting at $i$ **before the first use of coordinate $i$**. For $j=0$, the first flag member using it is $w_i$ itself. A radial candidate $y$ counted at draw $i$ can realize this term only if $y=\pm w_i$, after orienting the sign. On that event $P_{w_i^\perp}y=0$. Applying shortestness to this zero vector at $i+1$ would assert $s_{i+1}\le0$.

What survives is the rank-$(k-1)$ quotient of the lifted flag by the winning line. The next $h-i$ winners must come from successive projections of the draw-$i$ window and win against all competitors available at their respective draws. One can follow a lift of a *terminal* vector through these projections using (1), but its short terminal image gives a **lower** bound on the length of its earlier lift. It does not place that lift inside the terminal ball at draw $i$. The KZ determinant and length caps of Part 198 already use the shortestness tests internal to this flag. The weight still missing from the radial relaxation is the conditional probability that the specified line wins and that the remaining projected flag is selected in the subsequent windows. [Part 198, within one window](wall1_flag_horizon.md#within-one-window) · [Part 197, selected incidence count](wall1_enlarged_cutoff.md#raw-configurations-and-membership-conditioning)

## How much removing every $j=0$ term could buy

As a diagnostic, set every $j=0$ term of Part 198 equation (5) to zero on draws $155$ onward, retaining the raw terms, all $j\ge1$ terms, and the original $5.412\cdot10^{-36}$ prefix charge through 154. This deletion has **no probability justification**. It measures the best possible improvement to that sum from modifying only $j=0$.

| Cutoff | Last draw under budget after hypothetical deletion | Remaining cumulative sum there | Remaining cumulative sum one draw later |
|---|---:|---:|---:|
| $676\sqrt2$ | 165 | $(8.14486062,8.14486063)\cdot10^{-12}$ | $(1.77280926,1.77280927)\cdot10^{-8}$ |
| $1352/\sqrt3$ | 171 | $(2.38455504,2.38455505)\cdot10^{-14}$ | $(4.98851661,4.98851662)\cdot10^{-11}$ |

A single **$j=1$** term gives the same obstruction at draw 406 on a much larger scale. For $X=676\sqrt2$ use $(b,i,j)=(2,289,1)$, and for $1352/\sqrt3$ use $(2,288,1)$. Their base-ten logarithms lie in $(629.259595,629.259596)$ and $(608.214538,608.214539)$, respectively. The corresponding radii are below 1515 and 1390, both below the modulus. These are individual terms of the radial expression. Other caps exceed the modulus by this horizon, precluding the all-terms justification of (5). Even exact elimination of its entire $j=0$ branch would leave a loss exceeding 600 orders of magnitude.

**Numerical verification.** Scratch evaluation reran Part 198's 224-bit outward-interval audit calculation with its Part 77 and 82 cap inputs. For each draw it accumulated $Q$ and its $j=0$ subsum $Q_0$, added $Q$ or $Q-Q_0$ to the respective prefix, and rounded the final interval endpoints outward. For the individual $j=1$ checks the expression was $V_{505}(u^2+(505+i)/4)^{505/2}C_k\exp(-\ell_{i-1})$ with $u=\max(C_{k-1},K_b)$. All prefix radii were checked below $q$ through the two crossings. [Part 198 formula and cap inputs](wall1_flag_horizon.md#reproducing-the-certificates)

**Exact small checks.** Over $q=5$ the graph $x\equiv z\pmod5$ in integer coordinates $(x,y,z)$ has only $(0,\pm1,0)$ on the unit sphere, while the incoming $(1,0,1)$ survives their projection. With two old modulus axes and incoming residue $(1,0)$, the congruences become $x\equiv z,\ y\equiv0\pmod5$. The only nonzero points of squared length at most two are $\pm(1,0,1)$, both killed by the first freeze. Both enumerations fit in $\{-1,0,1\}^3$. A separate exact-rational width-two check started at $3\mathbb Z$, enumerated all $3^4$ residue sequences and every minimizing line at each tie, and followed each incoming graph vector until its projection vanished. The squared pointwise and product tests in (1)–(2) passed at all 222 comparisons. In the append basis, if $(u,v)$ is the primitive winner, a vector $(a,b)$ projects to coefficient $ub-va$ in a suitably oriented basis of length $D/s$. This permits the entire check with rational squared lengths.

## Consequences for the residuals

At the original cutoff, the part of $Z_1$ whose first hit is through draw 170 is bounded by $2.413\cdot10^{-15}$, or through draw 171 by $5.055\cdot10^{-12}$, directly from Part 198. These are alternative prefix charges. The established residual estimates are
$$
 Z_1 < p_{\rm old}+p_{\rm late}+1.3670\cdot10^{-11},
 \qquad 0\le Z_2-Z_{\rm rem}<2.515\cdot10^{-11}.
$$
Here $p_{\rm old}$ covers the wholly old horizontal first hits, $p_{\rm late}$ the remaining mixed horizontal cases on draws 403–406, and $Z_{\rm rem}$ the surviving vertical cases on draws 396–406 with eligible height and length. The fixed-vector test supplies no additional upper bound on those three masses. The $10^{-11}$ horizon through draw 406 and the proposed residual allocations remain **conjectural**. The survival inequality, counterexample, and numerical diagnostics above are paper results. [Horizontal residual](wall1_z1_horizontal.md#audit) · [Vertical residual](wall1_z2_vertical.md#audit) · [Part 192 decomposition](wall1_rank2_tail.md#audit) · [Lean controlled charges](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledPlaneCharges.lean) · [Lean terminal discrepancy](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConcreteTerminal506.lean)

## Audit

**Verdict — SOUND.** Equations (1) and (2) hold whenever the tracked image enters each of draws $i,\ldots,t$ nonzero, including when it wins at $t$. Shortestness gives $s_d\le\rho_d\le R$, and $\prod_{d=i}^t s_d=D_{i-1}/D_t$. Thus survival imposes a lower bound on $D_t$, compatible with the Part 183 floor. In the width-506 example the initial freeze deletes the sole zero-column axis. The retained graph has 104 columns with residue $e_1$ and one with residue $e_2$, so it has no unit vector. Each subsequent zero append supplies the unique unit line and its deletion restores that same graph. The vector from the $e_2$ column remains of length $\sqrt2$ after freeze 406. This positive-probability history already violates the raw good event at initialization.

For $j=0$ the first use of coordinate $i$ is by the winner at $i$. Its two signed representatives project to zero. For the Part 197 term at $i=47,h=162$, the 115 later comparisons select successive directions in the quotient. A bound on the lifetime of the first vector cannot charge any of those comparisons. [Part 197 term](wall1_enlarged_cutoff.md#keeping-two-directions-at-the-end-of-the-flag) · [Part 198 audit](wall1_flag_horizon.md#audit)

An independent 192-bit outward-interval calculation used the Part 77 and 82 tables, the Part 198 determinant moment, and the $5.412\cdot10^{-36}$ prefix charge. Summing the raw terms and the positive $j\ge1$ terms directly reproduced all four cumulative enclosures in the deletion table. The hypothetical crossing moves from 165 to 166 at $676\sqrt2$ and stays at 172 at $1352/\sqrt3$. At draw 406 the respective $j=1$ terms have radii in $(1514.84555,1514.84556)$ and $(1389.57564,1389.57565)$, and base-ten logarithms in $(629.25959509,629.25959510)$ and $(608.21453830,608.21453831)$. Both individual height tests are below 3329. These are lower bounds on terms of the radial expression. The selected first-hit probability and the Part 192 residual allocations remain open.

**Source rounding.** The Part 198 summary in PROOF_GAP.md rounds the two full prefix majorants downward. The independently computed totals lie in $(8.33506617,8.33506619)\cdot10^{-13}$ and $(5.05421448,5.05421450)\cdot10^{-12}$. The opening table here rounds both upper endpoints outward correctly. [Part 198 summary](../PROOF_GAP.md) · [Part 198 detailed enclosures](wall1_flag_horizon.md#audit)
