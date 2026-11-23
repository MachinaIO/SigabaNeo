# A raw-good delayed plane at width 506

**The raw-good dichotomy is false.** In the Part 108 restart there exists a reachable raw prefix through draw 288 with the following properties. Write $R$ for absence of a nonzero raw vector of norm **at most** 250 in the 511-column graph and $F$ for survival of the entire designated 118-step old flag. For both cutoffs $X=1352/\sqrt3,676\sqrt2$, the first retained-plane hit satisfies
$$
                 265\le\tau_X\le278.
$$
On $F$ the terminal lattice has a saturated old square of area 677 and minimum $\sqrt{677}>26$. Under the uniform unread columns, conditional on this fixed prefix,
$$
 \Pr(R)>1-4.249\cdot10^{-12},\qquad
 \Pr(F\mid R)>1-10^{-126},\qquad
 \Pr(F\cap R)>1-4.250\cdot10^{-12}.
$$
Thus even among raw-good completions the competitor tests can exclude less than one part in $10^{126}$. The required early hits through 164 or 171 are absent. The result concerns a prefix-uniform divisor. Its proof constructs a prefix of positive probability without estimating its weight in the residual. [Part 198 horizons](wall1_flag_horizon.md#audit) · [Part 201 old flags](wall1_multistep_branch.md#audit) · [Parts 202–203](wall1_delayed_plane_survival.md#audit)

**The dual gate separates this example from the residuals.** Every member of the constructed family fails the Part 172 raw dual floor at draw 156. Also, the first hit occurs at a positive-height win before draw 395. The family contributes zero to both gated residuals. The proposed bounds on the joint good event remain conjectural. [Part 192 residual](wall1_rank2_tail.md#audit) · [Lean definitions of the gates](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledPlaneTail.lean)

## A family of prefixes

Use $x=Ay\pmod q$, $q=3329$. Each input has its own unit height. Partition the 400 horizontal rows into sets $B,E,P,J,U$ of sizes $36,108,108,12,136$. The following finite auxiliary distribution chooses a prefix. All entries called uniform are mutually independent, and unspecified entries are zero. Each outcome is a possible prefix of the original independent-column law.

| Inputs | Columns |
|---|---|
| Initial 105 | Split $B$ into twelve triples. Give each triple one column with coefficients $(7,49,343)$ on that triple. The other 93 columns are uniform on all 400 rows. |
| Draws 1–48 | Append 48 columns uniform on all 400 rows. Call these and the preceding 93 uniform columns the **core**. |
| Draws 49–156 | Once per $E$ row, append coefficient 57 on that row and uniform entries on $B$. |
| Draws 157–264 | Once per $P$ row, append coefficient 26 on that row and uniform entries on $B\cup J$. Call these the **stored columns**. |
| Draws 265–276 | Once per $J$ row, append coefficient 20 on that row and uniform entries on $B\cup E$. |
| Draws 277–288 | In the same order, use 220 on each $J$ row and fresh uniform entries on $B\cup E$. |

The uniform entries on $B$, and later on $E$, protect the raw graph. Their coordinate directions have been completely frozen by the time these entries need to be invisible to the selector. The labels on $J$ keep the stored columns long until after draw 264.

## Three tests for the projected comparisons

Select a prefix passing the following tests as well as the raw test below. Write $V_d$ for unit ball volume. For a random $r$-row core matrix $C$, a nonzero core tuple $y$ of norm below $q$ has uniform image. The chance of a nonzero such tuple with $x=Cy\pmod q$ and $\|(x,y)\|\le T$ is at most $V_d(T+\sqrt d/2)^d/q^r$, by covering the integer points with unit cubes. The test can use all 141 core heights before they are read, by zero-padding. It is an existence test in the auxiliary distribution.

1. On the 364 rows outside $B$, exclude core tuples of length at most 506 in these joint coordinates. The base-ten logarithm of the bound is in $(-285,-284)$, with $d=505$.
2. On $U$, exclude core tuples of length at most 59 in the joint coordinates. The logarithm is in $(-142,-141)$, with $d=277$. All noncore columns vanish on $U$, and the prescribed projections leave both $U$ and the core input axes intact.
3. In the stored columns on $P\cup J$ and their height axes, exclude vectors of length at most 59 with nonzero stored tuple $b$. For $|b_j|\le59$, the private displacement $26b_j$ is centered. Thus $677\|b\|^2\le59^2$ implies $\|b\|_1\le\|b\|^2\le5$. There are at most $217^5$ possible tuples, by recording five signed unit steps or zeros. For each nonzero tuple the 12 shared residues are uniform. The failure bound $217^5(119/q)^{12}$ has logarithm in $(-5.70,-5.67)$.

**Through draw 48.** Each initial triple and its height form a rank-four graph block of determinant $q^3$. The centered vectors of heights $1,68,476,10$ have squared lengths $120100,231650,248635,255301$ and absolute determinant $q^3$. These four vectors span, and every length is below 506. At every successive projection of this block the surviving images span and have lengths below 506. Every nonzero projected vector has length at least $q^3/506^3>284$. Indeed, take a lift, adjoin the earlier frozen lifts, and complete to four independent vectors using the spanning set. The absolute determinant is at least $q^3$. Gram–Schmidt in this order bounds each of the three other factors by 506. Test 1 and the other horizontal periods $q$ therefore force the first 48 winners to exhaust these twelve blocks. Ties between blocks may be taken in any order. In particular the bootstrap blocks already pass the closed raw cutoff.

**Through draw 264.** After the 48 freezes, each 57-column has only its separate $E$ coordinate and height. Its signed height-one pair wins and leaves period $L_E=q/\sqrt{3250}$, strictly between 58 and 59. During the next 108 draws each winner is an intact $E$ period. Test 2 excludes any core input and test 3 excludes any stored input within 59. Freezing the period after its pivot deletes the entire original row and its appended input direction. Thus every retained minimum through draw 264 exceeds 36, including draw zero. A reduced basis in any rank-two sublattice then gives area greater than $36^2\sqrt3/2>676\sqrt2$.

**Through draw 288.** Both rounds on $J$ have height-one winners. The first has squared length 401. Its row period becomes $q/\sqrt{401}$. The second has squared length $48801/401$ and leaves period $L_J=q/\sqrt{48801}$ between 15 and 16. Each completed period is longer than the second-round pivot. Any candidate with a stored input within the pivot radius pays at least $\sqrt{677}$ on its private row and height. Test 2 still excludes the core. For all three kinds of height-one pivots the exact local check minimizes $nt^2+c_q(mt)^2$ at positive integer heights $t\le\lfloor\sqrt{1+m^2/n}\rfloor$, where $c_q$ centers the residue. For $(m,n)=(57,1),(20,1),(220,401)$, the unique minima are $3250,401,48801$, each at $t=1$. The horizontal period also loses each comparison. Projection in the row and new height changes the period from $q/\sqrt n$ to $q/\sqrt{n+m^2}$ by area divided by winning length. At draw 278 two completed periods give area $L_J^2<256$. Saturation can only decrease it. This proves the stated first-hit interval, including for prefixes where an earlier shared-row pivot creates a plane.

## Existence with a raw minimum above 250

The raw test must cover cancellations between columns, including multiples and different column types. A raw vector with any nonzero core coefficient of absolute value at most 250 imposes 400 independent uniform equations, after all noncore columns are fixed. The same signed integer-ball count as for the full 911-coordinate raw exit bounds its probability by $4.249\cdot10^{-12}$. One can zero-pad the unused future coordinates into that ball. [Part 183 raw count](wall1_terminal_tail_047.md) · [Definition of rawShort and radius-250 bound](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledRawBall.lean)

For zero core tuple, use the following finite positive sums at rate $v>0$. In each sum include just the integer arguments with the displayed energy $e\le62500$, weighted by $\exp(-ve)$.

| Sum | Energy |
|---|---|
| $A$ | $t^2$ |
| $P_{57}$ | $t^2+c_q(57t)^2$ |
| $S_{26}$ | $t^2+c_q(26t)^2$ |
| $H$ | $t^2+u^2+c_q(20t+220u)^2$ |

Call the last 24 inputs the helpers. Each row in the table below bounds the probability of any eligible raw member in that class by $e^{62500v}$ times the factor shown. A centered representative is necessary within radius 250. An unconstrained integer coordinate contributes $A$.

| Nonzero input class | Factor | $v$ | Outward interval for $\log_{10}$ bound |
|---|---|---:|---:|
| Some 57-input, no stored or helper input | $A^{48}P_{57}^{108}/q^{36}$ | .001 | $(-9.68,-9.66)$ |
| Some stored input, no helper | $A^{60}(P_{57}S_{26})^{108}/q^{48}$ | .0015 | $(-1.18,-1.16)$ |
| Some helper, zero stored tuple | $A^{264}H^{12}/q^{144}$ | .002 | $(-15.79,-15.76)$ |
| Some helper and some stored input | $A^{300}S_{26}^{108}/q^{156}$ | .003 | $(-4.11,-4.08)$ |

For the first class the 36 bootstrap rows are uniform for each eligible input tuple. Their horizontal coordinates and the 12 bootstrap inputs give the exponent 48. In the second class the 12 shared rows are uniform as well. In the third class the helper tuple makes all 144 rows of $B\cup E$ uniform. The 12 bootstrap inputs and 108 inputs of the 57-columns are now free, giving $144+12+108=264$. In the last class the stored tuple makes the shared rows independently uniform as well, and the 24 helper heights are free. The private rows still enforce $S_{26}$. Nonzero eligible tuples stay nonzero modulo $q$. The factorization relaxes the nonzero restrictions only **after** applying the indicated membership probability to eligible tuples. With just bootstrap inputs, the determinant argument above excludes every short nonzero member. Pure horizontal vectors have minimum $q$.

The four bounds, the core raw exit and the three comparison-test failures sum to less than 0.07. Hence some prefix passes them all. This is a finite existence proof for a reachable prefix under the original law.

## The last 118 comparisons

Run the signed selector on the old lattice alone. First it removes the twelve $J$ periods. Test 2 and the private stored coordinates exclude any shorter mixed input. The only noncore, nonstored directions on the shared rows are the orthogonal periods. Their removal deletes each shared row together with its two helper height axes. The stored columns now project to the mutually orthogonal vectors $26e_j+f_j$, where $e_j$ is private and $f_j$ its stored height. The next 106 winners are distinct such lines. Indeed the shortest in each intact private factor is its stored line, by centering at every height of absolute value at most 27. Once it is removed its remaining period is $q/\sqrt{677}>27$. Two stored lines remain after draw 406. Their square is saturated in the old section because the two untouched height coordinates read off the coefficients of every lattice point in their span. It stays saturated on full-flag survival since the fresh heights then project onto $\mathbb Z^{118}$ with old section as kernel.

Before any first disagreement, the 136 unused rows, 141 core input axes and all fresh heights are untouched. Every fresh competitor, including a tie, therefore has integer coordinates $(x,y,b)$ on these axes with norm at most $\sqrt{677}<28$, satisfying
$$
                 x=C_Uy+Vb\pmod q,\qquad b\ne0 .
$$
Zero-pad $b$ through position 118. The unread matrix $V$ on $U$ is uniform conditional on the fixed prefix, so each such tuple costs $q^{-136}$. All stages fit inside a single 395-dimensional ball. The common failure bound
$$
       \Pr(F^c)\le V_{395}(28+\sqrt{395}/2)^{395}/q^{136}
                   <10^{-126.26}
$$
uses the original unread law, before conditioning on any earlier success. Likewise any raw-short completion must use some fresh coefficient because the fixed prefix passed the raw test. Each fixed such vector costs $q^{-400}$ on the full unread columns. The full raw-ball bound applies again. Dividing the flag failure bound by $\Pr(R)$ gives the conditional assertion in the introduction. Averaging under the law conditioned on $R$ also gives a draw-289 prefix with conditional survival above $1-10^{-126}$ for the remaining 117 old comparisons. To see this, average the indicator of the *entire* 118-step success first. A prefix with positive conditional success already passed its first comparison, and the successful remaining winners restrict to the designated old winners at that enlarged prefix.

## Determinant, compression and the dual obstruction

The winner-length products through draws 48, 264 and 288 are respectively $q^{36},q^{144},q^{144}48801^6$. The old tail adds $(q/\sqrt{48801})^{12}677^{53}$. Since every appended height is one, the realized determinants are $D_{288}=q^{256}/48801^6$ and, on survival, $D_{406}=q^{244}/677^{53}$. Each plane has its usual rank-three pullback through a winning line of length $s$, with pullback covolume $s$ times the plane area. Thus the construction obeys the retained Rankin inequality. On $R$ every raw lift of a surviving stored generator loses strictly more than $1-677/62500=0.989168$ of its squared length. Its protection can lie in coordinates already frozen before the late marks are drawn. The terminal square and the near-unit conditional survival coexist with this loss. Part 183's precise $0.989184$ uses projected radius 26. [RankinWindow](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean) · [Part 184 compression identity](wall1_penultimate_projection.md#audit)

At draw 156 restrict the horizontal coordinates of the scaled raw dual $qL^*$ to the 256 rows outside $B\cup E$. Every noncore column already read vanishes there. For arbitrary horizontal vector $a\in\mathbb Z^{256}$, take integer core coordinates congruent to $-C^\top a$ and set the noncore coordinates to zero. This section has rank 397 and determinant $q^{141}$ in its orthonormal coordinate space. Blichfeldt's Hermite bound supplies a nonzero point of length at most
$$
 \sqrt{2/\pi}\,\Gamma(2+397/2)^{1/397}q^{141/397}<125.
$$
Part 172's scaled floor $qR_0(156)$ is greater than 138. Hence the raw dual exit is forced, irrespective of all random labels and all later columns. The unconditional exit allowance $8.147\cdot10^{-14}$ also bounds the original-law mass of this entire family. [Part 172 radii](wall1_transference.md#sharpening-the-exit-in-theorem-c) · [Blichfeldt bound, equation (22)](https://www.dpmms.cam.ac.uk/~taf1000/papers/n-descent-III.pdf)

**Remaining conjectures.** Conditioning on both gates may still change the pointwise conclusion. For the weighted residuals the outstanding ceilings are $Z_{2,\mathrm{rem}}\le6.485\cdot10^{-11}$ and $p_{\rm old}+p_{\rm late}\le7.633\cdot10^{-11}$. This construction settles the obstruction using the raw gate alone. [Vertical residual](wall1_z2_vertical.md#audit) · [Horizontal residual](wall1_z1_horizontal.md#audit)

**Numerical verification.** Scratch checks used 65-decimal-digit outward interval arithmetic, $V_0=1,V_1=2,V_d=2\pi V_{d-2}/d$, and exact integer histograms of the four energies, enumerating $-250\le t,u\le250$ and discarding energies above 62500. The scaled dual cap and floor lie in $(124,125)$ and $(138,139)$. Integer checks verified the rank-four determinant, the four squared lengths, and the unique positive minimizer at every prescribed row pivot. The new existence and probability results are paper proofs.

## Audit

**Verdict — SOUND.** There exists a reachable draw-288 prefix for which both first hits lie in $[265,278]$ and the entire old flag survives through draw 406 with probability greater than $1-10^{-126}$ conditional on that prefix and $R$. The two cutoffs may have different first-hit draws. The first-hit and survival assertions use a prefix passing the tests. The dual exit holds for every labeling in the auxiliary distribution.

**Existence and first hits.** Independent integer enumeration gives absolute determinant $3329^3$ for the four bootstrap generators and reproduces all four squared lengths. Within each unfinished block the three complementary Gram–Schmidt lengths are at most 506, giving the stated lower bound on the fourth factor. The untouched core coordinates enforce Test 1 throughout those projections. After the bootstrap, exact enumeration of the centered residues gives a unique positive minimizing height of one for each prescribed row pivot. The intact $E$ periods then win while the stored columns enter, since their lengths are below 59 and Tests 2 and 3 exclude every competing vector with a core or stored input in that radius. Through draw 264 the retained minimum exceeds 36, which excludes both plane cutoffs. At draw 278 the first two completed $J$ periods span a square of area $3329^2/48801<227.10$, already below both cutoffs before saturation. Every intervening winner has absolute newest height one.

**Raw cancellations and reachability.** For a fixed eligible integer tuple the independent uniform row counts in the four zero-core classes are $36,48,144,156$. In the last class the helper coefficients randomize $B\cup E$ even after the stored labels there are fixed, and the stored coefficients independently randomize $J$. Thus the row probabilities multiply before the tuple restrictions are relaxed. I recomputed the finite energy sums from integer histograms and the ball volumes from factorial formulas with 55-decimal-digit interval arithmetic. The four base-ten logarithms are respectively in $(-9.672,-9.671)$, $(-1.167,-1.166)$, $(-15.777,-15.776)$ and $(-4.095,-4.094)$. Including all three comparison tests and the signed core raw-ball bound gives a union bound in $(0.06821062,0.06821064)$. A passing prefix therefore exists in the finite support, and each such fixed prefix has positive probability in the restart.

**Old flag and conditioning.** The twelve $J$ periods win first. Thereafter an intact stored line has length $\sqrt{677}$, and a used private row has remaining period $3329/\sqrt{677}>27$. The 106 subsequent choices leave two of the 108 orthogonal stored lines. Their untouched integral heights recover the two coefficients in their real span, proving saturation in the old section. On flag survival a point in that span has all 118 fresh heights zero, proving saturation in the full output as well. The resulting square has area 677. These lengths also reproduce $D_{288}=q^{256}/48801^6$ and $D_{406}=q^{244}/677^{53}$ on survival.

At first disagreement, the 136 unused rows, 141 core heights and 118 zero-padded fresh heights give one common 395-coordinate test including ties. For each tuple the nonzero fresh coefficient vector makes the unread congruence cost $q^{-136}$ under the fixed-prefix law. The independent ball calculation gives $\log_{10}$ of the failure majorant in $(-126.265,-126.264)$. For the same prefix every short raw completion uses a fresh coefficient. Its signed 911-coordinate majorant is below $4.248599\cdot10^{-12}$. Division by the resulting lower bound on $\Pr(R)$ gives $\Pr(F^c\mid R)<5.436\cdot10^{-127}$. A union bound gives the stated joint probability. Averaging the whole-flag indicator under this conditional law also proves the draw-289 existence assertion. [Part 201, old flags](wall1_multistep_branch.md#audit)

**Dual gate and residuals.** At draw 156 the 141 core congruences impose index $q^{141}$ in the 397-coordinate section because each has its own unrestricted integer core coordinate. The scaled Blichfeldt cap lies in $(124.2693,124.2694)$, while the scaled Part 172 floor at raw dimension $400+105+156=661$ lies in $(138.0462,138.0463)$. Consequently the full auxiliary family lies in the dual exit, whose original-law mass is below $8.147\cdot10^{-14}$. Independently, on each passing prefix the first hit is a positive-height win by draw 278, outside both Part 192 residual strata. The contribution to $Z_1$ and $Z_2$ is zero. The prefix-weighted bound under the joint raw and dual gates remains open. [Part 172, dual radii](wall1_transference.md#sharpening-the-exit-in-theorem-c) · [Part 192, residual definitions](wall1_rank2_tail.md#audit)
