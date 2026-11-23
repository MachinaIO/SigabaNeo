# What the raw and dual gates force on a late plane

**The gated early-hit dichotomy remains open.** On every doubly-gated draw-406 history, the orthogonal projection of the raw lattice onto any rational plane contains the raw section in that plane with index at least **1,893**. For a retained hit, the hit plane itself is an intermediate lattice in this inclusion. The index measures the denominators of projected vectors. The exclusion divisor in Part 202 measures the fraction of unread marks for which the old winners survive. The two quantities need a further argument to relate them.

There is a stronger conclusion for the construction in Part 204. Its whole family already fails the dual gate by draw **120**. At draw 156, even replacing the defining zero rectangle by an arbitrary matrix of rank at most seven still forces dual exit. More generally, under the original law, the mass of histories with *any* rank-deficient 256-by-120 coordinate rectangle through draw 406 is less than $10^{-250}$. This pays for that class in either weighted residual, including histories where both gates pass. [Part 204 construction and audit](wall1_rawgood_dichotomy.md#audit) · [Part 202 exclusion law](wall1_joint_exclusion_scale.md#which-probability-multiplies)

## The two gates on one subspace

At draw $t\le406$, put $n=105+t$, $q=3329$, and let $L=\{(x,y)\in\mathbb Z^{400+n}:x=Ay\bmod q\}$. On the good event $G$, every nonzero member of $L$ has length greater than 250 by zero extension to the 511-column graph. The raw dual has minimum at least $R=R_0(t)$. Each retained state inherits this floor. Persistence transports a previously established floor through later appends and projections. The larger value $R_0(t)$ at a later draw comes from its own raw-prefix gate. The certified simultaneous exit allowance over 408 indices is $8.147\cdot10^{-14}$. [Raw and dual gates](wall1_penultimate_projection.md) · [DualMinimumExit408.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/DualMinimumExit408.lean) · [AppendDual.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/AppendDual.lean) · [Part 172 audit](wall1_transference.md#audit)

Let $T$ be any rational $d$-dimensional subspace of the raw Euclidean space, $d\ge1$. Write $B=L\cap T$, $C=\pi_T L$, and $g_d\ge\gamma_d$ for an upper bound on the Hermite constant. Then
$$
 I_T=[C:B]=\det(B)\det(L^*\cap T)>
              (250 R/g_d)^d.                                      \tag{1}
$$
Indeed $B$ and $C$ have full rank in $T$, and $C^*=L^*\cap T$ because pairing a vector in $T$ with a projection gives its pairing with the original vector. Apply Hermite separately to $B$ and $C^*$, multiply the two determinant lower bounds, and use $\det C\det C^*=1$. Equality $I_T=1$ is equivalent to an orthogonal splitting of $L$ along $T$, since $\pi_T L\subset L$ then lets one subtract the projected component from every raw vector. This argument works for a subspace chosen after observing all the winners. [Projection and section duality](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectionDual.lean)

At 406, $R\in(0.20090915,0.20090916)$. With the Part 77 dimensionwise caps, (1) forbids any orthogonal summand of ranks 1 through 447. For the actual span of the 406 frozen directions it gives $\log_q I_T>4.5528$. These statements use the *raw* lattice of rank 911. They do not prohibit an orthogonal splitting after projection. [Part 77 cap integers](wall1_lcz_all_widths.md#all-dimensions)

For a saturated retained plane, let $E$ be the orthogonal complement of the frozen directions and $T\subset E$ the real span of the plane. The plane lattice is $P=(\pi_E L)\cap T$. All these spaces are rational since each projection is off a rational line. Then
$$
       B\subset P\subset C,\qquad
       I_T=[C:P][P:B].
$$
The second inclusion follows by projecting any raw lift of a member of $P$ onto $T$. If $A_P=\det P$, the two factors obey
$$
 [P:B]>\frac{250^2}{\gamma_2 A_P},\qquad
 [C:P]\ge\frac{A_P R^2}{\gamma_2},\qquad \gamma_2=2/\sqrt3.       \tag{2}
$$
The first inequality forces $[P:B]\ge70$ at the original cutoff $1352/\sqrt3$ and $[P:B]\ge57$ at $676\sqrt2$. For instance, the order of a shortest plane vector $p$ in $P/B$ must itself exceed $250/\|p\|$, since that order times $p$ is a nonzero raw vector. Multiplying (2) cancels the unknown area and gives $I_T>1892.0854$ at 406. The lower bound on $[C:P]$ retains the actual $A_P$ in its numerator. Substituting an upper cutoff there could overstate the bound.

The rank-503 complementary section gives a separate necessary condition $A_P\ge D_t(R/\sqrt{g_{503}})^{503}$, where $D_t=\det(\pi_E L)$. Equation (2) uses the dual section *in* the plane and retains the raw minimum. In particular the same-plane product in (1) holds even for rational planes never encountered by the selector. [Part 172, Proposition 1](wall1_transference.md#a-deterministic-area-floor-and-a-witness-count)

## A rank test on coordinate sections

Choose $r$ horizontal rows $I$ and $c$ input axes $J$. Take $T$ supported on $I\cup J$, $d=r+c>0$, and write
$$
   u=\operatorname{rank}_{\mathbb F_q}A_{I^c,J},\qquad
   v=\operatorname{rank}_{\mathbb F_q}A_{I,J^c}.
$$
The two section determinants in orthonormal coordinates are
$$
 \det(L\cap T)=q^{r+u},\qquad \det(qL^*\cap T)=q^{c+v}.
$$
In the primal section, $x_I=A_{I,J}y_J$ gives $r$ independent congruences using the free $x_I$, and $A_{I^c,J}y_J=0$ gives $u$ more. In the scaled dual, $b_J=-A_{I,J}^{\mathsf T}a_I$ and $A_{I,J^c}^{\mathsf T}a_I=0$ give $c+v$ independent congruences. This proves the formulas by reducing modulo $q$. Consequently $I_T=q^{u+v}$. The individual gates require
$$
 r+u>d\log_q(250/\sqrt{g_d}),\qquad
 c+v\ge d\log_q(qR_0(t)/\sqrt{g_d}).                             \tag{3}
$$

In Part 204, for $48\le t\le156$ take $I$ to be the rows outside the 36 bootstrap rows and outside the $t-48$ processed $E$ rows. Take $J$ to be the 141 core inputs. Thus $r=364-(t-48)$, $c=141$, and $v=0$. The following intervals enclose the lower threshold for $v$ in (3). Each row allows arbitrary other three blocks of the matrix, including the core labels.

| Cap | Draw | Rows $r$ | Required lower threshold for $v$ |
|---|---:|---:|---:|
| Blichfeldt | 128 | 284 | $(-0.01203,-0.01202)$ |
| Blichfeldt | 129 | 283 | $(0.23075,0.23076)$ |
| Blichfeldt | 156 | 256 | $(5.14638,5.14639)$ |
| Part 77 | 119 | 293 | $(-0.21911,-0.21910)$ |
| Part 77 | 120 | 292 | $(0.05983,0.05984)$ |
| Part 77 | 156 | 256 | $(7.08334,7.08335)$ |

Thus the original zero block forces a dual exit at draw 120 regardless of subsequent winners or columns. At 156, the block on $I\times J^c$ has shape $256\times120$. A modification of rank at most seven on that block still fails the gate. Larger rank only passes this particular obstruction. The earlier draw-120 assertion also applies if the zero block at that draw is preserved.

## Probability of a deficient rectangle

For fixed sets of 256 rows and 120 columns, rank deficiency means that some line in $\mathbb F_q^{120}$ lies in the right kernel. Each fixed line has probability $q^{-256}$, using independence across rows. Hence under the marginal restart, the chance that *some* such rectangle among the first $n$ inputs is deficient is at most
$$
 U(n)=\binom{400}{256}\binom n{120}\frac{q^{120}-1}{q-1}q^{-256}.
$$
The base-ten logarithms for $n=261$ and $n=511$ lie respectively in $(-293.533,-293.532)$ and $(-250.849,-250.848)$. Taking $n=511$ once includes every prefix through draw 406 and allows both coordinate sets to depend on the realized history. Every residual intersected with this exceptional event has joint mass at most $U(511)$. This estimate concerns rank deficiency over the field. A full-rank matrix with small centered entries, or a rational subspace oblique to the coordinate axes, need not give such a rectangle.

## Why the exclusion divisor is still missing

After a fixed raw prefix through draw 288, Part 202 counts the tuples of 118 fresh marks that leave every prescribed old winner selected. At draw 289 the corresponding count uses 117 marks. Each count tests all mixed fresh competitors and signed ties. An index in (1) counts cosets of a projection modulo a section, even before a fresh mark is sampled. For example take $q=7$, three horizontal rows of period seven and one column $(2,0,0)$. The unique shortest line in the window is generated by $(2,0,0,1)$. After removing it, take $T$ spanned by $w=(1,0,0,-2)$ and the second row axis. In $T$, $P=C$ has generators $7w/5$ and $7e_2$, while $B$ has generators $7w$ and $7e_2$. Thus $[P:B]=5$ although every mark group has order a power of seven. This exact low-dimensional check illustrates the distinction between the two counts. [Part 202, joint exclusion](wall1_joint_exclusion_scale.md#which-probability-multiplies)

**Open conjectures.** For the original cutoff, the prefix estimate through draw 171 is $5.055\cdot10^{-12}$. At the enlarged cutoff the estimate through draw 164 is $8.336\cdot10^{-13}$ (both strict upper bounds). On later doubly-gated histories with full-rank rectangles, the estimates above establish neither an early qualifying plane nor the required suppression of old-flag survival. In particular, a first hit on draws 172–406 is only one condition in the residuals. The vertical remainder needs a first hit on draws 396–406 with the prescribed winner height and length. The horizontal remainder includes wholly old hits and the remaining mixed hits at draws 403–406. Both require a terminal hit. The ceilings $Z_{2,\mathrm{rem}}\le6.485\cdot10^{-11}$ and $p_{\mathrm{old}}+p_{\mathrm{late}}\le7.633\cdot10^{-11}$ remain unproved. No reachable doubly-gated counterexample follows from these section tests. [Part 198 audit](wall1_flag_horizon.md#audit) · [Vertical remainder](wall1_z2_vertical.md#audit) · [Horizontal remainder](wall1_z1_horizontal.md#audit)

**Verification.** Scratch calculations used 70-decimal outward interval arithmetic. With $N=400+n$, use $qR_0(t)=(q^n/(408000V_N))^{1/N}-\sqrt N/2$, the factorial formulas for the even and odd ball volumes, and $g_d=(2/\pi)\Gamma(2+d/2)^{2/d}$ for the Blichfeldt rows. For the Part 77 rows use $g_d=\exp(2\min(h_{\rm LCZ},h_{65})/(10^9d))$ from the two integer columns. The rank-447 statement checks each $d=2,\ldots,447$ separately, with $g_1=1$. Exact integers verify $10^{293}U(261)<1$ and $10^{250}U(511)<1$. An exhaustive check over all 81 two-by-two matrices modulo three and all 14 nonempty proper coordinate subsets compared the cardinalities of the projected and shortened graph codes. Their ratio was $3^{u+v}$ on all 1,134 tests. Direct enumeration through squared norm five verified the modulus-seven winner and rational basis determinants gave the plane index. These are paper bounds with scratch verification.

## Audit

**Verdict — MINOR CAVEATS.** All three main claims hold. One qualification concerns the draw range of the horizontal residual in the final paragraph.

**Part 204 family.** At draw 120 the 141 core inputs leave 84 noncore columns, all zero on the 292 rows outside the bootstrap and processed rows. At draw 156 the corresponding block has 256 rows and 120 columns. In the scaled dual section the $c$ congruences determine $b_J$ from $a_I$, and the remaining congruences have rank $v$ on $a_I$. The covolume is therefore $q^{c+v}$ for every assignment to the other three blocks. The Part 77 thresholds in (3) are in $(0.0598381,0.0598382)$ and $(7.0833418,7.0833420)$, respectively. The floor thus requires rank at least one at draw 120 and at least eight at draw 156. The first conclusion applies to every labeling in Part 204, including those outside its passing-prefix tests. The second applies to every proposed replacement of rank at most seven.

**Adaptive rectangles.** Sample the full $400\times511$ raw matrix once. Every deficient rectangle observed at any earlier draw supplies a triple consisting of its two coordinate sets and a kernel line. For each fixed triple, dotting the 256 independent uniform rows with a fixed nonzero representative gives 256 independent uniform scalars. Taking the union over all triples before any selection gives exactly the majorant $U(511)$, with no extra factor for stopping times. Independent integer comparisons give $10^{293}U(261)<1$ and $10^{250}U(511)<1$. The base-ten logarithms lie in $(-293.532018,-293.532017)$ and $(-250.848820,-250.848819)$. Intersecting with either gated residual preserves the upper bound on joint mass.

**Rational planes.** A rational orthogonal projector has a common denominator, so $C$ is discrete. It contains the full-rank section $B$. The identity $C^*=L^*\cap T$ transfers the dual floor to $C^*$, while the closed raw cutoff gives $\lambda_1(B)>250$. Binary Hermite applied to these two lattices gives $[C:B]>3(250R_0(406))^2/4$, whose right-hand side lies in $(1892.08542070,1892.08542071)$. Integrality gives 1,893 even for a plane chosen from the complete history. For a retained plane, $\pi_T\pi_E=\pi_T$ gives the intermediate inclusion in (2). The area cutoffs yield the stated lower bounds 70 and 57 on $[P:B]$. The index counts all cosets. The denominator of one projected vector relative to $B$ is the order of its own coset.

**Numerical and finite checks.** An independent 90-decimal-digit interval computation using $V_0=1$, $V_1=2$, $V_d=2\pi V_{d-2}/d$ reproduced all six threshold intervals, the draw-406 radius and the Part 172 exit majorant. The Part 77 caps give $250R_0(406)>g_d$ separately in each dimension through 447, with $g_1=1$. The lower bound on $\log_q I_T$ for the frozen span lies in $(4.55283,4.55284)$. Enumeration over all 81 matrices modulo three and all 14 coordinate subsets per matrix reproduced both section determinants and the index formula. The indices 1, 3 and 9 occurred 110, 784 and 240 times, totaling 1,134. In the modulus-seven example the only nonzero vectors through squared norm five are the two signs of the stated winner. Projecting the raw basis gives $7w/5,7e_2$ and two zeros, while membership of $(s,t,0,-2s)$ in the raw section requires $5s=t=0\pmod 7$. This gives index five.

**Residual scope.** Draw 172 starts the original-cutoff tail *after charging* first hits through draw 171. The published $p_{\rm old}$ includes wholly old horizontal first hits on draws 155–406. Using the shorter tail in that budget requires accounting for the earlier contribution. The mixed remainder starts at 403 and the vertical remainder at 396, each with its original selection and terminal tests. In Part 202 the surviving-mark fraction is $p(S,k)$, with reciprocal divisor when positive. The section index gives no estimate of that fraction. Both quoted residual ceilings remain open. [Horizontal residual and audit](wall1_z1_horizontal.md#audit) · [Prefix charges and audit](wall1_flag_horizon.md#audit) · [Part 202 joint count](wall1_joint_exclusion_scale.md#which-probability-multiplies)
