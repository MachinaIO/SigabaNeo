# A delayed first plane with a surviving old flag

**Counterexample.** In the unconditioned Part 108 restart at width 506, there are reachable prefixes with the following properties. Here $i$ is the last draw fixed by the prefix, $k=406-i$, and $\tau_X$ is the first draw whose **retained** lattice contains a saturated plane of area at most $X$, counting the initial state as draw zero.

| $i$ | $k$ | $\tau_{1352/\sqrt3}$ | $\tau_{676\sqrt2}$ | Conditional probability of the entire old flag and a terminal old plane below both cutoffs |
|---:|---:|---:|---:|---:|
| 288 | 118 | 273 | 273 | $>1-10^{-298}$ |
| 289 | 117 | 275 | 275 | $>1-10^{-301}$ |

Both entry winners have newest-coordinate height one up to sign. The terminal plane exhibited below has minimum strictly between 26 and 27. Thus even checking **both** cutoffs through draw 171 cannot give a substantial uniform exclusion divisor. The construction delays a single projection that shortens 105 independent old vectors simultaneously. [Part 198, horizons and first-hit definition](wall1_flag_horizon.md#audit) · [Part 202, previous examples](wall1_joint_exclusion_scale.md#audit)

## The specified prefix

Write $q=3329$, and use the graph convention $x=Ay\bmod q$. Among the 400 horizontal axes reserve one shared axis $e_0$, 105 private axes $e_j$, and $n=k-103$ further axes $f_1,\ldots,f_n$. The other $r=294-n$ rows are zero throughout the prefix. Initial graph column $j$ is $64e_0+26e_j$ for $1\le j\le105$. Each column has its own orthogonal unit input coordinate, as in the restart. Prescribe the next $i$ raw columns in the following order.

1. Append $i-2n-1$ zero columns.
2. Append $32 f_l$ once per row in increasing order.
3. Append $16e_0$ at draw $d=i-n$.
4. Append $120 f_l$ once per row in the same order.

These prescriptions have positive raw-prefix probability $q^{-400(105+i)}$. The two cases use $(n,r)=(15,279),(14,280)$, respectively. The proof below uses the physical lengths in the framed lattice, including the unit height of each fresh column. [Part 108, transition](wall1_first_tour.md#transition-and-loss-of-randomness)

## Verification of the first hit

Before draw $d$, the summand containing the initial inputs has minimum greater than 36. Indeed, a vector of norm at most 36 has integral input tuple $y$ with $|y_j|\le36$. In each private row $26y_j$ is already centered modulo $q$. If $\|y\|^2\ge2$, the private and input components alone have squared norm at least $2(26^2+1)>36^2$. If $y=\pm e_j$ in the input coordinates, the shared residue has centered magnitude 64. If $y=0$, every nonzero horizontal component has magnitude at least $q$.

Every padding unit wins uniquely up to sign and its projection restores the old lattice. On a fresh $f_l$ row the vector $(32,1)$ wins. Within its radius, a candidate of height $h$ has $|h|\le32$, so $32h$ is centered. The squared norm at nonzero height is at least $1025h^2$, and the horizontal period is $q$. Projection leaves a one-dimensional period $q/\sqrt{1025}>36$. The orthogonal summands therefore never interfere with these choices. Through $d-1$ every retained minimum exceeds 36. A Gauss-reduced basis of any plane then has area greater than $36^2\sqrt3/2>676\sqrt2$, since its second length is at least its first and the absolute cosine of their angle is at most $1/2$.

At draw $d$, the shared-row pivot $(16,1)$ wins uniquely up to sign. Within its radius a nonzero initial input component forces a private component of magnitude at least 26, by the same centering argument. With no initial inputs, the new shared graph has centered displacement $16h$ for every competing height $|h|\le16$. All other rows are too long. Projection shrinks the image of the shared unit to length $1/\sqrt{257}$. The 105 projected initial columns are independent by their untouched input coordinates. Each now has squared norm
$$
 B^2=26^2+1+64^2/257<693 .
$$
Any two span a plane of area at most $B^2<1352/\sqrt3$. Saturation divides its area by a positive integer. This proves the two exact first-hit times in the table.

On each remaining $f_l$ append the height-one pivot is $(120/\sqrt{1025},1)$ in orthonormal coordinates. Its norm is less than four. At any competing nonzero height $|h|\le3$, the centered numerator is $120h$, giving minimum squared norm $h^2(1+120^2/1025)$ on that layer. The shared and private summand has no nonzero vector within radius four. An initial input there forces a private displacement of at least 26 at that radius, and with zero inputs its shortest horizontal period is $q/\sqrt{257}$. Each completed $f_l$ row has period
$$
 L=q/\sqrt{1+32^2+120^2},\qquad B^2<L^2=q^2/15425<729 .
$$
Indeed, at either height-one freeze the old period divided by the pivot length gives the new period, and the projected original row unit is $1/q$ times that period. This also verifies the determinant path at entry. The padding has factor one, the shared pivot contributes $\sqrt{257}$, and each pair of $f_l$ pivots has length product $\sqrt{15425}$. Hence $D_i=q^{400}/(\sqrt{257}\,15425^{n/2})$.

## The 406th retained state

First run the prescribed signed selector on the old section alone. During the first 105 freezes at least one of the 105 independent short input vectors still has nonzero projection before each choice. Its length is at most $B<L$. Thus none of these winners touches an $f_l$ period. During the remaining $k-105=n-2$ freezes, an intact period bounds the winning length by $L$. A winner with a component on an intact period must be that pure period, since it already spends the full length $L$ there. Induction leaves at least two intact periods. The $r$ unused rows, of period $q$, are untouched throughout.

The two intact periods span a direct summand of the old terminal lattice. Their plane has minimum $L>26$ and area $L^2<729<1352/\sqrt3$. If the flag is selected, projection onto the $k$ fresh heights maps the full terminal lattice onto $\mathbb Z^k$ with kernel equal to the old section. Consequently the plane remains saturated. This argument allows every signed tie in the old selector. [Part 201, old section and joint exclusion](wall1_multistep_branch.md#where-joint-selection-can-save-mass)

Consider the first disagreement of the full selector with this forced path. Up to that comparison the $r$ unused horizontal axes and all fresh height axes have been left intact. A competitor using fresh coordinates must therefore have integer components $x\in\mathbb Z^r$ and $0\ne b\in\mathbb Z^k$ with
$$
 x\equiv U b\pmod q,\qquad \|(x,b)\|\le L<27 .
$$
Here $U$ is the restriction of the $k$ future raw columns to those $r$ rows, and $b$ is zero-padded after the comparison. All past columns vanish on these rows. Conditional on the specified prefix, $U$ is uniform. For each fixed $(x,b)$ in this ball, $b\ne0\bmod q$, so the congruence has probability $q^{-r}$. The same integer box covers all stages, all mixed supports and all ties. Thus the total failure probability is at most $53^{r+k}/q^r$. The exact integer comparisons $53^{397}10^{298}<3329^{279}$ and $53^{397}10^{301}<3329^{280}$ give the table. Each individual conditional survival factor given earlier successes is at least the whole product. [Part 202, conditional factors](wall1_joint_exclusion_scale.md#which-probability-multiplies)

## Scope of the obstruction

The retained Rankin inequality bounds the new rank-two minimum **from below** by $\min(\Delta_2(M),\Delta_3(M))/s$, where $s$ is the winning length and $\Delta_j$ denotes the rank-$j$ minimum covolume. At draw $d$ the divisor is $\sqrt{257}$. The exact determinant update and the Rankin inequality are compatible with the simultaneous shortening above. Neither can imply the proposed dichotomy on all prefixes with $\tau_X>171$. [Lean Rankin inequality](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean) · [Part 199, determinant direction](wall1_survival_constraint.md#audit)

**Open.** Conditioning additionally on Part 192's raw and dual good event is a stronger hypothesis. These prefixes already contain raw unit vectors from padding, and their first hit is a positive-height win before draw 395. They supply no lower bound for either gated residual $Z_1,Z_2$, or for a stratum requiring the first hit to occur at draw 406 itself. A terminal hit with a first hit after 171 includes the examples in the table. A first hit *at* 406 imposes all the additional misses through 405. The weighted residual estimate remains conjectural. [Part 192, residual](wall1_rank2_tail.md) · [Parts 197–202](../PROOF_GAP.md)

## Audit

**Verdict — SOUND.** Both exact first-hit times and both strict conditional probability bounds hold for the unconditioned Part 108 restart. No correction is required.

**First hit.** The prefixes have 257 and 260 padding draws, respectively. Exact enumeration of the centered horizontal residue at every height within each proposed pivot radius leaves only the winning sign pair for each of the three row pivots. Before the shared pivot, the private rows and input coordinates contribute at least $2(26^2+1)$ to squared length for any contender with input squared norm at least two and length at most 36. A singleton also pays $64^2$ on the shared row. Together with the separate-row periods, this gives retained minimum greater than 36 and hence plane area greater than $36^2\sqrt3/2>676\sqrt2$. At the shared pivot, the Gram matrix of two distinct projected initial columns has diagonal $677+c$ and off-diagonal $c=4096/257$. Their area is $\sqrt{677(677+2c)}<693$ even before saturation. The pivot therefore gives the first hit at both cutoffs, on draw 273 or 275.

**Terminal plane and joint survival.** Fewer than 105 frozen directions cannot kill all 105 independent short vectors. Their surviving projections bound each of the first 105 winning lengths strictly below $L$. The remaining $n-2$ freezes can remove at most one separate-row period each. The two surviving periods span a saturated plane of minimum $3329/\sqrt{15425}$ and area $3329^2/15425\in(718.45,718.47)$. On flag survival, every lattice point in their real span has zero fresh heights and belongs to the old section, which proves saturation in the full output as well. At first disagreement, zero-padding gives a single nonzero fresh tuple $b$ modulo $3329$ and an integer vector $x$ on the untouched rows. The same 397-coordinate box covers every stage, including tied competitors. Each candidate congruence has probability $3329^{-r}$ under the original conditional law of the unread columns. The two box bounds have base-ten logarithms approximately $-298.18803$ and $-301.71034$. Exact integer comparisons in scratch verified the strict bounds in the table.

**Raw-good gate and residual.** Every completion already contains a raw vector from an initial graph column of squared norm $64^2+26^2+1=4773<250^2$. Each zero padding column also gives a raw unit vector. Thus every such completion fails the raw part of $G$, irrespective of the dual floors. Independently, the first-hit winner has positive height and length $\sqrt{257}<30$ on a draw before 395. These histories contribute zero to both $Z_1$ and $Z_2$. Their high conditional survival concerns prefixes missing both cutoffs through 171. The gated, prefix-weighted draw-406 estimate remains open. [Part 184, definition of the good event](wall1_penultimate_projection.md) · [Part 192, residual strata](wall1_rank2_tail.md#audit)
