# Column subsets supporting a selected plane hit

A subset can certify the positive part of a win if it supports raw lifts of the earlier frozen directions, the two designated minima, and a transverse witness. There is an exact test for whether such a certificate wins in **some** processing order. Its positive equations involve only the subset. Its negative tests exclude smaller signed keys and may involve several outside columns in the same equation. Single-outside-column tests give a matching bound that integrates over all orders of the outside columns.

For the width-506 marginal restart, **every such certificate for either event has modular input rank at least 118**. In the two one-append toys the rank is exactly three, so a passing flag determines the entire design. The subset calculation reproduces the toy majorant means exactly. At width 506 it gives finite formulas and quantitative requirements on their sums. The estimate on those sums needed for the shared allowance remains open.

## 1. The event and the subsets

Use a uniform matrix with independent columns in $K=\mathbb F_q^m$, with $q$ prime. The initial graph has $j$ inputs, retained rank $d=m+j$, and window width $b=d+1$. Append at height one and freeze one designated shortest line at each step. At step $T$ test the first selected line $v$, the designated minimum $x$ after quotienting by $v$, and the existence of a nonzero witness after also quotienting by $x$. Give both signs of a line the key
$$
 (\|y\|^2,\min_{\rm lex}(y,-y)).
$$
Output coordinates precede input coordinates, and input coordinates are in processing order. A fixed-label tie rule gives a different experiment. [First-tour law](wall1_first_tour.md) · [Order conventions and audit](wall1_random_order.md)

In the restart for plain LWE $(511,512,3329)$ these parameters are $m=400, j=105, T=406, b=506$. There are $n_0=j+T=511$ columns used in the test. Write $N=511$ for permutations of these columns and $N=512$ for permutations of the full input, where the last slot goes unread. Fixed-order probabilities agree under these conventions. Their some-order majorants can differ. The CBD(3) plant is independent of these design events. The order always ranges over labeled positions, including when column values coincide. [Marginal restart](wall1_idea_round2.md) · [Part 164 and audit](wall1_selected_hit_direct.md)

Let $D$ be the incoming covolume before step $T$, $V_i$ the Euclidean unit ball volume, $s=\|v\|, t=\|x\|, g=(D/V_b)^{1/b}, h=(D/(sV_d))^{1/d}$ and $c=477/500$. Both events require
$$
 1<t\le r(h)=\sqrt{1+c^2h^2},\qquad 0<z<R=ch\,t^{-1/d}
 \tag{1}
$$
for the length $z$ of a quotient witness. For the upper-band event, require $32.18553<g<203.888, 0.990g<s\le1.097193g$, and nonzero fresh coordinate of $v$. Its fixed-order mass is $P$. For the inherited event $H_{\rm old}$, require lifts of $v,x$ and a witness all with zero fresh coordinate. Compare both designated minima against the **full** window, including fresh competitors. Its fixed-order mass is $p_a$, with no upper-band or good-history cut. This includes the near-lift and shrunken-lift cases. In the one-append toys only the width-specific condition on $g$ is omitted from the upper-band test. [Upper-band quotient and audit](wall1_upper_band_quotient.md) · [Inherited event and audit](wall1_inherited_witness.md) · [Residual split](wall1_penultimate_tail.md)

### A finite certificate

Fix a subset $S\subseteq[N]$ of input labels and assign its elements injectively to slots through $n_0$. This fixes their relative order and leaves vacant slots. Use slot coordinates for the following calculation. A template is a list of $L=T+2$ integer vectors $f_i=(a_i,u_i)$, with $a_i\in\mathbb Z^m$ and input coordinates $u_i$ zero outside the placed slots of $S$. Require the union of their integer input supports to be exactly the placed $S$. For $i\le T$, require $f_i$ supported through slot $j+i$. The last two vectors can use all slots through $n_0$. For the inherited test the last three vectors must vanish in slot $n_0$. For the vertical test the coefficient of $f_T$ in that slot must be nonzero.

Let $\Pi_i$ be orthogonal projection off the real span of $f_1,\ldots,f_{i-1}$, put $y_i=\Pi_i f_i$, and require $\ell_i=\|y_i\|>0$. The proposed lengths $s,t,z$ are $\ell_T,\ell_{T+1},\ell_{T+2}$. Test (1) and the applicable band using
$$
 D=q^m/\prod_{i<T}\ell_i.                                             \tag{2}
$$
Impose also $s\le2g$, which every selected minimum satisfies by the volume argument in Theorem 3. Require $\ell_i\le q$ and size-reduced lifts
$$
 |\langle f_i,y_k\rangle|\le\ell_k^2/2\quad(k<i).
 \tag{3}
$$
Both endpoints are allowed. These rules define a finite list before any column values are known.

For each $i\le T+1$, form a **competitor list** of raw integer sign pairs $w=(a,u)$ in the same available prefix as $f_i$. Keep exactly the pairs satisfying (3) against $k<i$ for which $\Pi_i w\ne0$ and its key is strictly smaller than the key of $y_i$. There is no competitor list for the existential witness. No band, primitivity or positive-height filter is applied to competitors. All comparisons here are on projected vectors in the processing frame.

**Theorem 1 (exact support and extension test).** A design has a hit in some order if and only if there exist $S$, a placement and a template as above satisfying the following two conditions.

1. For each $f_i$, the column combination with coefficients $u_i$ equals $a_i\pmod q$. No competitor supported entirely on the placed $S$ satisfies its own graph equation. Both tests are local to the labeled values $A_S$.
2. There is a bijection from the remaining labels to the vacant slots such that every remaining competitor fails its graph equation. Explicitly, a competitor $w$ with exterior slot coefficients $u_j$ forbids the equality
   $$
     \sum_{j\text{ vacant}} u_j C_{\sigma(j)}
         =a-\sum_{j\text{ placed}}u_j C_{\sigma(j)}\pmod q .              \tag{4}
   $$
   Here $\sigma(j)$ is already fixed on placed slots. Congruences with vanishing exterior coefficients modulo $q$ are deterministic once $A_S$ is given.

Call $S$ responsible when a placement and template on exactly $S$ pass both tests. This definition allows several responsible supports per design. It gives a condition on raw integer vectors and a finite system of forbidden equalities on a permutation. It does not require computing the reducer history for each completion of $A_S$.

*Proof.* The raw graph on a prefix $J$ is $\{(a,u):u\text{ supported in }J, a=A u\bmod q\}$ in its used ambient coordinates. It contains $q$ times every coordinate axis and has covolume $q^m$, by the surjective map $(a,u)\mapsto a-Au$. Removing a primitive projected winner gives the orthogonal quotient of the entire prefix graph. This follows by completing a primitive vector to a lattice basis and projecting the other basis vectors. Extending frozen directions by zeros commutes with passing to the next raw prefix. The new height is one, so appending preserves covolume in the enlarged window and quotienting divides it by the winner length. This proves (2) on an actual path.

Every selected vector lifts to its raw prefix. In any nonzero remaining quotient, some projected $q$-axis is nonzero and has norm at most $q$. For the witness one may take a shortest vector in the eligible quotient, using the old sublattice for the inherited test. The same axis argument applies there. Reduce each lift along earlier raw vectors in descending index, subtracting nearest integer multiples. Subtracting one copy of $f_k$ subtracts $y_k$ from the orthogonal component along $y_k$ and leaves all later orthogonal components unchanged. This proves (3), preserves the projection and keeps all lifts in their allowed prefix. In the inherited case every earlier lift used for rounding is old. The Gram–Schmidt decomposition now bounds raw squared norms by $\ell_i^2+\tfrac14\sum_{k<i}\ell_k^2$. The same bound applies to a rounded representative of every smaller-key competitor. Hence the lists are finite and complete, including length ties. Taking the union of input supports of these lifts supplies $S$ and a placement. All their equations hold and no smaller-key competitor is present.

Conversely, put the columns in an order supplied by condition 2. Inductively the full projected prefix before selection $i$ is the raw prefix projected by $\Pi_i$. The positive equation puts $y_i$ in it. Every nonzero line beating $y_i$ would have a rounded lift on its competitor list, contradicting condition 1 or 2. Equality of the entire key gives the same sign pair. Thus $y_i$ is the designated minimum and is primitive, so the induction continues. Apply this also to $x$ in the full quotient of the last window. The last positive equation and (1) supply the required witness with the prescribed fresh-coordinate condition. This proves both directions. ∎

The projections of the three terminal lifts alone need not be computable from their support. The earlier lifts in Theorem 1 specify the projector and $D$. The lower bound below applies to this explicit certificate class. It leaves open the possibility of encoding past selections in a different way.

## 2. Exact column counts and a bound for the outside columns

Let $M_E(A)=\max_\pi \mathbf1_E(A_\pi)$ for either event $E$. This is the least permutation-invariant pointwise majorant, since an invariant bound must dominate the maximum on each orbit. Write $R_S$ for the responsibility indicator and $\theta_{E,k}=\Pr(R_{[k]}=1)$. Theorem 1 and column exchangeability give
$$
 \Pr(E)\le \mathbb E M_E
   =\Pr\!\left(\bigcup_S\{R_S=1\}\right)
   \le \min\!\left(1,\sum_{k=0}^{n_0}\binom Nk\theta_{E,k}\right).
 \tag{5}
$$
For fixed $k$, integrating $R_S$ over the independent outside columns gives a symmetric kernel on $A_S$. Its sum over $k$-subsets is an unnormalized U-statistic with the same **mean** as the support count. The conditional kernel can be fractional on a particular hit design. The pointwise majorant in (5) is the union indicator. Averaging the original event over orders instead of maximizing would give exactly its original mean. [Orbit identities and audit](wall1_new_tools.md)

**Positive incidence.** Write $U$ for the $k\times L$ matrix of input coefficients on the placed labels and $Z$ for the $m\times L$ output matrix, reduced modulo $q$. Set $\rho=\operatorname{rank} U$ and $Q=q^m$. For a fixed placement and template,
$$
 \Pr(A_SU=Z)=
  \begin{cases}Q^{-\rho},&\ker U\subseteq\ker Z,\\0,&\text{otherwise.}\end{cases}       \tag{6}
$$
Indeed, the prescription $U\lambda\mapsto Z\lambda$ defines a map on a $\rho$-dimensional subspace exactly under the kernel condition. The number of extensions to $\mathbb F_q^k$ is $Q^{k-\rho}$ out of $Q^k$. Conditional on incidence, those extensions are uniform and all outside columns retain their independent uniform law. Local competitor exclusions must still be tested on the extension. This is the same equal-fiber principle as in Parts 92 and 108, applied before conditioning on selection. [Finite-field graph counts](wall1_qary_gap.md) · [Fresh-column fibers](wall1_first_tour.md)

**Proposition 2 (void bound without ordering the outside labels).** Fix a placed template and a passing local assignment $A_S$. Set $h_o=N-k$. In each vacant slot $j$, collect the forbidden values from (4) for all equations having just one nonzero exterior coefficient modulo $q$, in slot $j$. Each gives one forbidden value by division in $\mathbb F_q$. Write $G_j\subseteq K$ for the complement of this set, with $G_j=K$ for an unrestricted slot. Reject a deterministic forbidden equality immediately. For every nonempty subset $J$ of vacant slots define
$$
 u_J=\left|\bigcup_{j\in J}G_j\right|/Q,\qquad
 B_J=\sum_{i=|J|}^{h_o}\binom{h_o}{i}u_J^i(1-u_J)^{h_o-i}.
$$
The probability over the outside columns that **some** assignment of them passes all competitors is at most $H=\min_J B_J$, taking $H=1$ if there are no vacancies. A sharper upper bound is the probability that the Hall inequalities for **all** $J$ hold simultaneously. If every nondeterministic exclusion has only one nonzero exterior coefficient, this sharper bound is exact.

*Proof.* Join slot $j$ to each outside label whose column belongs to $G_j$. A permissible bijection gives a perfect matching. For $J$ the number of neighbors is a binomial variable with parameters $h_o,u_J$, because it counts independent labels in the displayed union. It must be at least $|J|$, proving every bound $B_J$. Hall's matching criterion gives sufficiency for simultaneous satisfaction in the one-slot case. To see the criterion, take a maximum matching. From an unmatched slot follow alternating paths, first along unmatched edges and then back along matching edges. If no unmatched label is reached, all neighbors of the reached slots are matched back into those slots, which include an unmatched root, contradicting the neighbor inequality. Otherwise augment the matching. Equal numbers of slots and labels finish the proof. The exact simultaneous probability can be computed from the multinomial law of the membership types $(\mathbf1_{a\in G_j})_j$, $a\in K$. Mixed exclusions (4) can reject even a perfect matching. ∎

In particular $\theta_{E,k}$ is bounded by the sum over its compatible placed templates of
$$
 Q^{-\rho}\,
 \mathbb E\!\left[\mathbf1_{\rm local\ exclusions\ pass}\,H(A_S)
                   \mid A_SU=Z\right].                                    \tag{7}
$$
The deterministic exclusions are included in the indicator. This follows by a union bound over templates, then conditioning in (6). Keeping their union before integrating avoids charging the same design for several lifts, placements or witnesses.

There is also an exact finite way to retain **every** mixed exclusion. For a single completed placement of the remaining labels, let $C$ be the positive system on all $N$ columns, and $\mathcal B$ the finite family of forbidden equations. Write $w(D')$ for the value of (6) with the coefficient and output matrices of a system $D'$, extended to all input labels. Its signed-void mass is
$$
   \sum_{I\subseteq\mathcal B}(-1)^{|I|}w(C\cup I).                       \tag{8}
$$
Expand the product of the absence indicators to prove the formula. For an intersection of several certificates or orders, take the union of their positive systems and the union of their forbidden equations before applying (8). Inclusion–exclusion over completed placements and templates thus computes each $\theta_{E,k}$ exactly. This construction charges a compatible witness and its void jointly. Multiplying by the unconditioned probability of an empty ball would discard both the affine constraints and the signed ties. [Selected incidence and audit](wall1_selected_hit_direct.md)

## 3. How large must a support be?

**Theorem 3 (modular rank obstruction).** For every realizable list of $L$ independent raw graph vectors in Theorem 1, with modular input rank $\rho$,
$$
 q^{L-\rho}\le \operatorname{vol}_L(f_1,\ldots,f_L)
       =\prod_{i=1}^L\ell_i=\frac{q^m}{D}stz .                            \tag{9}
$$
In particular the responsible support has size at least $\rho$. At width 506, $\rho\ge118$ for each of $P$ and $p_a$.

*Proof.* Modulo $q$ the full raw column matrix is $\binom{AU}{U}$, with the input rows padded by zeros as necessary, so its rank is $\rho$. Every maximal minor is divisible by $q^{L-\rho}$. Indeed, choose $\rho$ independent columns modulo $q$ and subtract integer combinations of them from each remaining column to make all its entries divisible by $q$. These operations preserve each maximal minor up to sign. At least one such minor is nonzero over the integers. Cauchy–Binet expresses squared volume as the sum of their squares, proving the inequality. Gram–Schmidt and (2) give the equalities.

Here $L=408, m=400$. The deterministic step-405 bound is $g>g_0=32.18553$. Use $s\le \eta g$ with $\eta=1.097193$ on $P$. For $p_a$ use $\eta=2$. A ball of radius greater than $g$ has volume greater than $D$, so two of its points agree modulo the window lattice by integrating translates over a fundamental domain. Their nonzero difference has norm less than twice its radius. Let the radius decrease to $g$. This requires no good-history restriction on $p_a$. [Deterministic lower bound and audit](wall1_band_plane_hits.md)

Put $h_0=g_0(V_b/(\eta V_d))^{1/d}$, hence $h>h_0$. Since $t>1, t\le r(h), z<ch$, rearranging (9) gives
$$
 \rho>8+\log_q\!\left(\frac{V_d h_0^d}{r(h_0)c h_0}\right).
 \tag{10}
$$
Indeed $D/s=V_d h^d$ and $h^{d-1}/\sqrt{1+c^2h^2}$ increases for $d\ge2$. The right side is in $(117.13927,117.13928)$ for the vertical event and $(117.06554,117.06555)$ for the inherited event. Both give the stated integer bound. These intervals follow by outward interval evaluation at 60 decimal digits using $V_0=1, V_1=2, V_i=2\pi V_{i-2}/i$. ∎

**Width-506 accounting.** A compatible individual template has mass at most $3329^{-400\cdot118}<10^{-166253}$ before exclusions. This bound concerns a prescribed template. The number and overlaps of feasible templates matter. In particular all kernels of order $k<118$ in (5) vanish for this construction. At $k=118$, (6) fixes every column of the support for each compatible template.

For a $P$-allocation of $10^{-4}$, the $k=118$ term of the *untruncated* support first moment alone requires $\theta_{P,118}\le10^{-4}/\binom N{118}$. This is approximately $2.842\cdot10^{-123}$ for $N=511$ and $2.187\cdot10^{-123}$ for $N=512$. The corresponding $p_a$ allocation of $0.00009770868$ gives $2.777\cdot10^{-123}$ and $2.137\cdot10^{-123}$. All larger supports must share those same budgets. These are thresholds on **some-order** support probabilities for this first-moment proof. The fixed-order masses could meet the budget with larger support probabilities.

At the opposite end, inherited certificates use at most 510 columns. For a fixed 510-subset and its values, every admissible placement fills exactly the first 510 slots. For each local template that passes the local exclusions, compute the allowed set for slot 511 by (4), rejecting deterministic violations. Take the union $G_*$ of these allowed sets over all such templates and placements. Then the conditional probability of responsibility is exactly
$$
    1-(1-|G_*|/Q)^{N-510}.
$$
Indeed, slot 511 is the only vacant slot read, so every remaining nondeterministic exclusion concerns that column alone. Any of the independent $N-510$ outside labels can occupy it. This eliminates the exterior probability at maximal inherited support once the local union is known.

The void bound has a separate numerical scale. For $N=511,\ k=118$, there are 393 vacancies. If every slot has the same forbidden set of relative size $\delta$, the exact one-slot matching probability is $(1-\delta)^{393}$. Making this factor alone at most $10^{-4}$ requires $\delta\ge1-10^{-4/393}>0.02316$. If each slot excludes just one value, even differing between slots, the survival probability of the one-slot tests is at least $1-393/3329^{400}$, by testing one fixed assignment and taking a union bound. This comparison quantifies the weakness of a few isolated exclusions. The actual forbidden sets, multi-slot exclusions and local masses in (7) have not been bounded in aggregate.

## 4. Exact check on both one-append families

Here $j=2, T=1, N=3$. The band contains only $s^2=2$. On the inherited event both toys also satisfy $s^2\le3$. Indeed a lift of $x$ rounded along the shortest $v$ gives $t^2\ge3s^2/4$, and at $s^2=4$ the upper gate $1+c^2h^2$ is already less than 3 and decreases with $s$. At $s\ge1$ both families have $c^2h^2<2.316$. Thus for **either** event $stz<\sqrt{3\cdot3.316\cdot2.316}<5\le q$. Equation (9), or its maximal-minor proof directly at $L=3$, forces $\rho=3$. In particular every passing certificate uses all three columns, and its compatible graph is uniquely specified. An inherited certificate uses only two old columns, so its probability is **zero** in both toys.

For the upper-band count, the following table treats a forced incidence as one pair (design, first candidate) passing both gates with the second minimum designated. Distinct lifts are merged before counting. The last three columns count input designs by how many of the six labeled orders win.

| $(m,q)$ | Designs | Forced incidences | Designs with a forced incidence | Fixed-order hits | 0 orders | 2 orders | 6 orders |
|---|---:|---:|---:|---:|---:|---:|---:|
| $(1,17)$ | 4,913 | 24 | 8 | 2 | 4,909 | 3 | 1 |
| $(2,5)$ | 15,625 | 48 | 16 | 4 | 15,617 | 6 | 2 |

**Finite verification.** Enumerate raw sign pairs $w\in\{-1,0,1\}^{m+3}$ of squared norm 1, 2 or 3. Store for each a bit set of ordered designs satisfying its graph equation, by testing the congruence in each output row. The following pseudocode gives the support calculation. In it $B(y)$ is the bit set, and union and difference act on these sets.

```text
for v of squared norm 2 with nonzero last coordinate:
    smaller1 = union B(e) for raw e with key(e) < key(v)
    forced_v = empty
    for w with lift rounded along v:
        x = projection of w off v
        require 1 < squared_norm(x) <= 1 + c² h²
        smaller2 = union B(e) over nonzero projections off v with key below key(x)
        for y with lift rounded along x and v:
            project y off span(v,w), obtaining y_perp
            require 0 < squared_norm(y_perp) < c² h² * squared_norm(x)^(-1/d)
            compatible = (B(v) intersect B(w) intersect B(y)) minus smaller2
            forced_v = forced_v union compatible
            hits[support(v,w,y)] |= compatible minus smaller1
    count forced_v once per design for this v
```

All projected keys can be compared with integer numerators using $p_e(w)=\|e\|^2w-\langle e,w\rangle e$. With $X=p_v(w)$ the squared witness length is $\|p_X(p_v(y))\|^2/(\|v\|^4\|X\|^4)$. Use the strict test $(z^2)^d t^2<(c^2h^2)^d$. A scratch calculation used exact rational lengths and 60-decimal outward intervals for the nonrational cutoffs, checking separation at each comparison. To check completeness using (3), put $C=c^2h^2$. Raw squared norms for the second selection and witness are at most $1+C+s^2/4$ and strictly below $C+(1+C)/4+s^2/4$, both below four at each possible $s^2=1,2,3$ in these two rows. For a smaller-key competitor at either selection the same rounding bound applies. The full-rank test also checked every compatible template surviving the second-key exclusion.

In each family the only ordered upper-band hits are $(a,a,a)$ and $(a,a,-a)$, one pair for each $a\in\{-e_1,\ldots,-e_m\}$. Permuting these triples gives one constant design and three distinct mixed designs per axis. On the mixed triples two of six labeled orders win. Thus (5) is an equality in its support-count step, and the least majorant means are $4/4913$ and $8/15625$, twice the respective fixed-order probabilities. There are no vacant slots in a passing toy certificate. Signed competitors on the support itself account for the reduction from forced to selected incidences. [Part 162 toy audit](wall1_upper_band_quotient.md) · [Part 167 orbit audit](wall1_new_tools.md)

## Remaining gap

**Conjecture (width 506, fixed-order restart).** $P+p_a\le0.00019770868$. This is the sufficient allowance after the Part 161 charge through $0.990g$. Replacing either probability by the mean of its least invariant majorant is already a stronger requirement. No factor of two for that replacement has been established at width 506. [Budget and audit](wall1_band_plane_hits.md) · [Direct selected count and audit](wall1_selected_hit_direct.md)

The unresolved quantities for this route are the sums in (5) over support sizes 118 through 511 for the upper band and 118 through 510 for the inherited event. Formula (6) accounts for every prescribed positive flag, (7) retains local signed exclusions and one-slot interference, and (8) includes all mixed competitors and overlaps. Their aggregate width-506 values are unevaluated. Consequently this argument gives neither the proposed $10^{-4}$ bound for $P$ nor the complementary bound for $p_a$. The thresholds above quantify what the subset count would have to prove. The actual numerical excess, if any, is unknown.

## Audit

**Verdict — SOUND.** The support criterion, rank obstruction and numerical claims hold for the stated processing-order tie rule and full-history certificates. No correction is required.

Reducing a raw lift by earlier selected lifts in descending order preserves its quotient image and its allowed prefix. Thus every strictly smaller projected key, including one tied in length, has a representative on the competitor list. Equality of signed keys identifies the same line. On an inherited hit the final three lifts can all be chosen old, while the two minimum comparisons still range over the full window. Given a placed template, an exterior equation with zero modular coefficients is deterministic. For the one-slot exclusions, Hall's neighbor count on a set of slots counts independent outside **labels**, including repeated values, in the union of their allowed sets. This gives the stated binomial tail. Equations involving several slots must hold or fail on the *same* assignment. Expanding the forbidden-equality indicators on each completed assignment gives (8), and inclusion–exclusion over those completions gives the existential probability. [First-pass law](wall1_first_tour.md) · [Order conventions and audit](wall1_random_order.md)

For (9), each integer maximal minor retains its determinant up to sign under the column operations that make the last $L-\rho$ columns divisible by $q$. Positive Gram–Schmidt lengths guarantee at least one nonzero minor. Thus the volume is at least $q^{L-\rho}$. With $L-m=8$, $D/s=V_d h^d$ and the deterministic step-405 floor, independent 65-decimal outward interval evaluation of (10) gave $(117.13927492,117.13927493)$ for $P$ and $(117.06554075,117.06554076)$ for $p_a$. The latter uses the unconditional $s\le2g$. Both ranks are therefore at least 118, so every smaller support has zero responsibility in this construction. [Step-405 floor and audit](wall1_band_plane_hits.md)

An independent scratch enumeration tested all ordered designs, using raw sign pairs through squared norm four, integer projected keys, rational squared distances to the selected plane, and outward intervals for the gate comparisons. The rounding bounds put every lift needed to decide the gates below squared norm four. On the 4,913 designs there were 24 forced incidences on eight designs, two fixed-order hits, and respectively 4,909, three and one designs winning in zero, two and six labeled orders. On the 15,625 designs the corresponding counts were 48 incidences on 16 designs, four fixed-order hits, and 15,617, six and two designs. The least invariant majorant means are exactly $4/4913$ and $8/15625$. Each passing lift triple checked had nonzero input determinant modulo $q$. More generally $stz<5\le q$ forces rank three by (9), so each prescribed passing flag fixes all three ordered columns. The independent inherited test returned zero hits in both families, as also follows because its last input row would vanish. [Toy orbit counts and audit](wall1_new_tools.md)

Exact binomial coefficients give $10^{-4}/\binom{511}{118}=2.8419335790\ldots\times10^{-123}$ and $10^{-4}/\binom{512}{118}=2.1869566994\ldots\times10^{-123}$. For the inherited allocation the respective coefficients are $2.7768157865\ldots$ and $2.1368465232\ldots$ times $10^{-123}$. These are necessary thresholds for the order-118 term of the stated first-moment calculation. Larger supports consume the same allowance. The fixed-order width-506 bound $P+p_a\le0.00019770868$ remains open. [Part 164 and audit](wall1_selected_hit_direct.md)
