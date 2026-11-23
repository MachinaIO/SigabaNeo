# How far the selected flag controls a small plane

For the unconditioned width-506 restart, let $M_h$ be the retained rank-505 lattice after $h$ selections and $\tau_X$ the first $h\ge0$ at which it has a saturated plane of area at most $X$. Write $a=1352/\sqrt3$, $X_*=676\sqrt2$ and $q=3329$. The following are finite-law prefix bounds.

| Cutoff | Horizon | Upper bound on $\Pr(\tau_X\le h)$ | First subsequent single-draw majorant |
|---|---:|---:|---:|
| $X_*$ | **164** | $8.336\cdot10^{-13}$ | $>1.8150\cdot10^{-9}$ at 165 |
| $a$ | **171** | $5.055\cdot10^{-12}$ | $>1.0488\cdot10^{-8}$ at 172 |

These extend the respective $10^{-11}$ horizons by three and four draws. At $a$ the stronger bound through 170 is $2.413\cdot10^{-15}$. The proof uses the actual determinant recursion, overlapping shortest-vector tests in the last nine directions, and a moment bound for earlier winners. The numerical proof uses outward intervals. The new estimates are paper results.

## The term responsible for the crossing

In R65 let $b$ be the terminal witness rank, $i$ the last suffix coordinate used anywhere in the flag, and $j$ the number of old-only winners starting at $i$ before its first use. At $X_*,h=162$ the largest summand has $(b,i,j)=(2,47,0)$, rank $k=118$ and radius $1546.182518$ rounded up. Its value is in $(4.53082,4.53083)\cdot10^{-10}$. The whole sum is in $(4.54658,4.54659)\cdot10^{-9}$, and $99.5907\%$ to $99.5908\%$ of it has $j=0$. At $a,h=168$ the largest term is $(2,52,0)$, in $(2.30239,2.30240)\cdot10^{-12}$, and the sum exceeds $2.3191\cdot10^{-11}$. These are upper-bound terms, so a lower bound on one of them gives no lower bound on the chance of a hit. [R65 and audit](wall1_enlarged_cutoff.md#audit)

In the first example the test counts a positive-height vector at draw 47. A hit actually requires it to win, **115 further winners** on draws 48–162 to come from successive projections of that same window, and a final plane of the prescribed area. R65 uses a separate Hermite inequality for each tail to bound that first length. Its radial count then admits every point below the cap and drops the further comparisons, the common reduced basis realizing those caps, and the old lattice section cut out by the flag. It also replaces the incoming determinant by a minimum over paths. Projection is already present in the counting grid. What is lost about compression is the relation between a dense projected flag and the old sublattice that must have produced it. The calculation uses heights strictly below $q$ throughout this crossing.

## Within one window

Fix the actual hit draw $h$. If the plane minimum is at most 24, use the designated shortest line of $M_h$ as the terminal witness ($b=1$). Otherwise use a Gauss basis of a hit plane ($b=2$). Set
$$
 d_1=K_1=24,\qquad d_2=\sqrt X,\qquad K_2=\sqrt{(X/24)^2+144}.
$$
The area bounds the product of the last two Gram–Schmidt lengths. Their basis vector lengths are at most $K_2$, by size reduction and monotonicity of $X^2/s^2+s^2/4$ for $24\le s\le\sqrt{2X/\sqrt3}$. At the last used coordinate $i$ the remaining $k=h-i+1+b$ directions lift into one window. All subsequent new coordinates vanish on the flag, and the identity input block lets one remove the corresponding columns from its lifts. The winners are shortest at each stage in the successive projections of this rank-$k$ lattice, since they were shortest among all window competitors. Completing by the Gauss basis and reducing the lifts along earlier vectors gives a Korkin–Zolotarev (KZ) basis of the witness lattice. Its ambient index plays no role. [Last-coordinate argument](wall1_uncovered_lines.md#3-a-separate-bound-at-the-unit-threshold)

Write $g_l$ for the R65 certified Hermite cap, $U_l$ for a bound on the log determinant divided by rank and $C_l$ for a monotone length cap. Start at $U_b=\log d_b,C_b=d_b$. At $l>b$ form
$$
 u=U_{l-1}+\frac{\log g_l}{2(l-1)},\qquad c=\sqrt{g_l}\,e^u.
$$
Indeed the determinant before a projection is the winning length times the remaining determinant. Apply Hermite in rank $l$ and solve for that length. Normally set $U_l=u$, $C_l=\max(C_{l-1},c)$. In the line branch cap $c$ also by $24\sqrt{3/2}$ at $l=3$. In the plane branch take the minimum of $u$ and the following at their indicated ranks, leaving the provisional $c$ as an upper bound:
$$
 U_4\le\log d_2+\tfrac14\log(3/2),\quad
 U_6\le\log d_2+\tfrac12\log(3/2),\quad
 U_9\le\log d_2+0.329.                                      \tag{1}
$$
If $v_j$ are successive orthogonal lengths, the classical KZ inequality gives $v_j^2\le(3/2)v_{j+2}^2$. Apply it to two overlapping triples for the rank-four bound. Applying it twice to the first pair and once to the middle pair gives the rank-six bound. The rank-nine certificate at the end uses the proved four- and five-variable inequalities, including their error allowances. [Pendavingh and van Zwam, equations (1.3), (6.10), (6.15) and (6.16)](https://www.matroidunion.org/stefan/pdf/065879.pdf)

## Carrying the flag backwards across a used column

Let $J$ be the rank-$k$ lifted flag in the window at $i$, and $B=\exp(kU_k)$. Its height image is a nonzero subgroup $e\mathbb Z$. The height functional is the last unit-coordinate functional. If $\eta$ is its restriction to $\operatorname{span}J$, adjacent layers have spacing $e/\|\eta\|$. Thus the old lattice $M_{i-1}$ contains a rank-$r=k-1$ section of determinant at most $B\|\eta\|/e\le B$. This holds even when the winning direction is vertical and the old vectors have been compressed.

Suppose at an earlier draw $d$ its output $M_d$ contains a rank-$r$ lattice of determinant at most $B$. Pull it back through the winner of length $s_d$. The lift has rank $r+1$, determinant at most $s_dB$, and minimum $s_d$. In particular
$$
 s_d\le H(B):=g_{r+1}^{(r+1)/(2r)}B^{1/r}.
                                                               \tag{2}
$$
If height is nonzero on the lift, cutting the old section again gives a rank-$r$ witness of determinant at most $H(B)B$. If the lift is wholly old, a shortest primitive dual vector in it cuts a rank-$r$ lattice of determinant at most $\sqrt{g_{r+1}}(H(B)B)^{r/(r+1)}$. This also fits $H(B)B$ at the ranks in the calculation: $B^{1/r}\ge24$ and $\sqrt{g_{r+1}}<24$. Hence at $d=i-1,i-2,\ldots$ record $H_d=H(B)$ and replace $B$ by $H_d B$. Stop when $H_d\ge q$ and use $q$ for all earlier steps. The caps computed from the witness at $i$ are necessary restrictions on the already revealed path. Testing the caps on the prefix preserves the uniform law of the next mark.

## A moment bound for the realized determinant

The path starts at $D_0=q^{400}$, appending preserves covolume, and freezing gives $D_d=D_{d-1}/s_d$. In addition $s_d\le q$ and $s_d\le\sqrt{56.2142}D_{d-1}^{1/506}$. The last coefficient uses the paper packing certificate. The Lean path supplies the actual winners and these determinant identities. Its terminal discrepancy theorem concerns a different final event. [TerminalRestartPath.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/TerminalRestartPath.lean) · [ConcreteTerminal506.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConcreteTerminal506.lean) · [Width-506 determinant recurrence](wall1_penultimate_tail.md)

For draw $d$, let $m=504+d$. Cap at $q$ the least raw length among competitors with newest coefficient one, calling the result $T_d$. Such a competitor keeps that coordinate after all previous projections. Thus $s_d\le T_d$. For $1\le p<m$,
$$
 \|T_d\|_p\le 1+\sqrt m/2+
 \left(\frac{2q^{400}}{V_m}\right)^{1/m}
 \left(\frac m{m-p}\right)^{1/p}.                              \tag{3}
$$
Here $V_m$ is unit ball volume. To prove (3), test $(x,y,1)$ with the $m$ old integer coordinates centered modulo $q$. Each has membership probability $q^{-400}$. Two different old input portions give independent tests, because $(y,1)$ and $(y',1)$ are independent over the field. With equal input portions, distinct horizontal residues give disjoint tests. The variance of the count is therefore at most its mean, without any conditioning on the selector.

For $t\le q$, round points in the old real ball of radius $v=t-1-\sqrt m/2>0$. Its portion with every coordinate of absolute value strictly below $q/2$ rounds to eligible centered candidates. These candidates have raw norm at most $t$. At least half the ball volume remains. Indeed if $v\le q/2$ it all remains; otherwise the excluded fraction is at most $2m(V_{m-1}/V_m)(3/4)^{(m-1)/2}$ by slicing and $v\le q$. One has $V_{m-1}/V_m\le\sqrt m$ by the gamma integral and Cauchy–Schwarz. Unit cubes have volume one. Consequently $\Pr(T_d>t)\le\min(1,2q^{400}/(V_m v^m))$; the tail vanishes at and above $q$. Taking the $p$-norm of a shifted Pareto majorant gives (3).

For a fixed $i>1$ take $p=i-1$, $\ell_0=400\log q$ and run forward to $i-1$. With $t_d$ the right side of (3), set
$$
 \ell_d=\max\{\ell_{d-1}-\log\min(q,H_d,t_d),\quad
        (505/506)\ell_{d-1}-\tfrac12\log56.2142\}.               \tag{4}
$$
Use $\ell_0$ directly at $i=1$. Then $e^{-\ell_{i-1}}$ bounds the expectation of $1/D_{i-1}$ on eligible prefixes. To see this, start a random upper envelope $Y_0=1/D_0$. At each step take the minimum of $Y_{d-1}\min(q,H_d,T_d)$ and $\sqrt{56.2142}\,Y_{d-1}^{505/506}$. Every path passing the recorded caps has $1/D_d\le Y_d$ up to that step. Hölder gives $\|Y_d\|_{p/d}\le e^{-\ell_d}$ by induction, using $d/p=(d-1)/p+1/p$ and monotonicity of norms on a probability space for the Hermite alternative. At the last step this is the first moment. In particular $e^{\ell_d}$ from (4) is **not** a pathwise floor. Multiplying independent raw-void probabilities would give a different, unjustified calculation.

## The finite sum and the dual test

For each $(b,i,j)$, force the $j$ old-only winners, selected independently of column $i$ by the original signed tie rule in the old projections. Discard a prefix failing their caps. Put $n=506-j$, $P=\prod_{v=0}^{j-1} C_{k-v}$ and $u=\max(C_{k-j},K_b)$. The next positive-height vector is tested in a grid of rank $n$. Its height is at most $u<q$ so multiplication by the height permutes the mark group. The projected grid determinant times the projected mark order is the forced old determinant, at least $D_{i-1}/P$. The projected integer grid has covering radius at most $\sqrt{505+i}/2$ by ambient rounding. The inward half of a centered Voronoi cell about a radius-$u$ point fits in the ball of squared radius $u^2+(505+i)/4$. Pairing opposite heights cancels the factor of two. Averaging the fresh count and then using (4) gives the single-draw majorant
$$
 Q(h,X)=\sum_{b=1}^2\left[
 \frac{V_{505}(u_0+\sqrt{505}/2)^{505}}{2q^{400}}+
 \sum_{i=1}^h\sum_{j=0}^{k-b}
 V_{506-j}\big(u^2+(505+i)/4\big)^{(506-j)/2}P e^{-\ell_{i-1}}
 \right],                                                       \tag{5}
$$
where $u_0=\max(C_{h+b},K_b)$. The first term covers a flag entirely in the initial graph by testing a nonzero raw sign pair. This fresh test uses only prefix-measurable restrictions. Equation (5) bounds existence; it does not estimate the number of selected planes. Since (2) depends on the *actual* tail rank, the prefix bound in the first table sums (5) separately over draws 155 through the reported horizon and adds $5.412\cdot10^{-36}$ through 154. With the original monotone caps and pathwise floor, the horizon-154 radial tests contain every shorter flag; recomputation at $X_*$ gave $(5.41158017,5.41158018)\cdot10^{-36}$. [R65 counting argument and audit](wall1_enlarged_cutoff.md#audit)

Here are the single-draw upper sums as constraints are added. All radii in (5) are below 2861 for the new calculations through the first failed draws.

| $X,h$ | R65 sum | With (1) | Also with backwards caps | Also with (3) |
|---|---:|---:|---:|---:|
| $X_*,164$ | $2.180\cdot10^{-2}$ | $3.246\cdot10^{-10}$ | $9.972\cdot10^{-11}$ | $8.332\cdot10^{-13}$ |
| $a,171$ | $1.945\cdot10^{-1}$ | $2.898\cdot10^{-9}$ | $8.818\cdot10^{-10}$ | $5.052\cdot10^{-12}$ |

On the simultaneous dual-floor event, a rank-$k$ flag of covolume at most $B$ in the window at $i$ also requires
$$
 R_i\le \sqrt{g_{506-k}}\,(B/D_{i-1})^{1/(506-k)}.             \tag{6}
$$
Saturating can only decrease its determinant. The complementary dual section has covolume at most $B/D_{i-1}$ and inherits the raw dual minimum. Apply the same test to the backwards rank-$r$ section in each retained lattice of rank 505. Use the Part 172 radii $R_d$ and the **pathwise** floor $e^{L_d}$ from R65 when evaluating these necessary tests. At the first failed enlarged draw the largest term is $(2,48,0)$, of size $1.72049\cdot10^{-10}$ to $1.72050\cdot10^{-10}$. Here $k=120$, $R_{48}\in(0.01232,0.01233)$ and the right side of (6) at the floor is in $(0.02508,0.02509)$. At the first failed original draw the largest term is $(2,54,0)$, above $9.9471\cdot10^{-10}$. Across **all** choices of $(b,i)$ at those two draws, including backwards tests until (2) reaches $q$, the largest ratio of the dual floor to its test threshold is below 0.559 and 0.548 respectively. Thus these floor-only tests remove no terms at either crossing. The probability bounds in the first table are unconditional and incur no dual-exit charge. [Dual section and simultaneous floors](wall1_transference.md)

## What remains at 406

The original-cutoff prefix pays for all first-hit cases through 170 at a cost below $2.413\cdot10^{-15}$, or through 171 at a cost below $5.055\cdot10^{-12}$. Independently, the pre-step shell pays for wholly old first hits through 165 at a cost below $8.336\cdot10^{-13}$. These are overlapping options. For example it is sufficient to bound the wholly old first-hit mass on draws 171–406 plus $p_{\rm late}$ by $7.6330\cdot10^{-11}-2.413\cdot10^{-15}$. The mixed term on draws 403–406 and the vertical residual on draws 396–406 still require selected-history estimates. Neither full allocation follows. [Horizontal audit](wall1_z1_horizontal.md#audit) · [Pre-step shell](wall1_z1_old_planes.md#audit) · [Vertical audit](wall1_z2_vertical.md#audit)

The radial count continues to discard the conditional chance that the counted candidate and its subsequent old directions win together. R65 bounds the probability of a small *raw* plane through 406 by $10^{-604}$; such a plane is possible. A large raw lattice can still have a small projected quotient. The independent-Haar floor means sum to $(2.22022,2.22024)\cdot10^{-13}$ at $X_*$. Lean's plane mean integrates against Haar on a fundamental domain. It supplies no weight for these surviving finite flags. The $10^{-11}$ horizon at 406 and the allocations $p_{\rm old}+p_{\rm late}\le7.6330\cdot10^{-11}$ and $Z_{\rm rem}\le6.485\cdot10^{-11}$ remain conjectural. [R65 audit](wall1_enlarged_cutoff.md#audit) · [RankTwoPlaneMean.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankTwoPlaneMean.lean) · [Parts 190–196](../PROOF_GAP.md)

## Reproducing the certificates

For the rank-nine check write $A_j=v_j^2/\mathcal A$, where $\mathcal A$ is the **actual** terminal area. Thus $A_8 A_9=1$. The terminal split gives $576/X_*\le A_8\le 2/\sqrt3$. We prove $\prod A_j<373<e^{18(0.329)}$. For every consecutive block of length $l$, Hermite implies $A_j^{l-1}\le g_l^l\prod_{u=j+1}^{j+l-1} A_u$. Use the exact rank 2–8 constants and $g_9^9<881$ from the Part 82 caps. The initial upper bound $A_j\le5$ for $j\le7$ follows by the ordinary tail Hermite recursion with $d_2=1$ up to rank nine. Under the contrary product assumption each of those seven entries is at least $373/5^6$. The five rows below are homogeneous inequalities on squared lengths in consecutive projected subblocks. Their directions in the code are $w\cdot A\le0$. The last three are the **proved** versions in Theorems 6.1–6.2 of Pendavingh and van Zwam. [Part 82 inputs](wall1_small_d_caps.md) · [Published inequalities](https://doi.org/10.1137/060658795)

This standalone integer verifier retains both halves of every split. Its endpoints are in units of $10^{-4}$. The squared lengths range over the full real intervals. No mesh assumption on a lattice is used.

```python
from math import prod
from fractions import Fraction

S = 10_000
target = 373 * S**9
hermite = [0, 0, 4, 6, 12, 24, 64, 192, 768, 2643]  # 3 * cap for gamma_l^l
rows = []
for w in ([3,-4], [2,0,-3], [25000000,36000000,-48000000,-40000007],
          [50000,0,0,-20000,-80003], [400000,0,300000,-400000,-800005]):
    for start in range(10-len(w)):
        rows.append(list(enumerate(w, start)))

def ceildiv(a, b):
    return -((-a)//b)

def root(x, n):
    lo, hi = 0, 1 << ceildiv(x.bit_length(), n)
    while hi-lo > 1:
        m = (hi+lo)//2
        if m**n <= x:
            lo = m
        else:
            hi = m
    return lo

def check(lo, hi):
    for _ in range(24):
        before = lo.copy(), hi.copy()
        for i, j in [(7,8), (8,7)]:
            hi[i] = min(hi[i], ceildiv(S*S, lo[j]))
        for i, j in [(7,8), (8,7)]:
            lo[i] = max(lo[i], S*S//hi[j])
        for row in rows:
            low = sum(c*(lo[i] if c>0 else hi[i]) for i,c in row)
            if low > 0:
                return 1
            for i,c in row:
                if c > 0:
                    hi[i] = min(hi[i], ceildiv(c*lo[i]-low, c))
                if c < 0:
                    lo[i] = max(lo[i], (c*hi[i]-low)//c)
        for i in reversed(range(8)):
            v = 1
            for l in range(2, 10-i):
                v *= hi[i+l-1]
                hi[i] = min(hi[i], 1+root(hermite[l]*v//3, l-1))
        if any(x>y for x,y in zip(lo,hi)):
            return 1
        upper = prod(hi)
        if upper < target:
            return 1
        for i in range(9):
            lo[i] = max(lo[i], target*hi[i]//upper)
        if before == (lo,hi):
            break
    j = max(range(9), key=lambda i: Fraction(hi[i]-lo[i], hi[i]))
    mid = (hi[j]+lo[j])//2
    assert lo[j] < mid < hi[j]
    left, right = hi.copy(), lo.copy()
    left[j] = right[j] = mid
    return 1 + check(lo.copy(), left) + check(right, hi.copy())

assert check([1]*7+[5900,8600], [50000]*7+[11548,16600]) == 1715
```

For (5), use $V_0=1,V_1=2,V_n=2\pi V_{n-2}/n$. Start $\log g_l$ at $2\min(\mathrm{LCZ},\mathrm{Part65})/(10^9l)$ from Part 77, minimize against $2\log2+(2/l)\log(\Delta_l/V_l)$ at the Part 82 upper densities, set $g_{24}=4$ and propagate the Mordell minimum $\log g_l\gets\min(\log g_l,(l-1)\log g_{l-1}/(l-2))$ in increasing rank starting at 3. Use the fixed $56.2142$ in (4). For each $b,i$ initialize the summand weight to $e^{-\ell_{i-1}}$; multiply by $C_{k-j}$ after adding term $j$. Sum positive terms with 190-bit outward interval arithmetic. For the cumulative column, initialize at $5.412\cdot10^{-36}$ at draw 154. The resulting enclosures for the two successful endpoints are $(8.33506,8.33507)\cdot10^{-13}$ and $(5.05421,5.05422)\cdot10^{-12}$. The largest-weight term and the full finite sum are distinct calculations. [Part 77 integer table](wall1_lcz_all_widths.md) · [Part 82 density inputs](wall1_small_d_caps.md)

Three exact scratch checks exercise the new constraints. For the $E_{4a}$ Gram form in Table 6.1 of Pendavingh and van Zwam, successive leading determinant ratios are $1,3/4,2/3,1/2$. The resulting rank-four bound in (1) is attained. For the section formula enumerate ordered independent $x,y\in\{-1,0,1\}^3$ with nonzero height image in the last coordinate. Put $e=\gcd(x_3,y_3)$ and $z=(y_3x-x_3y)/e$. On all 576 pairs,
$e^2\|z\|^2=\|x\wedge y\|^2-(x_1y_2-x_2y_1)^2$, with $e^2\|z\|^2=\|x\wedge y\|^2$ on 192. Finally, over all 125 one-row three-column maps modulo 5, test $(x,y,z,1)$ with $x^2+y^2+z^2\le3$. The 27 candidates give count mean $27/5$ and variance $54/25$; two maps have zero count. This checks the disjoint and pairwise-independent contributions used in (3). [Exact Gram form](https://www.matroidunion.org/stefan/pdf/065879.pdf)

## Audit

**Verdict — SOUND.** Both unconditional prefix bounds hold for the width-506 restart. An independent scratch calculation used 224-bit outward-rounded intervals, factorial formulas for even- and odd-dimensional ball volumes, and the Part 77 and 82 cap tables. The draw-154 R65 sum at $X_*$ lies in $(5.41158017,5.41158018)\cdot10^{-36}$. Starting with its rounded upper bound $5.412\cdot10^{-36}$ and adding (5) once per draw from 155 gives the following enclosures. The last column concerns a single draw.

| Cutoff | Last draw $h$ | Cumulative majorant through $h$ | Majorant at $h+1$ |
|---|---:|---:|---:|
| $676\sqrt2$ | 164 | $(8.33506617,8.33506619)\cdot10^{-13}$ | $(1.81502251,1.81502252)\cdot10^{-9}$ |
| $1352/\sqrt3$ | 171 | $(5.05421448,5.05421450)\cdot10^{-12}$ | $(1.04882075,1.04882076)\cdot10^{-8}$ |

**What dominates R65.** At $X_*$ and draw 162, $(b,i,j)=(2,47,0)$ is the unique largest summand. It contributes $9.9653\%$ of the sum to four decimal places. Its $4.53082\cdot10^{-10}$ already exceeds the entire $10^{-11}$ budget. The $j=0$ terms together contribute $99.59077\%$ to five decimal places. Draws 48 through 162 account for exactly 115 further winner tests. The radial count at draw 47 drops their joint realization as well as the terminal area test on the realized plane. This is distinct from the older Part 192 diagnostic at draw 154 and column 38. [Part 192 audit](wall1_rank2_tail.md#audit) · [Part 197 audit](wall1_enlarged_cutoff.md#audit)

**Shortestness and the determinant.** Once the last used column is fixed, each later winner remains shortest among the competitors in the projected witness lattice. This allows the *same* Gram–Schmidt lengths to enter overlapping KZ inequalities. The rank-nine verifier covers the normalized terminal pair and both children of every split. It returned 1,715 nodes using the proved coefficients with their error allowances. Cutting the lifted flag by height and then pulling the section back one winner at a time gives (2) on every eligible prefix. For (4), the random variables $T_d$ can be dependent. Hölder applies to their successive products, and on the eligible prefix the random envelope bounds $1/D_d$ by the realized determinant identity. At $d=i-1$ this yields the required restricted first moment before exposing column $i$. The calculation still relaxes simultaneous selection of the counted vector and its successors. [Pendavingh and van Zwam, Theorems 6.1–6.2](https://www.matroidunion.org/stefan/pdf/065879.pdf)

**Dual test.** Using $L_{i-1}$ for the window at $i$ and $L_d$ for the retained lattice at $d$, the maximum floor-to-threshold ratios at draws 165 and 172 lie in $(0.55829258,0.55829260)$ and $(0.54745461,0.54745463)$ respectively. Both maxima occur in the rank-one terminal branch at window $i=3$. The scan includes all terminal ranks, last coordinates and backwards sections through the stopping rule in (2). No term is excluded at either crossing. The primal probability calculation needs no conditioning on the dual-floor event.

**Scaling to draw 406.** The single-draw sum grows by factors between 2,159 and 2,179 on the two steps from 164 to 166 at $X_*$, and between 2,054 and 2,077 from 171 to 173 at $a$. The loss compounds across draws even though the marginal factors decrease over these steps. There is also a direct obstruction at 406 without extrapolating either rate. The individual $(b,i,j)=(2,289,0)$ radial term at $X_*$ has radius below 1,538 and base-ten logarithm in $(631.60,631.61)$. At $a$, $(2,288,0)$ has radius below 1,411 and log in $(610.54,610.55)$. Each individual test still has height below $q$. Elsewhere in the sum the rank-two cap $C_{h+2}$ first exceeds $q$ at draws 179 and 188 respectively, where the all-terms justification for (5) also expires. Extending the same calculation to more draws cannot establish the 406 budget. A stronger bound on the joint selection of the flag, or another estimate supplying comparable suppression, would be needed. These diagnostics put no lower bound on the hit probability.

**Scope correction to the Part 197 summary.** A small raw plane through draw 406 has probability below $10^{-604}$ at $X_*$. It is possible, for example when two input columns vanish. The note and the Part 197 audit state this correctly. The enlarged-cutoff shell pays for wholly old first hits at $a$ through 165 by testing their predecessors through 164. That payment overlaps the direct $a$ prefix. The later horizontal and vertical allocations remain open.
