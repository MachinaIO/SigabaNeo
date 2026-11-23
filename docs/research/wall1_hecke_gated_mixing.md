# Effective Hecke mixing from the draw-406 dual gate

**Result.** For every gated draw-406 start, **46,595,465 independent uniform index-two steps suffice** for additive error at most $10^{-60}$ on the Lipschitz majorant below. The probability of a saturated plane of physical area at most $1352/\sqrt3$ in the determinant-matched randomized endpoint is then **below $2.19843\cdot10^{-58}$**. The step count is a sufficient upper bound. Its derivation counts overlaps of a real-group neighborhood, allowing a smoothing radius much larger than the available uniform injectivity radius.

**Scope.** This walk chooses every neighbor without conditioning and measures the endpoint after restoring the initial covolume. A walk conditioned to keep a fixed primitive vector has a different limiting behavior. For any fixed positive normalized area cutoff, every such path eventually has a plane below the cutoff. Neither calculation gives a probability bound on the original horizontal or vertical first-hit histories. [Earlier Hecke note and audit](wall1_hecke_randomization.md#audit) · [Parts 192–211](../PROOF_GAP.md)

## 1. The gate and the real-group neighborhood

Use row lattices, $X_n=\mathrm{SL}_n(\mathbb Z)\backslash\mathrm{SL}_n(\mathbb R)$, and Haar probability $\mu$. For a retained lattice $M$ of covolume $D$, write $x=D^{-1/n}M$. At $n=505$ the inherited dual floor and the determinant recurrence give
$$
 \lambda_1(x^*)=D^{1/n}\lambda_1(M^*)>
 e^{891.78/505}\,0.20090>1.1746 .
$$
We use the weaker floor $s=1$. By duality and Mahler compactness the closed set $K_s=\{x:\lambda_1(x^*)\ge s\}$ is compact. Raw-good bounds lengths in the raw graph. This calculation only uses the retained dual floor and the physical determinant lower bound. The gates apply to the start. [Part 205, inherited dual floor](wall1_doubly_gated.md) · [Part 186, audited determinant recurrence](wall1_quotient_slack.md#audit)

Let $V_n$ denote the volume of the Euclidean unit ball. Choose independent dual vectors $u_i$ at the successive minima $\ell_i$ of $x^*$. Minkowski's second theorem gives
$$
 \prod_i\ell_i\le 2^n/V_n,\qquad
 P=2^n/(V_n s^n),\qquad \ell_n\le sP .
$$
Use operator norm throughout. For $0<r\le1/8$ take the symmetric identity neighborhood
$$
 W_r=\{g:\max(\|g-I\|,\|g^{-1}-I\|)<e^r-1\}\subset\mathrm{SL}_n(\mathbb R).
$$
If $xg_1=xg_2$ for $g_i\in W_r$, then $h=g_1g_2^{-1}$ stabilizes $x$, and $h^{-T}$ stabilizes $x^*$. Both displacements from the identity have norm at most $2e^r(e^r-1)<4r$. If $r\le 1/(8P)$, each $u_i h^{-T}-u_i$ has norm less than $s$ and vanishes. The $u_i$ span the real space, so $h=I$. Thus $1/(8P)$ is a uniform lower bound for the injectivity radius in the specified neighborhoods. At $s=1$ it is $1.24479\ldots\cdot10^{-526}$.

**Overlap at a larger radius.** Fix one representative $g_2$ of a point of $x W_r$. Every other representative specifies a distinct $h$, determined by its action on the independent $u_i$. The possible images of $u_i$ lie in a ball of radius $4r\ell_i$ about $u_i$. Disjoint balls of radius $s/2$ give at most $(1+8r\ell_i/s)^n$ choices. Since $\ell_i/s\ge1$, the multiplicity is at most
$$
 J=\prod_i(1+8r\ell_i/s)^n
     \ \le\ J_0=(1+8r)^{n^2}P^n .
$$
This bound on the product avoids raising the longest-vector bound $sP$ to a power for every vector.

**Haar normalization.** Take $d\eta=\delta(\det g-1)\,dg$ with entrywise Lebesgue measure in the ambient matrix space. Its quotient covolume is $Z_n=\prod_{j=2}^n\zeta(j)<2^{n-1}$. Write $w=\eta(W_r)/Z_n$. An ambient cube $|C_{ij}-I_{ij}|<r/(8n)$ has $\|C-I\|<r/8$ and positive determinant. Its radial coordinate $t=(\det C)^{1/n}$ belongs to $(1-r/8,1+r/8)$, and $C/t\in W_r$ since both displacements are at most $(r/4)/(1-r/8)$. The radial formula $dC=n t^{n^2-1}dt\,d\eta$ bounds the cube's volume above by $\eta(W_r)(1+r/8)^{n^2}/n$. Hence
$$
 w\ge w_0=\frac{n}{2^{n-1}}
       \left(\frac{r}{4n(1+r/8)}\right)^{n^2}.
$$
The power $n^2$ comes from this conservative ambient cube bound. The local group dimension is $n^2-1$. [Venkatesh, *Geometry of Numbers*, Example 5.3.1 and Theorem 5.4.1](https://math.berkeley.edu/~fengt/245C_2016.pdf)

## 2. An explicit test and a two-sided discrepancy

Let $H(x)$ be the least saturated-plane area and $b=aD^{-2/n}$ for the physical cutoff $a$. Right multiplication by $g\in W_r$ changes $\log H$ by at most $2r$, by applying the exterior-square bound to $g$ and $g^{-1}$. Put $z=\log(H/b)$. Let $F$ equal one for $z\le 2r$, fall linearly to zero on $[2r,3r]$, and equal zero thereafter. Define
$$
 f(x)=\frac{1}{\eta(W_r)}\int_{W_r}F(xg)\,d\eta(g).
$$
Then $1_{H\le b}\le f\le 1_{H\le b e^{5r}}$ and $\mu f=\mu F$. Along $x\exp(tY)$ with $\|Y\|\le1$, $F$ is $2/r$-Lipschitz in $t$. Conjugation by $g\in W_r$ sends $Y$ to a matrix of norm at most $e^{2r}$. Thus $f$ is $2e^{2r}/r$-Lipschitz in the corresponding path metric. For $r=10^{-5}$ the constant is below $200005$. The argument requires no higher derivatives.

For the full-level normalized index-$p$ operator, use the mean-zero norm $\rho_p\le 2\sqrt p/(p+1)$. For an independent prime mixture one may average these bounds under its prime law. In particular the index-two bound works for any prescribed prime list or independent prime draws. [Clozel–Oh–Ullmo, Theorem 1.1, remark and §§4.7, 5.1](https://ullmo.ihes.fr/publications/COU-Invent.pdf) · [Full-level specialization](wall1_hecke_randomization.md#audit)

Push uniform group measure on $W_r$ forward by $g\mapsto xg$. Its probability density $d_x$ relative to $\mu$ is the multiplicity divided by $w$. Thus $\|d_x-1\|_2^2\le J_0/w_0-1$. Right equivariance of the Hecke correspondence gives $T^k f(x)=\langle d_x,T^k F\rangle$. Since $0\le F\le1$ gives $\|F-\mu F\|_2\le1/2$, one obtains uniformly on $K_s$
$$
 |T^k f(x)-\mu f|\le \tfrac12\sqrt{J_0/w_0}\,(2\sqrt2/3)^k .
$$
Consequently a sufficient number of steps is
$$
 k=\max\!\left(0,\left\lceil
 \frac{(\log J_0-\log w_0)/2-\log(2\varepsilon)}
      {\log(3/(2\sqrt2))}
 \right\rceil\right).
$$
For $s=1$, this is $O(n^2\log(n/r)+\log(1/\varepsilon))$. This measures the number of uniform correspondences. For $r=10^{-5}$ and $\varepsilon=10^{-60}$ the unrounded expression is $46{,}595{,}464.81770$ rounded upward to five decimal places. The inequality gives no lower bound on the actual mixing time and does not resolve whether ten million steps suffice.

## 3. The area probability and the two allowances

Let $p_D$ be the Haar probability of the physical area event and $U_D$ the mean number of its unoriented saturated planes. Part 192 gives $U_{D_*}<7.64067\cdot10^{-58}$ at the physical floor. The mean scales exactly as $a^n/D^2$. A point counted in the excess $F-1_{H\le b}$ has a plane in the shell $(b,b e^{3r}]$. Thus
$$
 T^k1_{H\le b}(x)\le p_D+U_D(e^{3nr}-1)+\varepsilon .
$$
Only the shell **mean** was scaled here. The scaling of a nonempty-event probability can differ. At $D_*$ the shell term is below $1.16638\cdot10^{-59}$. Using the Part 192 lower endpoint for $p_{D_*}$, shell and discrepancy together cost less than $0.06331\,p_{D_*}$. The Part 192 upper endpoint and monotonicity in $D$ give the uniform absolute upper bound $2.19843\cdot10^{-58}$ for $D\ge D_*$. The relative-error statement uses the floor only. [Part 192, probability enclosure and first moment](wall1_rank2_tail.md) · [Kim, sublattice mean formula](https://arxiv.org/abs/2005.10874)

Both $7.1275\cdot10^{-11}$ and $6.485\cdot10^{-11}$ exceed the randomized endpoint upper bound by more than $2.94\cdot10^{47}$. The former budgets horizontal histories after draws 155–171 have been charged. The latter budgets the remaining vertical histories on draws 396–406. Appending a transition leaves these original events measurable before any Hecke coins are drawn. A small conditional endpoint probability is consistent with an arbitrarily large probability of a prior event. Inserting a transition before those draws instead requires the ensuing joint law of the prefix, retained lattice, and finite displacement subgroup. The rank-three example in Part 195 already gives next-hit probabilities zero and $2/3$ with the same plane counts and mark-group order. [Part 193](wall1_z2_vertical.md) · [Part 195](wall1_plane_moment_recursion.md) · [Part 206](wall1_raw_section_compression.md) · [Part 210](wall1_distortion_sharpening.md)

## 4. What happens to a primitive mark

For a primitive physical vector $u$, an unrestricted random index-$p$ sublattice retains it with probability $c_{n,p}=(p^{n-1}-1)/(p^n-1)$. Surviving marks stay primitive because any divisibility in the sublattice would already hold in the parent. Thus for nested physical sublattices the probability of retention throughout $k$ steps is exactly $c_{n,p}^k<p^{-k}$. For the index-two count above this is below $2^{-46{,}595{,}465}$. An unrestricted path uses $k\log_2(2^{505}-1)$ bits of neighbor-choice entropy, approximately $2.3531\cdot10^{10}$ bits, and the physical composite index is $2^k$. These are combinatorial costs. No wall-clock reduction or lift cost follows.

**Conditioning changes the area law.** In determinant-one coordinates each retained mark has length $h_k=p^{-k/n}h_0$. For any primitive mark of length $h$ in a unimodular lattice, the orthogonal quotient has covolume $1/h$. Its shortest line lifts to a plane through the mark, giving
$$
 H\le\sqrt{\gamma_{n-1}}\,h^{(n-2)/(n-1)} .
$$
Indeed the area is $h$ times the projected length; saturation can only reduce area. Hence for any fixed $b>0$, every mark-retaining endpoint has $H\le b$ as soon as
$$
 p^{-k/n}h_0\le(b/\sqrt{\gamma_{n-1}})^{(n-1)/(n-2)}.
$$
This proves a deterministic obstruction for the normalized marked kernel. More generally a stationary probability on nonzero marks is impossible for this kernel since the radial coordinate contracts by a constant at every step. At fixed physical covolume this calculation compares shapes rescaled back to that covolume. Keeping the physical index-$p^k$ sublattice at its new covolume changes the normalized area cutoff as well.

The full space of unimodular lattices with a chosen primitive vector is an infinite-sheeted cover of $X_n$ with infinite invariant volume. Fixing the vector in real coordinates gives a different homogeneous space. Its stabilizer is conjugate to $\mathbb R^{n-1}\rtimes\mathrm{SL}_{n-1}(\mathbb R)$; at a coordinate mark the integral stabilizer yields a finite-volume quotient, with transverse lattice shape and a lift shear modulo integers. The determinant-normalized restricted transitions above move between radial fibers. Even a Haar law on one fixed fiber would give a conditional plane law depending on the length of its mark.

Randomizing only the lattice in the orthogonal complement of an already fixed prefix still changes the available projected points. If the relevant projected vector is a nonzero primitive point, the same hyperplane count applies in that rank. For a zero projection all information about its identity resides in the fiber of the projection. In either case the application requires a joint event: the projected output admits an allowed lift through the original prefix and the specified selection rule returns the required object. Endpoint area alone supplies neither condition. In Part 183 the independent plant enters the score separately from the unmarked geometry; identifying a primitive point of a retained lattice with that plant needs its own argument. [Part 183, score and terminal geometry](wall1_terminal_tail_047.md) · [Part 185, conditioning at a pivot](wall1_winner_alignment.md)

## Reproducing the constants

The following calculation is embedded so that the research note is the only added file. It evaluates analytic bounds and does not simulate a walk.

```python
from mpmath import mp

mp.dps = 80
n = 505
r = mp.mpf("1e-5")
eps = mp.mpf("1e-60")
half_n = mp.mpf(n) / 2
ball = mp.pi**half_n / mp.gamma(1 + half_n)
P = 2**n / ball
log_J = n*n*mp.log1p(8*r) + n*mp.log(P)
log_w = (mp.log(n) - (n-1)*mp.log(2)
         + n*n*(mp.log(r/(4*n)) - mp.log1p(r/8)))
steps = ((log_J - log_w)/2 - mp.log(2*eps)) / mp.log(3/(2*mp.sqrt(2)))
shell = mp.mpf("7.64067e-58") * mp.expm1(3*n*r)
upper = mp.mpf("2.07179e-58") + shell + eps
print(mp.nstr(1/(8*P), 15), int(mp.ceil(steps)), mp.nstr(upper, 15))
```

**Completeness.** The compact-start unmarked discrepancy, smoothing error, and primitive-mark obstruction are paper proofs. The numerical calculation uses the audited determinant and Haar enclosures as inputs. Both original residuals and the success cost under an alternative joint marked law remain open.

## Audit

**Verdict.** Confirmed for the unrestricted index-two walk with the endpoint rescaled to the starting covolume. The two-sided discrepancy applies to the averaged test $f$. The shell estimate gives a one-sided bound for the area event. The primitive-mark obstruction holds on every retaining path, with a threshold depending on the starting mark and the normalized cutoff.

1. **Compactness and overlap.** The physical determinant and inherited dual floors give $\lambda_1(x^*)>e^{891.78/505}\,0.20090>1.1746297$. Dualization is a homeomorphism, so Mahler compactness applies to $K_1$. If two representatives coincide in the quotient, their relative stabilizer moves each independent dual vector by less than $4r\ell_i$. At $r\le1/(8P)$ this is at most $s/2$ in the displacement bound, forcing the stabilizer to fix a real basis. The certified radius is $1.24479751278263\cdot10^{-526}$ to the displayed precision. At $r=10^{-5}$, packing the possible images separately and using $\prod_i(\ell_i/s)\le P$ gives the stated $J_0$. The determinant-fiber Haar normalization gives $Z_n=\prod_{j=2}^n\zeta(j)$. Integrating $n t^{n^2-1}$ over the radial interval of the ambient cube gives $[(1+r/8)^{n^2}-(1-r/8)^{n^2}]/n$, which verifies the factor $n$ in $w_0$. [Venkatesh, Example 5.3.1 and Theorem 5.4.1](https://math.berkeley.edu/~fengt/245C_2016.pdf)

2. **Discrepancy and step count.** Exterior-square distortion bounds the change in $\log H$ by $2r$. Conjugation in the group average gives the Lipschitz constant $2e^{2r}/r=200004.000040\ldots$. The pointwise proof only uses $\int d_x\,d\mu=1$, $d_x\le J_0/w_0$, and $\operatorname{Var}_\mu(F)\le1/4$. Thus it requires no higher-order Sobolev estimate for the piecewise-linear cutoff. At full level the paired-root bound for Smith type $(2,1,\ldots,1)$ contributes one factor $2\sqrt2/3$ per step. Rerunning the embedded calculation at 80 digits gives the unrounded count $46{,}595{,}464.81769106823\ldots$. The displayed discrepancy bound is $1.04933336\ldots\cdot10^{-60}$ at $k=46{,}595{,}464$ and $9.89320980\ldots\cdot10^{-61}$ at $k=46{,}595{,}465$. This verifies the ceiling for this estimate. [Clozel–Oh–Ullmo, Theorem 1.1 and §§4.7, 5.1](https://ullmo.ihes.fr/publications/COU-Invent.pdf)

3. **Endpoint probability.** Haar invariance gives $\mu f=\mu F$, so the shell in the mean ends at $be^{3r}$ even though the pointwise support bound for $f$ extends to $be^{5r}$. The shell indicator is bounded by the number of planes in that shell. Using the Part 192 enclosures, the shell costs at most $1.166374482693\cdot10^{-59}$. Adding $10^{-60}$ and the floor probability upper bound gives $2.198427448270\cdot10^{-58}$ rounded upward. Monotonicity of the base event and $D^{-2}$ scaling of the shell mean extend the absolute bound to every $D\ge D_*$. [Part 192 audit](wall1_rank2_tail.md#audit)

4. **Retention and forced area.** Conditional on survival so far, the vector still has nonzero reduction modulo two. Of the $2^{505}-1$ hyperplanes, exactly $2^{504}-1$ contain that reduction. Multiplying the conditional probabilities proves strict retention probability below $2^{-46{,}595{,}465}$ at the stated count. On every surviving path the normalized length is $h_k=2^{-k/505}h_0$. The quotient by that primitive line has covolume $1/h_k$, hence its shortest line gives $H\le\sqrt{\gamma_{504}}\,h_k^{503/504}$. For each fixed $h_0,b>0$, the same threshold in §4 works for every path. An arbitrary primitive mark can have unbounded initial length even in one lattice, so a common numerical threshold for all marks would require a length bound.

5. **Alternative walks.** Uniform superlattice steps have the adjoint unmarked operator and inherit the same endpoint discrepancy. Every physical old vector survives, but its determinant-normalized length grows by $2^{1/505}$ per step and it can lose primitivity when the superlattice contains its half. At the unrescaled physical cutoff, any pre-existing qualifying plane persists by saturation. The determinant-matched estimate instead tests a changing physical cutoff. In neither comparison does membership alone identify the selected vector or give a lift of a new winner to the original lattice. [Part 213](wall1_hecke_randomization.md)

   A bounded factor only requires control of the particular observable. Part 209's $6.9\cdot10^6$ applies to the sum of two rank-504 quotient **means** over eleven draws. Part 210's $3329^{13.48}$ concerns a terminal **area probability**. Neither is a bound on the density of the whole finite-step law relative to Haar, since that law has finite support from a fixed start. Merely relaxing the absolute tolerance to $6\cdot10^{-11}$ in §2 while keeping its radius and prefactor still gives $46{,}593{,}519$ sufficient steps. This calculation neither excludes a shorter event-specific estimate nor supplies the required joint comparison for the original histories. [Part 209](wall1_zrem_flag_moment.md) · [Part 210](wall1_distortion_sharpening.md)
