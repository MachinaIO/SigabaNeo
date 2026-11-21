# How long can a canonical q-prefix survive exact BKZ?

For the Part 39 embedding, at widths 646 and 647 the largest persistent prefix of a fully exact-BKZ-reduced basis has **length zero, deterministically**. At widths 406 and 512 we can certify long initial segments of the *first scan*. For the completed reducer we obtain upper bounds of 105 and 22 rows, respectively. The exact high-probability lengths at these latter widths remain open. In particular the 377 deleted axes in the dimension-647 certificate cannot be explained by their persistence in BKZ-647.

## A concrete scan and its pathwise invariant

Use zero-based row indices, sample axes first. Take the integer basis with rows $(q e_i,0,0)$, then $(-A_j,e_j,0)$ for the secret columns, then $(b,0,1)$, using centered representatives. Let $H_{i,l}(B)$ be the integer span of rows $i$ through $i+l-1$ after orthogonal projection away from the first $i$ rows. This is exactly the lattice of `blockAt` in [Slide/SVP.lean](../../SigabaNeo/Lib/Lattices/Reduction/Slide/SVP.lean).

Specify the following exact BKZ scan. Use [firstInsertion](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Tour.lean) with $\delta=1$, $l=\min(\beta,d-i)$ and the first unit coefficient as incumbent. On strict improvement insert the returned coefficient row by a unimodular change inside the window, and restart the scan. For definiteness choose the completion of least sum of squared entries, breaking ties lexicographically in row-major order. A shortest coefficient row is primitive, hence completable. On equality use the identity. These choices specify a variant without preliminary LLL. [BKZ.Reduced](../../SigabaNeo/Lib/Lattices/Reduction/BKZ.lean) is an output predicate. Our completion and restart policy are additional algorithm choices.

Termination follows because the tuple of squared prefix determinants in row order decreases **lexicographically**: earlier cuts are unchanged and the cut after the inserted head decreases strictly. Each entry is a positive integer by Cauchy–Binet. This proves finite termination for any of the local completions above. A clean scan satisfies full overlapping BKZ reducedness, including the truncated end blocks.

**Invariance lemma.** Suppose the first $k$ rows initially are the indicated $q e_i$. They survive unchanged through a sequence of scans if at every visited head $i<k$, while the prefix is intact, $\lambda_1(H_{i,l}(B))\ge q$. Conversely the first strictly shorter call at such a head destroys that row. Indeed its incumbent projects to itself and has length $q$, so the displayed inequality is equality. The strict comparison in `best` retains the seed on ties and the update is the identity. Updates at $i\ge k$ leave all protected rows untouched. Induction proves the assertion, and on a shorter call the new head has projected length strictly below $q$. This is an equivalence for uninterrupted persistence, not a test for a row to reappear later.

For slide, this argument applies to an individual primal call under the identity-on-tie update. [Slide/Update.lean](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Update.lean) normalizes disjoint blocks, permits unimodular completions, and can update a shifted block using a reciprocal SVP witness. Its `slidePass` chooses a pass by existence. A primal seed tie alone constrains neither the other rows of its completion nor a shifted dual update crossing the cut. The overlapping-BKZ conclusions below concern the specified BKZ reducer.

## What the first scan actually certifies

An all-sample canonical window has minimum $q$. In a mixed canonical window starting at a sample axis, ending before the height, write $r=m-i$, $h=\beta-r>0$. The projected window is precisely the rank-$\beta$ lattice of $(x,y)\in\mathbb Z^r\times\mathbb Z^h$ with $x=-A' y\pmod q$, for an iid $r\times h$ submatrix. The omitted coordinates are zero in the projection. Each signed nonzero pair of length strictly below $q$ with $y\ne0$ has membership probability $q^{-r}$, since $y$ is nonzero modulo $q$. There is no competitor with $y=0$. The expected pair count is therefore exactly
$$
 [N_\beta(q^2-1)-N_r(q^2-1)]/(2q^r),
$$
where $N_j(J)$ counts integer points of squared norm at most $J$. It gives an upper bound on the probability of a shorter vector. It is not generally the probability itself.

Bounding the numerator by the volume of the radius-$q+\sqrt\beta/2$ ball (disjoint unit cubes), then summing geometrically over canonical heads down to $r_0$, gives failure at most $V_\beta(q+\sqrt\beta/2)^\beta/[2q^{r_0}(1-q^{-1})]$. Here $V_j=\pi^{j/2}/\Gamma(1+j/2)$. Until the first insertion all these calls see the original basis. With $m=511,n=512,q=3329$ the following are the longest initial runs certified at 99% by this **cube and geometric-sum bound**. The entries follow by taking logarithms, rounding the bounds upward. No row in these mixed windows uses the height.

| Width | Last $r_0$ | Initial heads passed ($512-r_0$) | Failure upper bound |
|---:|---:|---:|---:|
|406|327|185|0.00402|
|512|405|107|0.00477|
|646|502|10|0.000516|
|647|503|9|0.0000511|

A later insertion to the right can change the last rows of an earlier window while preserving its head. The proof would have to count the new sublattice to apply the invariance lemma on restart. Applying the canonical-window probability a second time has no justification. At widths 646 and 647 at least one insertion ultimately reaches head zero on every input, even when its initial call passed.

## A deterministic obstruction at the fixed point

Here is a reproducible head bound from the block Hermite inequalities of [Part 6](wall1_prefix.md). For any fully reduced rank-$N$ basis let $S$ be its log base-two covolume and $g$ its first length. Define $F_1=0$ and require $\log_2 g\le S/N+F_N$. The projected suffix of any length inherits reducedness. If its log determinant is $T$ and its rank is $j$, removing its head leaves mean log determinant at least $T/j-F_j/(j-1)$ for $j>1$. Starting with the suffix after the first row, iterate this inequality to lower-bound the determinant remaining after $l$ rows. Combining it with Hermite on the first $l$ rows gives the valid recurrence
$$
 F_N=\min_{2\le l\le\min(N,\beta)}
 \frac{N-1}{N(l-1)}\left(C_l+(N-l)\sum_{j=N-l+1}^{N-1}\frac{F_j}{j-1}\right),
$$
where $C_l\ge(l/2)\log_2\gamma_l$ and the whole sum term is zero for $l=N$. Indeed $l\log_2 g$ is bounded by $C_l$ plus the initial block log determinant, which equals $S$ minus the remaining log determinant. Substitution and isolation of $\log_2 g$ give the formula. All coefficients used on prior bounds are nonnegative.

If row $k-1$ is the last of $k$ leading sample units scaled by $q$, project away its predecessors. The resulting rank is $N=1025-k$, the determinant is $q^{511-k+1}$, and its head has length $q$. The recurrence therefore requires $513\log_2 q\le NF_N$. This argument applies to every fully reduced basis with that prefix, regardless of scan history or the planting.

| Width | Ambient head upper bound (rounded up) | Largest $k\in[0,511]$ passing this necessary test |
|---:|---:|---:|
|406|8627|105|
|512|3990|22|
|646|2138|0|
|647|2131|0|

For reproduction use the following outward-rounded integer recurrence with $M=10^8$. Blichfeldt's bound from Part 6 gives the displayed choice of $C$ in scaled units. Ceilings in its initialization can equivalently use an upper endpoint from high-precision interval arithmetic.

```text
C[l] = 1 + ceil(M*(l/2*log2(2/3.14159) + log2(Gamma(2+l/2))))
f[1] = 0
for N = 2,...,1024:
    a = 0
    for l = 2,...,min(N,width):
        if l < N: a += ceil(f[N-l+1]/(N-l))
        v[l] = ceil((N-1)*(C[l]+(N-l)*a)/(N*(l-1)))
    f[N] = min(v)
F[N] = f[N]/M
```

## The suffix and the terminal call

While $k$ sample rows persist, their orthogonal quotient is *exactly* the punctured Part 39 lattice, by extension of every deleted sample in its prescribed residue class. It has dimension $1024-k$ and determinant $3329^{511-k}$. This identifies the entire quotient, independent of the basis chosen within it. In the original canonical basis the remaining GS lengths are $511-k$ copies of $q$ followed by 513 copies of one. These latter unit lengths follow by projecting off the sample coordinates and then preceding unit directions. They are initial GS data. They establish no unit tail or slope for a reduced basis.

Even at the deterministic upper limits above, a completed BKZ-406 output would leave at least 919 dimensions, hence at least 513 further prefix directions before its terminal window. BKZ-512 leaves at least 1002 dimensions, hence at least 490 further directions. Their selection law remains uncontrolled. In general if a predetermined plane persists with probability at least $1-\epsilon$, an unconditional fixed-plane failure bound $h$ costs at most $h+\epsilon$ jointly with persistence as a success requirement, by a union bound. Conditioning on successful persistence can bias the punctured design.

Freezing 377 prescribed axes by algorithm design and using one terminal call gives width 647 and success at least 0.9951664 by [Part 39](wall1_projected_reference.md). This is full-dimensional SVP in that quotient. For ordinary fully reduced BKZ the hypothesized prefix is impossible at that width. No smaller width for the full reducer follows, and no necessary middle-region width for recovery is established here. The many-plane result of [Part 40](wall1_finite_family.md) and early capture concern different success mechanisms. The fixed-point obstruction rules out a particular selection explanation, without giving a lower bound on attack cost.
