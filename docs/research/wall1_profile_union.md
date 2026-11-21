# What the Part 6 profile tests about a divisible projection

The last-block shortest-vector argument proposed for discarding Part 41 witnesses is invalid. There are two different tests here. Intrinsic BKZ tests projected vectors *in the prefix*. At its last index that lattice has rank one. The full-dimensional Part 6 profile also tests inequalities across the prefix boundary, using the remaining determinant. Even these latter inequalities can admit many divisible projections. The following results concern the geometry of these tests.

## The bound that follows for the Part 41 pencil

Use one-based indexing. Fix the horizontal flag, let $V=V_{k-1}$, let $P$ be orthogonal projection off $V$, and write $h=\|Pb_k\|>0$, $H=\det V$. In the displayed basis the last spacing is exactly
$$
 t_a=\|Pu+aPb_k\|,\qquad \det B_a=Ht_a .
$$
Every vector of $B_a$ outside $V$ has projected norm at least $t_a$. In particular a shortest-vector test at the last index gives **equality for every integer $a$**. At an earlier start, a short vector from $V$ can win the block even when $t_a$ is large. Indeed if $t_a$ exceeds every preceding spacing, adjoining this generator to the indicated HKZ prefix preserves all its intrinsic HKZ tests. At each earlier start, vectors with nonzero last coefficient have norm at least $t_a$ after projection, and the old truncated block was already reduced. Size reduction by preceding rows preserves these statements. Thus increasing the last spacing eventually makes intrinsic reduction automatic in this very pencil.

For any *independently justified* ceiling $t_a\le G$, put $c=\langle Pu,Pb_k\rangle/h^2$ and $r^2=\|Pu\|^2-c^2h^2$. Completing the square gives
$$
 (a+c)^2\le (G^2-r^2)/h^2 .
$$
There are zero solutions for $G<r$, and otherwise at most $1+\lfloor2\sqrt{G^2-r^2}/h\rfloor$ before excluding $0,\pm1$. This counts distinct members of one pencil. The Part 6 terminal cumulative ceiling $X_k$ supplies $G=X_k/H$ for **any** ordering, by invariance of determinant. A bound on a particular basis's final spacing supplies $G$ directly only when its preceding plane is the indicated plane. Two upper bounds on successive partial sums do not imply an upper bound on their difference given by the difference of the ceilings.

One can impose a stronger intrinsic-profile filter by requiring a completion of the log spacings to all Part 6 inequalities with total log determinant fixed. For the displayed ordering this gives, for example, a ceiling using all $b=d-k\le\beta$ suffix spacings. With $c_j$ the Part 6 constants in natural logs, the length-$b$ block starting at $k$ gives
$$
 (b-1)\log t_a\le b c_b+\sum_{i=k+1}^{k+b-1}\log g_i .
$$
The missing final log spacing can be bounded below by the Part 6 ratio propagation from $t_a$, say $\log g_d\ge\log t_a-p_k^{(d)}$. Substitution of the total determinant yields
$$
 (b+1)\log t_a\le \log(D/H)+b c_b+p_k^{(d)} .
$$
Here $b\ge2$. This is a necessary condition for that ordering. Taking a maximum spacing in a different reduced basis and identifying it with $t_a$ would require another argument.

There is also a basis-independent use of genuine per-index upper bounds. In any reordered basis of $B_a$, take the first row outside $V$, at index $j$. Its component normal to $V$ is a nonzero integer multiple of the displayed last generator's normal component. Its GS projection removes only a subspace of $V$, so $g_j\ge t_a$. Hence if the filter proves $g_i\le G_i$ for every admitted ordering, one may use $G=\max_{1\le i\le k}G_i$ in the pencil count. It is the first exit from $V$ that proves this assertion. The final row need not be the exit row.

## Integral counterexample even with full inequality completion

Fix $k\ge1$, $b=d-k\ge3$, and use mutually orthogonal unit coordinate axes. Let the ambient lattice have $k+2$ unit generators and $b-2$ generators scaled by an integer $M\ge2$. Mark $u=e_{k+1}$, take $b_k=e_k$, and use the first $k-1$ unit vectors for $V$. For every integer $a\ge2$ with
$$
 (1+a^2)^{b+1}\le M^{2(b-2)}
$$
the sublattice $B_a$ passes the stronger profile filter. Indeed its displayed basis is orthogonal with nondecreasing spacings $1,\ldots,1,t$, $t=\sqrt{1+a^2}$, hence HKZ. Append $b$ formal spacings all equal to $(M^{b-2}/t)^{1/b}\ge t$. Their product with the prefix determinant is exactly the ambient determinant. Every local Part 6 inequality holds since a block's first log spacing is at most its mean. Consequently all Part 6 cumulative ceilings hold as well. The completion used here is a sequence of positive numbers. Lattice realizability of its suffix is unnecessary for this profile filter.

The shear defining $B_a$ is primitive and the quotient class of $u$ is $-a[e_k]$, with $[e_k]$ primitive. The subgroups are distinct by their height-one slices on coordinate $k+1$. With $M=2^{40}$, $b=5$, every $2\le a\le 2^{20}-1$ passes (the condition $s\ge t$ is sufficient, not exact). An ambient block extending one row further could detect the short projected $e_k$ if that direction were included in that block. An intrinsic block cannot make this comparison. This example is deterministic and makes no assumption on random orientations. It is not a draw from the specified ensemble.

An exact integer certificate for the example bracketing the largest admissible $a$ is

```python
from math import isqrt
# b=5: (1+a*a)^6 <= M^6 iff 1+a*a <= M.
M = 2**40
a = isqrt(M-1)
assert a == 2**20-1
assert (1+a*a)**6 <= M**6 < (1+(a+1)**2)**6
```

## Scope of the discrete mean

For the off-line stratum alone, the Part 41 identity admits an exact deterministic filter. In its HNF enumeration retain only subgroups admitting a basis satisfying the chosen profile test. This predicate depends on the integral subgroup, the ambient determinant and the width. Within the reduced cylinder retain precisely the competitor representatives whose projection lies outside the real line of the projected plant. Writing $C_B^{\rm off}$ for this set, the conditional summand is $J_B(U_B)-J_B(U_B\cup C_B^{\rm off})$. This counts each bad subgroup once, including a subgroup that also has a divisible projection. To count disjoint strata, exclude the divisible case separately. The modular rank and consistency tests in every term remain necessary. For example, for the full shape and widths 406, 512 and 647 the prefix ranks are 618, 512 and 377. An off-line competitor increases the rational rank after shearing by one: its vector is outside the span of the prefix and the plant, and the shear has exactly the plant line as kernel. Thus a consistent prefix-plus-competitor tuple must lose at least 107, 1 and 0 joint ranks respectively modulo the prime. For the punctured dimension 647 the corresponding ranks are 241, 135 and 0; there is no forced loss from the 512-column bound. These statements are dimension counts, not estimates of the number of surviving tuples.

For the empty prefix the count of bad prefixes is a single indicator. Part 39's capped conditional estimate therefore already bounds its mean by 0.00483352 at punctured width 647. Part 30 covers containment under ambient uniqueness when $k\le\beta$, which includes all three punctured cases and the latter two full-dimensional cases. Neither assertion bounds the filtered off-line sum at positive rank. Terminal identification and lifting also have different hypotheses.

The counterexample disproves a general inference from the profile to absence of multiples. The pencil ceiling bounds a specified flag and ordering; it gives neither an all-design construction nor an exclusion theorem for the concrete full ensemble. The positive-rank filtered means and their minimum certifying width are undetermined here. The existing full-width 1024 and punctured full-width 647 certificates apply to their respective experiments.

[Part 6](wall1_prefix.md) · [Projected-line criterion](wall1_planted_flags.md) · [Containment](wall1_contained.md) · [Puncturing](wall1_projected_reference.md) · [Part 41 discrete mean](wall1_sublattice_union.md)

**Audit note.** The integral example is a logical counterexample only: it is not q-ary, its plant is not uniquely shortest,
and its suffix completion is formal. At the real parameters (β = 406, k = 618, d = 1024, det 3329^511), the displayed-ordering
completion bound limits the pencil spacing to t_a ≲ 2^5.8, so at most dozens of values of a survive in that pencil — far from
the 2^635 witnesses of Part 41's determinant-only family. The existential "some basis passes" filter remains open.
