# A reachable draw-2 exit for the small-radius void fraction

Under the unconditioned 400-row marginal, there are draw-2 histories with
$$
 b_2 \ge \frac{752418912}{2529270911}>0.2974.
$$
The family below has probability less than $10^{-6689}$. This proves that
even at draw 2 the threshold $0.273$ requires an exceptional set. The
requested upper bound $3.64\times10^{-12}$ on the probability of an exit
through draw 404 remains open.

## The radius at draw 2

Write $q=3329$, $n=506$, $V_n=\pi^{253}/253!$, and $g_i$ for
the incoming window GH length. Distinguish the Part 246 **fraction** $b_i$
from the Part 230 **radius** indexed by offset one. In the notation of those
parts, if $M_i\subseteq K_i$ is the retained lattice inside the projected
integer grid, then
$$
 r_i^2=(1.10\,g_i)^2 S_i^{-2/n}-2,\qquad
 b_i=\Pr_{z\in K_i/M_i}\{\operatorname{dist}(\tilde z,M_i)>r_i\},
 \qquad S_i=\min(q,\sqrt{56.2142}\,V_n^{1/n}g_i).
$$
The mark is uniform conditional on the incoming history. These formulas are
for the height-one test. [Two-mark inequality](wall1_inductive_typicality.md)

The first window is integral with determinant $q^{400}$. Its first
winner has length $1\le s_1\le q$, the upper bound coming from a
sample period. Thus $g_1=(q^{400}/V_n)^{1/n}$ and
$g_1 q^{-1/n}\le g_2=g_1s_1^{-1/n}\le g_1$. In particular
$S_2>1$, and $r_2<1.10\,g_1<3672$. For the last inequality one
can check the integer comparison obtained by clearing denominators in
$$
 (11/10)^{506} q^{400} 253!
 < 3672^{506}(31415/10000)^{253},
$$
using $31415/10000<\pi$.

## A family with independent surviving sample coordinates

Suppose at least 18 sample rows vanish on all 106 inputs present at the
first freeze (105 initial columns and the first appended column). Designate
18 of these rows as $J$. Every first-window graph vector has coordinates
in $q\mathbb Z$ on $J$. A shortest vector of length at most $q$
with a nonzero coordinate on $J$ must therefore be a signed coordinate
period on a single such row. Consequently there is a set $T\subset J$
of 17 rows on which the selected vector vanishes, for every tie outcome.
Choose $T$ using only the first-window history.

Projection off the winner fixes those 17 coordinates. Every retained
lattice point still has coordinates in $q\mathbb Z$ there. A fresh
sample column represents a uniform incoming mark, and its balanced
residues $X_j$ on $T$ are independent uniforms on
$\{-1664,\ldots,1664\}$, conditionally on that history. Hence
$$
 \operatorname{dist}(\tilde z,M_2)^2\ \ge\ Y:=\sum_{j\in T}X_j^2 .
$$
The inequality holds simultaneously for all representatives because
adding a retained vector changes these coordinates only by multiples of
$q$. The row condition is on the exposed sample matrix and leaves the
fresh column unrestricted. [Marginal law and coordinate sections](wall1_fresh_review.md)

For one balanced residue the second moment is $(q^2-1)/12$ and the
variance of its square is $(q^2-1)(q^2-4)/180$, by summing squares and
fourth powers. Put $d=\mathbb E Y-3672^2=2216256>0$. The one-sided
Chebyshev inequality gives
$$
 b_2\ \ge\ \Pr(Y>3672^2)
 \ \ge\ \frac{d^2}{d^2+17(q^2-1)(q^2-4)/180}
 =\frac{752418912}{2529270911}.
$$

## Probability under the specified marginal

The number of rows satisfying the condition has distribution
$\mathrm{Bin}(400,q^{-106})$. Writing $E$ for the event that at
least 18 do, a fixed set of 18 rows gives the lower bound and a union over
sets of that size gives the upper bound
$$
 q^{-1908}\le\Pr(E)\le {400\choose18}q^{-1908}<10^{-6689}.
$$
Every history in $E$ exits at draw 2. The upper bound here applies only
to $E$. Part 230 controls a subsequent miss given the current void
profile, and Parts 243–244 supply fresh marks on specified sections.
Neither implication bounds the probability of large $b_i$ on the
complement of $E$. That complementary probability, including first
exits after draw 2, is the missing term. [Generalized deletion](wall1_generalized_deletion.md) · [Part 246](../PROOF_GAP.md)
