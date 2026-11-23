# High-order production frontier and completion counting

The companion `wall1_high_order_frontier.py` captures the actual return locals
of `wall1_larger_triangular_components.actual_parameters`, rather than
substituting a different cap, an excluded-family diagnostic, or a handpicked
anchor. It reconstructs every competing cover for each reported stratum,
checks that the selected interval agrees with `refined_strata`, and reports
all selected-cover components. It separately reconstructs the underlying
one/two-relation remainder candidates and their actual leading terms.
No production source is edited.

## What the completion factor means

In the two-relation remainder at support size h and rank r, after selecting
an anchor and enough additional free basis points, there remain

    k=h-r-2

points assigned freely in an affine span of dimension d=r-1. The present
count uses q^(d*k). The script prints d*k and d*k*log10(q) exactly as a
positive contribution to the logarithmic upper bound. This is not the
logarithm of the entire bound: anchor membership, the free-basis ball masses,
the witness choice factor, and the signed-moment transfer coefficient remain
separate. For a three-relation extension the analogous unrestrained
completion count is q^((r-1)*(h-r-3)).

A uniform affine-slice bound C_d <= q^d immediately replaces the two-relation
factor by C_d^k, since each dependent point must still lie in the ball.
If the certified per-point log10 ratio is g_d=log10(C_d/q^d), the maximum
change supplied by this replacement in a fixed two-relation term is k*g_d.
The minimum among valid covers can be recomputed afterward; the improvement
of a non-selected candidate alone is not a global reduction.

## Why basis witness multiplicity alone cannot close a very large deficit

For the existing two-circuit/basis witness format, a witness is determined by
three subsets of the h labels: its first circuit support, second circuit
support, and chosen extra basis labels. There are at most 2^(3h)=8^h such
triples. On an actual configuration, normalized circuit coefficients and
basis coordinates are determined, so the q-power counts alternative point
assignments, not additional witnesses of that fixed configuration.

Consequently the specific method of dividing the existing witness upper
bound by a justified uniform multiplicity of these label-subset witnesses
cannot improve it by more than 3h*log10(2) decimal orders.
At h=24 this generous absolute ceiling is about 21.675 orders, even before
accounting for divisions already present. It cannot by itself remove an
upper-bound excess of more than two hundred orders. This is a ceiling for
that particular division method, not an impossibility theorem for more
powerful geometric, probabilistic or differently structured counting methods.
The large residual numbers are coarse upper bounds, never lower bounds on
actual incidences. Sharpening the Gaussian estimate itself or reweighting
witnesses using geometry is not constrained by this multiplicity argument.

## Concrete next lemma: weighted completion mass

Let X be the random/free anchor-and-basis data in a fixed witness branch,
with its existing nonnegative weight w(X), including the indicator of every
anchor ball constraint. Let A_X be the resulting r-1 dimensional affine
slice over F_q, and let B_R be the centered-residue Euclidean ball. Define

    C(X) = | A_X intersect B_R |.

The required replacement at this branch is the weighted bound

    integral w(X) * C(X)^k dX <= M_{h,r,anchor},

instead of

    q^((r-1)*k) * integral w(X) dX.

A uniform bound uses C(X)<=C_d and is already sufficient for a valid local
improvement. To obtain stronger averaged savings, the expectation must use
the same weighted distribution of X that includes the anchor constraints.
A statement for a uniform, independently sampled affine slice cannot simply
be substituted: short-anchor conditioning changes that distribution.
Distinctness and exact rank restrictions may be retained in the completion
count for further savings, or dropped for a conservative bound. Existing
covered-family addbacks and every theta/periodic tail remain necessary.

This is a precise new quantitative obligation, not a proved small bound for
M. It identifies the place where simultaneous geometry of the many dependent
points has to enter, rather than counting all field coordinates freely.

## Captured production result (Part396 snapshot)

The completed run `/tmp/wall1_high_order_frontier.log` used the production
functions imported before the subsequent uniform ball-completion and D24-six
changes. It reproduces total logs 17.1698920070702, 51.2341232389501 and
226.846947674638 for h=18,19,24 respectively. Every reported selected cover
agreed with its actual `refined_strata` interval. These are upper bounds,
not actual error estimates.

| h | Leading rank/girth | Nullity h-r | Leading stratum log10 | Leading (c,t,a) | Extra free basis points |
|---|---|---:|---:|---|---:|
| 18 | 11/5 | 7 | 17.1667894118343 | (5,8,4) | 0 |
| 19 | 11/5 | 8 | 51.2325715205191 | (5,8,4) | 0 |
| 24 | 12/4 | 12 | 226.846923049576 | (4,10,3) | 0 |

For h18 and h19 the original cover wins: there is no special addback hiding
the leading girth-five bound. Its two-relation minimum wins over the
one-relation logs 145.7925 and 179.7913. The next rank/girth stratum is 11/7,
with logs 14.6952465 and 48.7610286. At h18 the next two are 9/5 and 9/4;
at h19 they are 11/6 and 10/4.

For h24 the D31-eleven cover wins, but its remaining two-relation term is
226.8469230 while the largest addback, other-two-four, is only 186.5259539.
Thus another local addback improvement would not address this leading term.
The next strata are 12/5 (222.3278268), 13/4 (222.2658317), 12/7
(219.8562837), 11/5 (219.8229137), and 12/6 (218.6351584). The dominant ranks
are near half the support size, and nullity is large.

| h | Anchor union H=c+t | Affine dimension d=r-1 | Unconstrained points k=h-r-2 | Old q exponent dk | log10(q^(dk)) |
|---|---:|---:|---:|---:|---:|
| 18 | 13 | 10 | 5 | 50 | 176.115689757833 |
| 19 | 13 | 10 | 6 | 60 | 211.338827709400 |
| 24 | 14 | 11 | 10 | 110 | 387.454517467233 |

In all three leading branches H=r+2. The two circuits already span the
entire rank, leaving no extra free-basis points. Nevertheless the final
5,6,10 points are charged by all affine-span coefficients. This specifically
identifies the weighted-completion lemma above as a useful next target.

Using the separately proved `wall1_ball_slice_completion.completion_bound`
with the same parameters gives fixed-branch shifts -0.702307901833,
-0.842769482200 and -3.265022123906. Thus the resulting leading branch logs
are approximately 16.46448151, 50.38980204 and 223.58190093. These are
branch diagnostics, not a recalculation of the global sum. The uniform
improvement is valid but far too small to close these particular bounds.
For example the h24 branch alone needs a gain above 226.8469 orders just to
fall below one; its current ten-point uniform gain is 3.2650 orders.

The diagnostic script has subsequently been made compatible with D24-six
and the captured `completions` dictionary, and disables line tracing while
retaining return-local capture. The full numerical log above belongs to the
prior snapshot; these compatibility edits passed a Python compilation check
but were not used to claim a second complete production run.
