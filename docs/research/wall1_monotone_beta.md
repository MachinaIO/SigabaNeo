# Success at adjacent block sizes

A single size-reduced basis can be fully exact BKZ-reduced at widths two and three, recover the unique ambient shortest pair at width two, and miss it at width three. Even coupling the two outputs to have identical basis rows would therefore be insufficient on general Euclidean lattices. There is a separate logical issue for the planted model. Upward monotonicity alone can propagate a *lower* success bound only toward larger widths. To propagate the full-width certificate downward one needs a quantitative bound on the loss.

## A fixed basis and a strict reversal

Use orthonormal coordinates in dimension five. Write the following vectors as rows, omitting trailing zero coordinates:
$$
 b_1=(1),\quad b_2=(1/2,\sqrt{3}/2),\quad
 b_3=(1/2,1/(2\sqrt{3}),\sqrt{2/3}),\quad
 b_4=(1/2,\sqrt{3}/4,0,5/6),\quad b_5=(0,0,0,0,2).
$$
Take their integer span and mark $u=b_4-b_2$. Its squared norm is
$3/16+25/36=127/144<1$. No row is the mark up to sign.

**Ambient uniqueness.** The Gram matrix of the first three rows has diagonal one and off-diagonal one half. Hence the squared norm on their integral span is
$(\sum c_i^2+(\sum c_i)^2)/2$, a positive integer away from zero.
A vector of norm at most $‖u‖$ has fifth coefficient zero and fourth coefficient zero or $±1$, by its last two coordinates. Normalize a nonzero fourth coefficient to one. A nonzero third coefficient then contributes at least $2/3$ in squared third coordinate alone, in addition to $25/36$. For third coefficient zero the second coordinate is $(2c_2+1)\sqrt{3}/4$. To attain the radius one must have $c_2=0$ or $-1$ and first coordinate zero. The first choice gives a half-integer first coordinate, and the second forces $c_1=0$, giving precisely $u$.

**Exact block checks.** The Gram–Schmidt directions are the coordinate axes. Each earlier-coordinate entry divided by its diagonal pivot is at most one half in absolute value, so the rows are size reduced. For width three, check the projected blocks in order.

1. The first three rows have minimum one by the integral quadratic form above.
2. Delete the first coordinate in rows two through four. The first two projected rows have squared norms $3/4$ and inner product $1/4$. Their binary form is $(a^2+b^2)/2+(a+b)^2/4$, of minimum $3/4$. A fourth-row coefficient of magnitude at least two already exceeds this minimum in coordinate four. For magnitude one, a nonzero third-row coefficient gives squared norm at least $25/36+2/3$. With third-row coefficient zero the lower bound is $25/36+3/16>3/4$. Thus row two attains the block minimum.
3. The remaining three projected rows are orthogonal with strictly increasing lengths $\sqrt{2/3},5/6,2$. Every trailing block also starts with a shortest vector.

Reducing the width with the basis held fixed only removes candidate vectors from each local shortest-vector test and retains its first vector. Thus the same rows satisfy full width-two reducedness. At width two the prefix has rank three and the projected mark is exactly the projected fourth row, the unique shortest pair up to sign. At width three the prefix has rank two. The projected mark still has length $5/6$, but the newly available third row projects to length $\sqrt{2/3}<5/6$. This is a failure from a different, strictly shorter line. The mark is primitive in both quotients. Neither divisibility nor a change of selected basis is needed.

## What transfers to a random planted lattice

For any specified coupling on the same planted instance, let $S_j$ denote capture or terminal recovery at width $j$. For $k<d$,
$$
 \Pr(S_k) ≥ \Pr(S_d)-
 \sum_{j=k}^{d-1}\Pr(S_{j+1}∖ S_j).
$$
Indeed on $S_d∖ S_k$ some adjacent step changes failure to success. The inequality is sharp even for nested events: on a nested chain the increments are disjoint and the bound is equality. A coupling proving $S_j⊆ S_{j+1}$ eliminates the *opposite* increments. Knowledge of full-width success alone permits every smaller-width success probability to be zero, even for nested events.

The geometric example concerns fully reduced Euclidean bases. It does not realize the prescribed prime-field plain-LWE ensemble or the canonical slide initialization. For the registered slide statement, the joint law induced by running both widths on the same uniform matrix is already a coupling. A downward certificate would follow, for instance, if the sum above could be bounded by the difference between the full-width success lower bound and the desired target probability. No such loss estimate, or improved certified width for those parameters, follows from reducedness here.
