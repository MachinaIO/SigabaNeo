# Wall 1 revisited: what the probability bounds certify

Part 39 certifies a single dimension-647 exact SVP call at 99% for the stated plain-LWE CBD(3) ensemble. Part 130 reports a failure *upper bound* above 1% at 646. That leaves the actual probability at 646 undecided. There are two distinct questions here. Can one strengthen a bound on the same random event? Can one change the event that the proof needs to bound? The following observations concern the second question and the limits of the current evidence.

## The geometric event

For a fixed horizontal lattice $H$ and displacement $y$, write $R^2=1+\|y\|^2$. Part 94 gives an exact test for the marked pair to be the only shortest pair. It requires all three of the following:

1. Every nonzero horizontal vector has length strictly greater than $R$.
2. The origin is the unique closest point of $H$ to $y$.
3. For every integer $2\le k\le R$, the squared distance from $ky$ to $H$ exceeds $R^2-k^2$.

Indeed, the squared length at height $k$ is $k^2+\|ky-h\|^2$ for $h\in H$. Sign symmetry accounts for negative heights. With ties charged as failures, the exact probabilistic target for this geometric event is a bound of $1/100$ on the measure of the **union** of the three exceptions over the joint design, selection and plant law. No allocation of separate failure budgets is necessary. Identifying a projected pair and identifying its intended lift are separate assertions whenever projection discards information.

## Checking a certificate

Write $C$ for certificate acceptance and $G$ for a desired geometric property. Soundness gives $C\subseteq G$. Even perfect completeness, $C=G$, gives no lower bound on $\Pr(C)$. With independent new coins for each trial on the same design $A$, and conditional acceptance probability $p(A)$, the probability of exhausting $t$ trials is $\mathbb E[(1-p(A))^t]$. A mean acceptance rate alone gives a **lower** bound on this expression by Jensen's inequality. For example, if $p(A)$ takes only the values zero and one, repeated trials give exactly the one-trial probability of exhaustion.

There is also a distinction concerning what to certify. At final rank 506 the Part 103 Cantelli threshold for conditional 99% uniqueness lies strictly between 27.45 and 27.46 (substitute horizontal rank 505 in its formula). This is a necessary floor. Even a sound check of that floor leaves the random-radius comparison and the positive-height cosets unresolved. Part 101 reports 8.1588 at *horizontal* rank 506 with its sharpened cap. The rank conventions differ by one. Neither figure measures the probability that a check accepts.

## Multiple observations of one mark

Let $X_i$ indicate a favorable geometric event for observation $i$ and $S=\sum_i X_i$. For positive mean, Cauchy–Schwarz gives $\Pr(S>0)\ge (\mathbb ES)^2/\mathbb ES^2$. Thus this particular proof would reach 99% if $\operatorname{Var}(S)\le(\mathbb ES)^2/99$. The condition is sufficient and can be wasteful when $S$ is positive but variable. Part 25 already studies second moments and reruns. Merely choosing multiple prefixes does not constitute a new second-moment theorem.

The missing quantity can be seen even for independent random observation choices conditional on the full instance $I$. For identically distributed choices, $\operatorname{Cov}(X_i,X_j)=\operatorname{Var}(\mathbb E[X_i\mid I])$ when $i\ne j$. This term survives averaging arbitrarily many choices. Part 47's independence of the mark from the horizontal design does not imply independence of observations of the same mark. Part 95's simultaneous bounds on 60 tail heights do not estimate this covariance.

## Allowing multiplicity

A bound on the first moment of a point count $N$ would have a different use from a bound on a minimum: $\Pr(N>L)\le\mathbb E[N]/(L+1)$ for integer $L\ge0$. The observable and the measure matter. Part 101 counts weighted vectors of an ambient **dual** under the design law, then derives a determinant inequality. The count needed to apply this elementary tail bound to a projected **primal** ball would be its occupancy under the selected-lattice law. Part 97 additionally involves translated balls. A determinant lower bound alone controls neither occupancy.

For an exact geometric illustration, take a rectangular rank-505 lattice with 504 orthogonal spacings $41/5$ and last spacing $M>28$. Its determinant grows without bound with $M$, its minimum exceeds 8.16, and the radius-27.45 ball contains at least $2^{11}\binom{504}{11}$ points: choose eleven short axes with either sign. The squared norm is $18491/25<(2745/100)^2$. This example tests the information in a minimum and determinant alone. It makes no assertion about how frequently this shape occurs in the graph ensemble. Even a small bound on terminal occupancy would still leave the cost of finding all the points and the multiplicity of their lifts to establish.

## Scope of the conclusion

These observations identify distinct missing inputs: a lower-tail estimate for conditional acceptance, a joint probability estimate for observations sharing a mark, and a selected primal occupancy estimate. None follows from the quoted certificates. The geometric arguments here establish no width below 647. In particular, the 646 upper-bound failure in Part 130 and the rank-955 crossing in Part 103 are limits of specific certificates, not lower bounds on every possible procedure.

## Audit note (Nov 2026)

Independent audit (Codex): FLAWED in one conclusion; the rest is correct.

**Overlooked joint estimate.** Disjoint fixed sample blocks DO give the joint estimate the note asks for:

* Conditional on the secret s, the blocks' design rows and errors are independent, so k blocks fail together with probability
  ≤ E_s[f(‖s‖²)^k]. Here f is Part 39's per-secret single-block failure bound.
* With blocks of 133 rows, i.e. width 133 + 512 + 1 = 646, the joint failure bounds are 0.014905 (k = 1), 0.005908 (k = 2) and
  0.003682 (k = 3).
* Each candidate is checked on the 245 unused rows. A wrong candidate passes with probability ≤ 2·(7/3329)^245.

So two width-646 SVP calls recover the secret with probability > 99.409%. Three blocks also satisfy the second-moment condition:
Var/E² < 0.009179 < 1/99. The certified maximum oracle dimension with multiple calls is therefore ≤ 646, not 647.

**Confirmed parts.**

* The restart and list-size reductions.
* The rectangular example: minimum 8.2, and ≥ 2.45·10²⁵ points of squared norm 739.64 < 753.5025.
* The uniqueness criterion and the benchmark values (8.15876975, 955, 0.01490536 / 0.00483351).

The audit's exact-integer script is at scratchpad audit98/check646.py.
