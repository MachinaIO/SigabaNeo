# What the existing estimates say about the Part 246 exit

Let $E$ be the event that the smaller-radius uncovered fraction exceeds
0.273 at least once on draws 2 through 404, inclusive. The proposed upper
bound is $3.64\times10^{-12}$ under the unconditioned 400-row marginal
and the actual shortest-vector selections. There are two sources of
randomness to distinguish. For a fixed incoming history, $b_i$ is the probability
that a uniform coset is uncovered. Drawing the history
determines which fraction is being measured. The requested probability
is over the latter draw. [Parts 230 and 243–247](../PROOF_GAP.md)

### How much of the exit event does the known example cover?

Let $C$ denote the event that at least 18 sample rows vanish on the
106 exposed inputs at the first freeze. Part 247 proves $C\subseteq E$
for every tie outcome. The resulting probabilities satisfy

$$
3329^{-1908}\leq \Pr(C)<10^{-6689},\qquad
\Pr(E)=\Pr(C)+\Pr(E\setminus C).
$$

Thus the lower bound on $C$ is also a lower bound on $E$. The
upper bound pays for one summand only. In particular, the complement
includes potentially different draw-2 exits as well as later first
exits. [Draw-2 construction](wall1_void_exit.md)

### Do the available probabilities measure the same event?

Part 230 bounds a conditional mean for the *next* height-one void
using the *current* two smaller-radius fractions. The inputs of that
inequality already include the unknown fraction. Parts 243–244 provide
independence for specified coordinate tests, and Part 245 identifies
configurations those tests miss. Part 246 reports a finite-group example
with tail above $1.0664\times10^{-8}$, more than 2,900 times the requested
allowance. Its reachability under shortest-vector selection is open.
It diagnoses a limitation of the independence assumptions. It supplies
no lower bound of that magnitude for the lattice process.
[Two-mark estimate](wall1_inductive_typicality.md) · [Part 246](../PROOF_GAP.md)

### What could observing zero exits establish?

As a statistical benchmark, suppose each trial samples an independent
complete history and classifies $E$ exactly. For $N$ trials with zero
exits, the one-sided exact 95% binomial upper confidence limit is
$1-0.05^{1/N}$, obtained by solving $(1-p)^N=0.05$. To put this
limit at or below the proposed bound would require at least

$$
\left\lceil\frac{\log(0.05)}{\log(1-3.64\times10^{-12})}\right\rceil
=823{,}003{,}371{,}854
$$

independent histories with zero exits. Repeated coset probes on a single
history refine the estimate of that history's fraction. They do not
increase the independent-history count in this calculation. This is a
confidence calculation under the stated sampling assumptions. No such
trials were run.
