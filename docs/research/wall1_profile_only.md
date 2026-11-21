# Memory in the sequence of Gram–Schmidt profiles

Consider two exact full-block visits followed by one visit to the projected suffix in dimension three. With independent uniform shortest-line ties, the ordered squared Gram–Schmidt profiles after these visits need not form a Markov chain, even with the schedule position supplied. The discrepancy concerns the next **observed profile**. The observer never sees an axis label, a selected line, or a Gram matrix.

## Exact enumeration for one binary check

Let the lattice be the integer kernel modulo two of a uniform row in three coordinates. Use the Euclidean metric. Visit blocks [1,3], [1,3], [2,3]. As in Part 19, whenever a full visit selects a unit axis, put its positive generator first and take a coordinate-adapted basis on the surviving coordinates in increasing **original** index order. This is a basis since the unit summand splits off orthogonally. By coordinate-adapted we mean that each initial segment spans the lattice restricted to the corresponding coordinate span. Other completions can be arbitrary. This rule allows a fresh choice even if the current first vector is shortest.

Write A for profile (1,4,1) and B for (1,1,4). For profiles after the first two visits let E be the event that the second squared spacing after the third visit exceeds one. The following table enumerates all histories with those first two profiles in {A,B}. Entries are unconditional masses in units of 1/32, with columns ordered by observed histories. The last column identifies the histories in the row contributing to E.

| Binary check | AA | AB | BA | BB | E |
|---|---:|---:|---:|---:|---|
| 100 | 4 | 0 | 0 | 0 | none |
| 010 | 1 | 1 | 1 | 1 | none |
| 001 | 0 | 0 | 0 | 4 | none |
| 110, 101, 011 together | 12 | 0 | 0 | 0 | AA |
| Total | 17 | 1 | 1 | 5 | |

Indeed the zero row has squared covolume one, and row 111 has no unit vector. Neither contributes. For every remaining row the shortest lines are precisely its zero-coordinate axes. Every full visit samples these axes independently and uniformly, since it acts on the same full lattice. After deleting the chosen axis, the remaining pair contains a nonzero check. If its first coefficient is one, the first spacing in the pair is two and the second is one by index two. Otherwise those spacings are reversed. Thus for row 010 either profile occurs with probability 1/2 at each visit. For each other displayed row the profile is deterministic. Finally the third visit puts the suffix minimum at position two. That minimum exceeds one exactly when both surviving coefficients are one, in which case its square is two (the vector (1,1) attains it). This derives all entries without observing which axis was chosen.

Consequently
$$
 P(E\mid AA)=12/17,\qquad P(E\mid BA)=0.
$$
The Markov property for the natural filtration would give equality. Including an initial profile in the filtration cannot restore the property, since one could average its prediction over that initial observation. Conditioning the input on a nonzero row preserves both conditional laws.

Any transition kernel using only the current profile has conditional total variation error at least 6/17 on one of the two histories, by the triangle inequality applied to E. For expected conditional TV error, these two histories alone contribute at least 3/136: if the predictor assigns E probability p, their contribution is at least
$(17|12/17-p|+|p|)/32$, minimized at $p=12/17$. These lower bounds measure different notions of approximation.

For this same input distribution no fixed number k of recent profiles suffices uniformly over revisit schedules. Make k+1 full visits before the suffix. Histories consisting of k+1 copies of A, or of B followed by k copies of A, share their last k observations. The latter forces row 010. On the former the posterior probability of a weight-two row is $3/(4+2^{-(k+1)})$ by the table's row-wise independent sampling rule. The discrepancy persists conditionally even as the exceptional history becomes rare.

## A marked example and its limits

The same calculation also fits a small fixed-plant plain-LWE ensemble. Take m=n=1, q=2 and e=s=0 in the embedding of usvp_planted.md. Order coordinates as (y,x,t), so the check is (a,1,0) with a fair bit a and the plant is the third unit axis. Use the same visits and completion in this declared order. Only rows 010 and 110 remain, now equally weighted. On histories AA and BA the posterior probabilities of row 010 are respectively 1/5 and 1. On either history the current profile is A. For row 010 this last A forces the first axis to have been selected, leaving the plant as a primitive unit in a rectangular suffix with other spacing two. It generates the unique shortest line. For row 110 the full visit selected the plant itself, so its suffix projection vanishes. Hence the corrected terminal recovery probabilities on AA and BA are respectively **1/5 and 1**. These are conditional probabilities for a marked block, obtained by summing over inputs and ties given only scalar profiles.

This example allows ties in the ambient lattice (row 010), uses a specified coordinate order, and uses full-block revisits. It gives no lower bound on prediction error conditional on an ambient uniqueness gap, on one forward BKZ sweep, or on the output distribution of the verified slide loop. The Kyber-dimensional selected-prefix probabilities and a block-size improvement over the deterministic recovery criterion remain open.


## Independent audit (Nov 2026)

Verdict: **correct** (all rows and tie choices enumerated with Gram–Schmidt: masses 17/32, 1/32, 1/32, 5/32; 12/17 vs 0; k-window posterior 3/(4+2^{−(k+1)}); marked example 1/5 vs 1). Nit: 'spacing two' means GS length 2 (squared 4).
