# Weighted six-position determinant24 kernel

After the two-new triangular refinement, the largest remaining rank8/girth4
two-circuit term has c=4,t=2,overlap2. Its norm-four/norm-six determinant24
family consists of a balanced unit row a on the four old coordinates and
a balanced unit row b on all six coordinates, with <a,b>=0. The twelve
normalized witnesses are already counted in the existing exact cover.

Assign weights5/6 to the four old coordinates and4/3 to the two new ones.
The sum is6, preserving the Gaussian Markov exponential at the existing
scalar beta. In metric diag(1/w), the two rows remain orthogonal and have
squared lengths24/5 and63/10. The weighted determinant product is

    prod(w)*(24/5)*(63/10)=700/27 > 24.

`scripts/wall1_six_d24_weights.py` checks these identities with rational
arithmetic for all twelve balanced witnesses. Each pair has a unit minor
using an old and a new coordinate; it generates the saturated integer plane.
The Poisson prefactor is multiplied by prod(w)^(-1/2)=27/25. Its short-plane
theta product uses the two weighted squared lengths above.

For the error terms use the form inequality diag(1/w)>=3/4 I. Accordingly
replace alpha by3*alpha/4 throughout the existing cutoff-40 tail, and a by
3*a/4 in the periodic-coordinate error. The original unweighted short-plane
lifting conditions still apply to the same set of norm-below40 vectors.
The weighted norm domination bounds the complementary tail; no vector is
dropped by switching metrics.

The production six-position split uses the minimum of this complete kernel
and the previous one only for determinant24. Determinants28,31,32 and the
unclassified remainder keep their previous bounds and counts. This remains
a computer-assisted local estimate, with no new Lean formalization or
complete adaptive BKZ conclusion.
