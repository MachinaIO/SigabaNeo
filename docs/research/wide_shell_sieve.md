# Acceptance in a wide shell

Let a fixed bank map source points in a finite set U to differences in a
finite target set T. Suppose every source has at most cA eligible indices
and each target has between l/c and ch representations, where c ≥ 1 and
l > 0. These are bounds on actual counts in the bank. Bounds on continuum
lens volumes alone do not imply them.

Exact cancellation assigns every target mass (l/c)/(cA |U|). Thus the
total success probability is p₀/c², where p₀ = |T| l/(A |U|). For a
nonempty target and positive success probability, the conditional output
is exactly uniform. Independent retries from this fixed good bank take
c²/p₀ trials in expectation. The Lean theorem windowAcceptance gives the
finite mass identity.

For a depth-m budget, if a separate survival analysis justifies inflating
each input batch by a fixed factor B per level, the input-size multiplier
is B^m. A quadratic scan on the enlarged batches then incurs at most
B^(2m) times its original pair budget (before integer rounding).
Its additive base-two log cost is 2m log₂ B, which is o(n) for fixed B
and m = O(log³ n). Establishing that such a B suffices requires bounds on
bank failure and terminal occupancy as well as independent uniform leaves.

For radial half-width w the squared interval has length 4wR². Length
at least one guarantees an integer label in the closed interval.
Representability in a given lattice is a separate counting question.
A positive ensemble mean implies existence of a populated instance when
the ensemble is finite. S1 requires a relative population error of at
most one percent on the instance under consideration.
