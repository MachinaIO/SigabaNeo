# Probability audit for fixed sample blocks

Part 131 concerns the plain LWE ensemble. The secret is shared across trials. Conditional on that secret, the matrix rows are independent uniform vectors over the prime field and the errors are independent CBD(3) variables, independent of the matrix. For predetermined disjoint row sets, the events that the projected plant fails to be the unique shortest pair are therefore conditionally independent. Each event is determined by the secret and the rows and errors in its own set.

For row counts $r_i$, Part 39's bounds consequently give

$$
\Pr(\text{every block lacks uniqueness})
\leq \mathbb E_s\!\left[\prod_i f_{r_i}(\|s\|^2)\right].
$$

The product is taken before averaging over the secret. The proof conditions on the full secret. Dependence of the *bounds* only on its squared norm suffices for the displayed formula.

Distinct coordinate projections of shared rows have no such independence guarantee. Both events can depend on the same error and matrix entries even after fixing the secret. Moreover, deleting secret coordinates changes the projected membership condition. A residual must belong to the span of the deleted matrix columns modulo $q$, since any deleted coefficient may be chosen in a lift. Part 39's sample-axis counting argument uses equality to zero and retains all secret coordinates. Applying its bound unchanged to this different membership event would require a separate proof.

## Meaning of a verification error

For a candidate fixed independently of the reserved rows given the secret, suppose its field residue differs from the secret. Conditional also on the reserved errors, the inner product of each fresh uniform row with that nonzero difference is uniform. Exactly seven residues yield a centered residual in $[-3,3]$. Independence across the reserved rows gives acceptance probability $(7/q)^v$, and a union bound applies to a list formed before inspecting those rows.

An integer candidate congruent to the secret passes the residual test with certainty. Thus the preceding probability bounds false acceptance of a **field residue**. For exact integer comparison, each residue has at most one representative in the secret support because $q>6$. Decoding to that representative when it exists resolves the distinction. When the projected plant is the unique shortest pair, the height is $+1$ or $-1$. Multiplying the entire vector by its height selects the height-one representative. A vector of any other height supplies no candidate by this rule.

These observations audit the probability arguments in Parts 39 and 131. They establish no new numerical optimum.
