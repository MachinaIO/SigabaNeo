# Norm-six rows in the girth-three no-norm-four class

For c=3, a norm-six affine row can have either balanced six-support or
the three-support shape (2,-1,-1), up to permutation and sign. The number
of projective integer lines is therefore

    K = 10 choose(H,6) + 3 choose(H,3).

There are three short patterns on the first three-circuit. With Q=q^(t+a-1),
the coefficient count for codes containing a norm-six line is at most

    min(Q, 3*q^(t+a-2) + 1_(t<=5)*K*q).

The first term must remain even when t>=6: the external-support restriction
only excludes independent short directions. The second term fixes the
normalized first circuit (at most q choices) and an independent short line;
the prescribed missing old position fixes the second circuit direction.

Two independent norm-six rows spanning the code have full union H. If both
have six-support and H>=9, every mixed direction has at least 2H-12>=6
exclusive nonzero entries; neither a generator nor a mixed direction can
be the prescribed three-circuit. A three-support plus six-support pair has
H<=9. At H=9 these supports are disjoint: only the three-support generator
can be the first circuit, and no second direction has a proper nonempty
overlap with it. Two three-support rows have H<=6. Thus H<=8 is necessary
for an eligible two-short-line anchor. K^2, capped by Q, bounds its
coefficient count; this count is set to zero for H>8.

Apply this split only inside the no-norm-four contribution. The existing
theta products (8,6), (6,13/2), and (6,9/2) and their complete long-vector
and periodic tails apply unchanged. Keep all norm-four contributions.
The new envelope is used only if smaller than the old no-norm-four bound.

The exact short-row enumeration now checks the additional three-support
patterns in dimensions four through ten, and the balanced-pair regression
checks that a mixed three-support direction requires H<=7. The field-free
support argument above establishes the omitted large-H case.

This is a paper refinement with exact and interval regression checks.
The residual budget, selected histories and complete BKZ proof remain open;
no Lean formalization is claimed.
