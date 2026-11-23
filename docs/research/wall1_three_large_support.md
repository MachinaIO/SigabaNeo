# Three-circuits with many new coordinates

The size17 rank10/girth3 residual is dominated by c=3,t=9, especially
overlap two. Improve its no-four family by retaining the support
restriction in the norm-six and no-six cases.

For t>=6, a norm-six row cannot be independent of the first three-circuit:
an independent row must be nonzero on all t new positions, and a row
supported entirely on the new positions would make every old support
empty or all of C. That contradicts the prescribed proper nonempty old
overlap. Hence an independent row needs at least t+1 nonzero entries.
The only possible norm-six line is on C, of shape (2,-1,-1) up to sign
and permutation. This line is primitive.

For every integer old-coordinate vector v, its squared projection
perpendicular to (2,-1,-1) equals

    (v1-v2)^2/2 + (v0+v1+v2)^2/3.

If nonzero, this is at least1/3. An independent codeword must have
nonzero old projection: otherwise its old coordinates are an integer
multiple of the primitive first row, and subtracting that row leaves
a new-only direction, contradicting the proper old overlap as above.
Each new coordinate is nonzero, giving second squared height at least
t+1/3. Combine this with the old13/2 bound by taking the maximum.
The integer identity proves the result for all old vectors;729 bounded
vectors independently cross-check it.

For t>=8, a norm-eight row also cannot be independent, since that would
require at least t+1>=9 nonzero entries. It cannot lie on C either:
affine norm-eight shapes with support at least three have support five
or eight. Therefore, in the no-six family, the first squared minimum is
at least ten. Use complete theta kernels with squared heights10,15/2
instead of8,6, taking the smaller complete envelope. Short-span dimensions
zero or one are covered by the same products, with unused factors>=1.

The production split keeps every coefficient count, the norm-six tail
at cutoff36, the no-six tail at cutoff14, and all periodic layers. No
family is excluded. The proof is for component envelopes; it is not a
Lean formalization or a complete adaptive BKZ theorem.

The complete interval run passes2106 cumulant regressions. Transfer through
sixteen stays below9.583e-13 (about8.78527726940e-13). Size17's weighted
residual log10 is4.9020758187; the former rank10/girth3 obstruction is no
longer in the five largest strata. Rank8/girth8 now leads at4.5117420786.
Through24 is about1.05489e232, still an ineffective upper envelope. The
remaining2.0505e-12 allocation and the adaptive BKZ bridge remain unproved.
Logs: `/tmp/wall1_three_large_support.log` and
`/tmp/wall1_three_large_support_cumulants.log`. These are not estimates
of actual failure probabilities.
