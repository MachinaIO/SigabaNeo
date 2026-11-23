# Weighted Gaussian bound for a triangular norm-four extension

The diagnostic `/tmp/triangle_parts.log` identifies the t=3 norm-four
extension, rather than the t=4 crossing, as the effective triangular
size17/rank8 bottleneck after the short-row splits. Its raw crossing has
log10 approximately30.119, versus11.670 for t=4 and-2.708 for t=5.
The raw t=2 crossing is superseded by the parallel/marked minimum.

Let P be a six-position triangular relation plane, with a norm-four
extension v on one old coordinate j and three new coordinates. Among the
three norm-four lines of P choose a containing j and b not containing j.
Their squared norms are four and their inner product has absolute value two.
Every old coordinate admits this choice. There are five affine anchor
patterns and eighteen balanced extension witnesses for each pattern.

Give coordinate j weight5/8, the other five old coordinates weight1,
and the three new coordinates weight9/8. Their sum remains9. In the Fourier
Gaussian metric diag(1/w), exact Gram--Schmidt squared lengths are

    23/5, 72/23, 32/9.

`scripts/wall1_triangle_four_weights.py` verifies these equalities for all
90 pattern/witness pairs with rational arithmetic. The product of coordinate
weights times the Gram determinant is729/16, compared with44 for uniform
weights. This improves the continuous Gaussian determinant factor; the
actual implementation evaluates complete theta bounds rather than using
that asymptotic improvement as a certificate.

For scalar beta, replace the Gaussian majorant by
`exp(beta*R^2*sum(w))*exp(-beta*sum(w_i*||x_i||^2))`. It still majorizes
the product of nine radius-R ball indicators. Since sum(w)=9, the old
Markov exponential is unchanged. Poisson summation multiplies the prefactor
by `prod(w)^(-1/2)=sqrt(4096/3645)` and replaces the code-plane theta product
by the three squared lengths above, with alpha=pi^2/(beta*q^2).

All error terms are retained. Since max(w)=9/8, the weighted quadratic form
is at least8/9 times the unweighted form. Thus the original cutoff-30 tail
is bounded with alpha replaced by8*alpha/9 throughout, and the periodic
coordinate error uses8*a/9 in place of a=pi^2/beta. The short-plane and
integer-lift arguments remain valid: the fixed three rows have a unit minor,
and a fourth integer row of norm below30 would have four-volume at most
sqrt(44)*30<3329 if independent. This contradicts the rank-three code
condition modulo3329. The weighted form does not change this integer argument.

Only the eighteen rare norm-four extension kernels use this bound. Each
witness can choose its own coordinate weights before the union bound.
The norm-six, norm-eight and coefficient-count remainder covers retain their
previous bounds. The production path takes the minimum of the weighted and
unweighted norm-four kernels. This result is computer-assisted mathematics,
not a Lean formalization or a complete adaptive BKZ theorem.
