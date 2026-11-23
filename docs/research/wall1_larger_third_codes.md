# Fixed short planes with arbitrary crossing size

The fixed-plane three-row argument does not require exactly two new
positions. Let A be an eligible triangular, orthogonal, or shared-point
anchor of size s and rank s-2. Fix an independent basis X of its input
columns. A crossing fundamental circuit introduces t>=2 new positions
and has a nonzero old coefficient row d supported in X.

Let P be the two-dimensional old relation code. Since X is independent,
no nonzero vector supported in X lies in P. Thus d is not in P. Every
three-row code direction independent of P has old part lambda*d+p,
where lambda is nonzero and p is in P, and this old part cannot vanish.
This is stronger than merely excluding weight-two or weight-three words;
it remains true for t>=4. It is an eligibility condition on the crossing,
not a statement about arbitrary three-row codes.

Use the same cutoff and saturated short-lattice construction as Parts
293 and 299. The old primitive plane extends to a basis of that lattice.
The third basis vector reduces independently of P, so every one of its
t new coordinates is a nonzero integer. Its old real projection is also
nonzero: otherwise saturation of the old plane allows subtracting an
integer old-plane vector, producing an independent modular direction
with zero old part, contrary to the preceding argument.

The third squared Gram--Schmidt height is therefore at least

    t+2/3  (triangular), t+1/2  (orthogonal), t+3/5  (shared-point).

Use the previous two old theta factors and this third height. The code
dimension stays three; the number of positions is H=s+t, the augmented
rank is H-3, and beta=(H-3)N/(2HR^2). Retain the same cutoff-dependent
long-vector term, now with the periodic expansion through degree H.
Normalize by q^((H-3)m). Take the minimum with the previous anchor/new-group
product for every t>=3; the t=2 bounds remain the same.

Exact modular checks enumerate 112,918 nonvanishing old parts over the
three planes. The fixed bases are checked by invertible complementary
two-column minors. The argument above applies over any field; the finite
checks guard the implementation and canonical representations.

At size fifteen the full residual weighted log10 improves from -4.86704
to -4.90099 (about 1.26e-5), while the triangular part becomes -5.58631.
The gain is small: the no-double-short remainder and the no-large-crossing
parallel branch still matter. All full cumulant regression bounds through
fourteen are preserved. The residual target, later selected histories,
and full BKZ proof remain open; these new arguments are not Lean formalized.
