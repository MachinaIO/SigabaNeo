# Fourth-relation extension of the determinant44 anchor

This extends the projection certificate in `wall1_d44_projection.md` into
the larger-component calculation. The anchor has nine positions, rank six
and relation nullity three. A further crossing on t new positions has
H=9+t positions, relation dimension four and rank5+t.

## Short-plane lift and complete kernel

Let L=20 and q=3329. The anchor rows a,b,c are primitive and have Gram
determinant44. If two further integer words of norm below L were independent
modulo their real span, their five-volume would be at most sqrt(44)*L^2<q.
Their residues lie in the same dimension-four relation code, so every
five-minor is divisible by q, a contradiction. Thus the short span has
dimension at most four. Its saturation reduces into the code: adjoining
one word gives covolume at most sqrt(44)*L<q, so the saturation index is
prime to q. The same covolume bound prevents its reduction from losing rank.
The primitive anchor rows extend to a basis of that saturation.

For a fourth basis row, the new coordinates are all nonzero integers. Its
old projection is nonzero because the prescribed old coefficients form a
nonzero vector on an independent rank-six anchor basis. The projection
certificate gives squared fourth height at least t+6/11. With no new
norm-four word, old-plane rounding with squared error at most8/3 gives
the further lower bound6-8/3=10/3. Girth four excludes norm-two words;
the affine lift and q^2>6H justify the even-norm argument at this radius.

The short theta product uses squared heights4,3,11/3 and that fourth height.
The tail is exp(-200*alpha)*theta(alpha/2)^4. It follows by dropping to
four independent coordinate functionals in the relation code after using
half the Gaussian for the norm-L tail. The old anchor alone uses dimension
three and the corresponding power three. Periodic coordinate errors are
retained in every complete Poisson kernel. The implementation chooses
beta=rank*N/(2*H*R^2) and normalizes activity by q^(rank*m).

## Complete coefficient cover

There are at most choose(9,6)*75*18=113400 anchor witnesses: choose an old
six-set, a triangular code and a norm-four extension on one old and three
new positions. Overcounting anchors is harmless. For each h-point support,
multiply by choose(h,9). At rank six, bound either all dependent completions
or expose the least outside point and its fourth relation.

At higher rank r, a t-new crossing leaves extra=r-t-5 free basis points.
Its coefficient cover is

    sum_(a=max(1,4-t))^6 choose(6,a)*q^(t+a-2).

After choosing those positions and free basis points, h-r-4 points remain
dependent, giving q^((r-1)*(h-r-4)). The no-coloop basis multiplicity divides
this cover by extra+1. The t=2 cover is also compared with the existing
parallel and marked-parallel completion counts for anchor rank six.
Rank r>h-3 is incompatible with the anchor's nullity three, and r=h-3
would make every outside point a coloop; both cases contribute zero.

For t<=3, additional norm-four lines have witness upper count
3*choose(9,4-t). At t=4 they would have only new support and violate the
nonzero old projection condition. Add the rare full kernels and the full
coefficient count times the no-four kernel, comparing against the original
unrestricted coefficient bound. All classes and tails are retained.

## Connection to the existing envelope

In the triangular cover restricted to configurations with no determinant44
anchor, the t=3 norm-four exception is empty. Other terms are unchanged.
The new full-anchor envelope is added back; take the minimum of this sum
and the preceding triangular envelope. This is an exhaustive split, not
the deletion of an inconvenient positive term. The final selected-cover
diagnostics still reconstruct the actual envelope, and unrestricted and
restricted crossing diagnostics are stored separately.

This remains computer-assisted mathematics. The whole size17 residual,
later selected histories, adaptive projected BKZ blocks and the new Lean
formalization are separate outstanding obligations.
