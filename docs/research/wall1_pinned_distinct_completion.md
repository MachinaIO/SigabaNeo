# Pinned distinct completions and the full-anchor degeneracy

The production full-incidence count is over distinct input residues, not
integer representatives. Fix a valid anchor and its extra basis points. Let
U be their affine input span, B the centered input ball, and C=|B intersect U|.
Suppose exactly m distinct already used inputs lie in B intersect U. For k
remaining ordered positions the number of admissible distinct input choices is
exactly (C-m)_k before imposing further incidence or girth constraints.
Here (n)_k counts injections from k labels into n objects, and is zero for n<k.
Consequently an integer cap C<=L gives the upper bound (L-m)_k; if L<m,
there is no valid fixed configuration at all.

The identities of the m used points may depend on the basis: their number is
what matters for this count. For fixed m, f(U)=(C(U)-m)_k is still a function
of U alone on the support of valid configurations. For a reference law also
containing planes with C<m, define f(U)=0 there, rather than extending the
falling-factorial polynomial to negative integers. This nonnegative function
can be used directly in the weighted-span Cauchy--Schwarz inequality.

In the one-circuit production cover, m=r+1 and k=h-r-1. In the two-circuit
cover, m=r+2 and k=h-r-2. Conditional joint incidence for the remaining
inputs is at most one. Thus apply this bound pointwise on valid fixed data,
then relax the anchor/basis sum by its nonnegative Gaussian majorant. Existing
coefficient-chart factors and rank normalizers are unchanged. An interval
implementation must take L=floor of a certified upper endpoint, not round an
approximate bound to the nearest integer.

Raw integer representatives are not injective modulo q: at q=3329 both
-1665 e_1 and 1664 e_1 are in the radius-2933 ball and have the same residue.
The argument uses the input fibers already aggregated in
`wall1_full_incidence_reduction.md`, so it does not count these as distinct.

## What the weighted method still needs in the leading branches

The high-order diagnostic identifies H=r+2 in each leading two-circuit branch
at h=18,19,24. There are no extra free basis inputs. After the full anchor is
fixed, its affine span S already has dimension d=r-1. The family of affine
d-planes containing S has exactly one member, S itself. Therefore the
fixed-anchor reference of `wall1_weighted_completion.md` has chi-square zero
and variance zero, and its conclusion is the identity E_w f=f(S).

This is not a contradiction of that inequality. It means that conditioning on
the whole anchor removes precisely the geometry over which averaging is
needed in these dominant branches. To improve their completion count, one
must bound occupancy of the anchor span itself, or average over varying
anchors with their actual incidence weights. An unrestricted reference is
valid but then needs its own weighted same-span collision estimate. Fixing a
smaller anchor likewise requires retaining the remaining anchor constraints
in the weights; it does not supply independent random directions for free.

Distinctness alone is numerically insufficient with the existing cap. For
L>=m+k, the relative factor is

    (L-m)_k/L^k = product_(j=0)^(k-1) (1-(m+j)/L)
                 >= 1 - (km+k(k-1)/2)/L.

The last inequality follows by multiplying factors in [0,1] inductively.
For h<=24, m+k=h, the numerator is below 576. Thus when L>=10^30,
this refinement changes the cap by a relative amount below 5.76e-28.
It cannot address the hundreds of decimal orders in the largest current
envelope. Production is deliberately unchanged: the substantive missing
estimate concerns geometry averaged over anchors, not repeated input labels.

`scripts/wall1_pinned_distinct_completion.py` checks the injection count,
variable forbidden sets with equal cardinality, the relative-factor bound,
and the integer-representative counterexample exactly. These checks support
the paper argument; they are not a Lean proof or a new BKZ guarantee.
