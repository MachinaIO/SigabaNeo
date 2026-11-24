# H5 exceptional normalizer and correlated moments

The c3/H5 overlap-two exceptional family contains six coefficient codes with
two balanced norm-four relations. Its canonical basis is (s,3,4), where s is
the shared old coordinate of the two relations; the omitted old coordinates
have a unit relation minor. The resulting A, up to swapping the last two
rows, has rows (1,1),(1,−1),(−1,1). Both columns sum to one over the integers,
have norm squared three, and have inner product −1.

Thus det(I+AᵀA)=15, its largest eigenvalue is5, and the exact LDL pivots
of G⁻¹, G=I+AAᵀ, are (1/3,3/5,1/3). The root Gram EᵀG⁻¹E has pivots
(14/15,5/14). Their products are1/15 and5/15. The correlated-moment argument
applies with r₀=3,H₀=5. This must be distinguished from H7,D15,r₀=5.
Numerical caches and profile selection now include H₀ explicitly.

The centered kernel normalizer is at least both h_old³ and
q²α/(π√15), by the same centered sublattice and Poisson arguments as the
other canonical families. The completion-square cancellation and raw
correlated moment candidates do not divide by this boost again.

## Common Gaussian reference

The one-four component is saved before the weighted D23 refinement. Its
isotropic complete split uses the existing filtered determinant counts and
fixed_four_plane(D/4), with the existing complete remainder. The no-four
component remains isotropic. Before the five-point weighted ball replacement,
save, with pref=exp(5βR²)/q^(3m),

    exceptional = pref * bad_count/q³ * bad_bound^N,
    remainder   = pref * (safe_one + none_power).

Only the exceptional part receives the H5,D15 completion. The remainder
receives the generic H5 completion. The bad count is six for overlap two,
and zero when exclude_five_fifteen applies. The one-four D20 exclusions
remain governed by exclude_five_twenty.

For f=r−3 independent extensions, the candidate is
choices*q³*free_cost^f/(f+1) times the completed sum. There is no extra half.
Both the original Gaussian weight and independently optimized free weight
are tried, with all previous candidates retained. Production and frontier
reconstruction both include the split. This is an analytic/interval result,
not a Lean formalization or a selected-history theorem.
