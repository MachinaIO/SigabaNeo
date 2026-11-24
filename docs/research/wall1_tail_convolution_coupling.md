# Coupling winner tails to convolution budgets

The winner-bin program can retain the fact that a long winner forces the
fresh mark itself into a specified old miss set. This yields joint interval
constraints, rather than separate winner-tail and convolution constraints.
The argument is conditional on a complete incoming history. It does not
provide the still-missing radial profiles of production selected histories.

## A restricted three-set convolution

Let H be a finite abelian group with qH=0 for prime q, with normalized
counting measure. For subsets A,B,D of respective densities p,r,beta, put

    h(u)=E_v[1_A(v) 1_B(v+u)],
    T(A,B,D)=E_u[1_D(u) h(u)].

Use Fourier normalization hat(f)(chi)=E_x[f(x) conjugate(chi(x))].
For real indicator functions, Fourier inversion and orthogonality give

    T(A,B,D)
      = sum_chi conjugate(hat(1_A)(chi))
                   hat(1_B)(chi) conjugate(hat(1_D)(chi)).

The trivial-character term is beta*p*r. The remaining sum is real, even
though individual terms may be complex. Parseval gives

    sum_(chi nontrivial) |hat(1_A)(chi)|^2=p(1-p),

and analogously for B,D. The coefficient bound in
[the correlation MGF note](wall1_correlation_mgf.md), together with the
indicator and complement bounds, gives

    |hat(1_A)(chi)| <= M_q(p),
    M_q(t)=min(t,1-t,sin(pi*t)/(q*sin(pi/q)))

for every nontrivial character. At t=0 or1 use M_q(t)=0. Every nontrivial
character has order q, so the equal-fiber proof applies for any rank of H.
For trivial H the nontrivial sum is empty and the formulas remain valid.

Bound any one of the three Fourier factors by its M_q bound and apply
Cauchy--Schwarz to the remaining two. This proves

    T(A,B,D) <= beta*p*r + min(
      M_q(beta)*sqrt(p(1-p)*r(1-r)),
      M_q(p)*sqrt(beta(1-beta)*r(1-r)),
      M_q(r)*sqrt(beta(1-beta)*p(1-p))).                 (1)

Independently, positivity and h<=min(p,r), E h=p*r give

    T(A,B,D) <= min(beta*p,beta*r,p*r).                (2)

Let J_q(p,r,beta) be the smaller of the right sides of (1) and (2).
The proof above uses actual conditional densities. The fractional-majorant
argument below also allows one-sided density caps, without asserting that
the displayed expression is coordinatewise increasing.

## One-sided density caps suffice

Suppose only p<=pbar, r<=rbar and beta<=betabar are known, with all caps
in[0,1]. If p<1, replace1_A by

    f=1_A+(pbar-p)/(1-p)*1_(A complement).

Then1_A<=f<=1 and E f=pbar. If p=1 necessarily pbar=1, so take f=1.
Define g and z similarly for B and D. Since every factor is nonnegative,

    T(A,B,D)<=E_(u,v)[z(u) f(v) g(v+u)].

The same Fourier proof applies to these fractional functions. The
equal-fiber character argument bounds each nontrivial coefficient by
M_q of its mean for every function taking values in[0,1], not just an
indicator. Parseval gives E f^2-(E f)^2<=pbar*(1-pbar), and similarly
for g,z. Finally E_v f(v)g(v+u)<=min(pbar,rbar), its average over u
is pbar*rbar, and0<=z<=1. These prove both(1) and(2) with the capped
means. Therefore

    T(A,B,D)<=J_q(pbar,rbar,betabar).                    (4)

No monotonicity of the analytic expression J_q is needed. Multiple valid
cap triples may be evaluated and their bounds intersected. For a trivial
group, the fractional functions are constants and the same result holds.
Thus(3) needs certified upper bounds on the selected-state radial profiles,
rather than exact profiles. The existing seed at one radius does not
provide these caps at the smaller radii required by the winner bins.

## Joint interval constraints for the existing program

Use the cutoffs, events E_j={c_(j-1)<S_U<=c_j}, miss correlations h_j,
and moments m_j=E[1_(E_j) h_j(U)] from
[winner-bin convolution](wall1_winner_bin_convolution.md).
Consider indices 1<=l<k within the prefix where all radius floors are at
least1, and require c_l>=1. The miss sets increase with the bin index,
so h_j<=h_k for j<=k. Write p_k,r_k for the two miss densities defining h_k.

Define, using the incoming nearest marked distance d,

    D_l={u:d(u)>sqrt(c_l^2-1)},  beta_l=|D_l|/|H|.

The height-one graph vector gives S_U<=sqrt(d(U)^2+1). Hence
{S_U>c_l} is contained in D_l. The strict inequalities match the bin
partition exactly; no boundary atom is discarded. Therefore

    sum_(l<j<=k) m_j
      <= E[1_(union_(l<j<=k) E_j) h_k(U)]
      <= E[1_(D_l) h_k(U)]
      <= J_q(p_k,r_k,beta_l).                          (3)

These are additional linear constraints on the m_j once the radial inputs
are specified. Retain the existing shared-prefix constraints, bin masses,
tail constraints and cap inequalities. In particular, do not replace the
right side by beta_l*p_k*r_k: that would assert unjustified independence.
Trivial suffix bins with undefined miss sets are not covered by (3).

The three-set bound can be strictly below p_k*r_k and beta_l*min(p_k,r_k),
so (3) can strengthen the available relaxation. It still needs the same
incoming radial information, and it is not a quantitative bound for the
production chain. No selected-history drift or final BKZ theorem follows
without certifying those inputs and solving the resulting bound rigorously.

## Verification scope

### A directly certified linear-cap transition bound

For k=1 in the capped potential, the interval constraints can be composed
without a floating-point LP optimum. Suppose all m bins have valid radius
floors at least1. Supply certified upper density caps pbar_k,rbar_k and
betabar_l for the miss set D_l at each interior cutoff c_l>=1. Define

    cost(0,k)=pbar_k*rbar_k,
    cost(l,k)=J_q(pbar_k,rbar_k,betabar_l),  1<=l<k,
    d_0=0,   d_k=min_(0<=l<k) [d_l+cost(l,k)].

Every partition of the indices into consecutive intervals bounds the sum
of all m_j by the sum of its interval costs. Induction in k proves that
d_k is the minimum such partition cost and still an upper bound for the
partial sum through k. Since the branch contribution to the linear cap is
at most m_j/delta, this yields

    E[Phi_1(P'_U) | complete history] <= min(1,d_m/delta). (5)

`partition_certificate` implements this recurrence with exact rational
arithmetic and interval-certified rational upper costs. It returns the
chosen partition as a certificate. It takes O(m^2) cost evaluations.
The caller must establish the radius floors, cutoff conditions and density
caps for its actual state. In particular betabar_l must bound the old miss
set D_l, not merely Pr(S>c_l), which can be smaller. Invalid-radius suffix
bins must be charged separately; this routine does not handle them.

This is a feasible combination of interval inequalities, not the optimum
of the full strengthened LP: it omits other bin-mass and cap constraints.
On a pre-exit history with incoming void P<delta it supplies the sufficient
nonnegative drift charge

    max(0,min(1,d_m/delta)-P/delta).

Its stopped average is still unbounded for production histories.

There is a strict improvement of the whole certificate on supplied inputs,
not only one isolated scalar constraint. Take two bins, profiles(0,0) and
(2/7,2/7), tail cap2/7 and delta=2/7. The old shared-prefix relaxation has
optimum2/7: the second-bin assignment alpha=2/7, m=4/49, x=2/7 is feasible
and saturates its total bound. The new partition(0,1),(1,2) certifies

    E Phi_1(P') <=132751925299/500000000000 <2/7.

This is an algebraic comparison of conditional certificates. The supplied
profiles are not asserted to occur in a production selected history.

### Exhaustive checks

Run `python3 docs/research/scripts/wall1_tail_convolution_coupling.py`.
It checks all33,280 triples of subsets in the cyclic groups of orders3 and5.
The comparison uses exact rational triple counts and rational upper bounds
certified by60-digit outward interval arithmetic. At q3329 and the exact
densities p=r=beta=932/3329, the spectral term is below.0715, whereas the
separate shared-prefix budget p*r is above.0783. These are scalar inputs,
not measured or proved production profiles.

For an explicit symmetric-set comparison, take A=B=D={1,-1} in F_7.
The true triple count is zero, and the certified joint bound is strictly
below p*r=4/49. This verifies strictness relative to the separate scalar
bounds; it is not a claim about the optimized full production program.

The checker also exhausts all subset triples in F_3 with all upper-density
caps on the1/3 grid. It verifies(4), including zero and full-density
endpoints, by exact count comparison with interval-certified rational caps.
The composed transition bound additionally passes1,000 two-bin and9,261
three-bin cases over F_3, exhausting ordered miss sets and branch partitions.
The suffix events themselves serve as D_l in these algebraic tests; no
shortest-vector or radius-law realization of them is asserted.
