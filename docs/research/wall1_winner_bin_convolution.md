# Winner-length bins without conditioning away selection

The capped two-height bound can be used with different radius floors on
different winner branches. This retains a valid bound despite the dependence
between the winner length and the fresh mark. It still needs quantitative
nearest-distance profiles on actual selected histories.

Fix the complete incoming history. Partition fresh marks into arbitrary
events E_j of probabilities alpha_j, on each of which the outgoing radius
is at least a deterministic B_j>=1. For each j form the two miss sets at
B_j and sqrt(B_j^2-1), their densities p_j<=r_j, and their overlap h_j(u)
as in wall1_two_height_convolution.md. Put

    Phi(x)=min(1,(x/delta)^k),
    a_j=delta^(-1) min(1,p_j/delta)^(k-1),
    b_j=min(1,a_j*p_j*r_j),  f_j=Phi(p_j).

For k>=1, the event-restricted contribution satisfies

    E[1_(E_j) Phi(P'_U)] <= min(alpha_j*f_j, b_j).        (1)

Indeed on E_j, P'_U<=h_j(U)<=p_j, giving the first bound.
The second follows by dropping the event indicator in the nonnegative
expectation E[1_(E_j) Phi(h_j(U))] and then applying the unconditional
convolution identity. There is no assertion that U is uniform conditional
on E_j. Summing(1) bounds the outgoing expected capped potential.

## Winner tails from a legitimate incoming representative

Choose fixed cutoffs 0=c_0<c_1<...<c_m=C where s_U<=C is a proven
universal winner cap, and E_j={c_(j-1)<s_U<=c_j}. The radius law gives

    B_j^2=(1.1g)^2 c_j^(-2/506)-1.

Use(1) only for bins with B_j>=1; for all other bins (including a
negative displayed B_j^2), do not define miss sets and set f_j=b_j=1
in the linear program. Their contribution is then bounded by alpha_j. Since (y(U),1) is a nonzero graph vector, shortest selection
gives s_U<=sqrt(d(U)^2+1). Thus for each cutoff c_j>=1,

    sum_(l>j) alpha_l=Pr(s_U>c_j)
        <= Pr(d(U)>sqrt(c_j^2-1)).                       (2)

Strict tails handle ties correctly. These inequalities require no law for
the selected direction. Unknown bin masses may be bounded conservatively
by maximizing sum_j min(alpha_j*f_j,b_j) over alpha>=0, sum alpha=1,
subject to the available tail bounds(2). This is a finite linear program
after introducing 0<=x_j<=alpha_j*f_j and x_j<=b_j and maximizing sum x_j.
A numerical optimizer alone is not a certified upper bound; a rigorous
dual bound or exact solution is needed for a numerical application.
Differences of two upper tail bounds do not bound an individual bin mass:
alpha_j<=T_(j-1)-T_j is not justified without additional lower-tail data.

This combines event probabilities with convolution without multiplying two
dependent probabilities. In particular replacing b_j by alpha_j*b_j would
be unjustified. With one bin it reduces to the capped two-height bound.
With known masses it can improve the worst-cap estimate, but no such
improvement for production histories or stopped-budget closure is claimed.

The finite checker exhausts nested miss sets and all branch events on
cyclic groups of orders1 through5. These algebraic fixtures test selection
dependence; they do not assert realizability as BKZ states.
