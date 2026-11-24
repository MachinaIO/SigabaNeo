# Expanding the negative weighted competitor term

This algebraic identity isolates the additional information needed by weighted
Bonferroni. It is valid for dependent counts. It is not a numerical bound on
the production selected-history event.

Let(Q,N) have any finite joint probability law on nonnegative integers.
Here Q can count forbidden competitors and N can count terminal witnesses
for a fixed proposed flag. Define formal series

    A(t)=E(1+t)^N, B(t)=E[Q(1+t)^N],
    c_j=[t^j] B(t)/A(t).

A(0)=1 makes division well-defined; c_0=E Q. Equivalently j!*c_j is
the mixed factorial cumulant with one Q entry and j N entries, since
partial_s log E[(1+s)^Q(1+t)^N] at s=0 equals B/A.

For every polynomial f of degree d, with forward difference Delta,

    E[Q f(N)] = sum_(j=0)^d c_j E[Delta^j f(N)].          (1)

Proof: for f(N)=(N)_k, comparison of t^k in B=A*(B/A) gives the result,
using Delta^j(N)_k=(k)_j(N)_(k-j). Linearity in the falling-factorial
basis proves(1). There is no independence step. At j=1 the mixed cumulant
is Cov(Q,N), which can have either sign.

## A rigorous lower envelope, and what it still requires

Suppose f>=0, E Q>=m>=0, E f(N)>=L>=0, |c_j|<=e_j and
E|Delta^j f(N)|<=U_j for1<=j<=d. Then

    E[Q f(N)] >= max(0,m*L-sum_(j=1)^d e_j*U_j).         (2)

If f(N)=sum_k f_k(N)_k, the nonnegative polynomial

    M_j(N)=sum_(k>=j) |f_k| (k)_j (N)_(k-j)

dominates |Delta^j f(N)| on nonnegative integers. Thus univariate factorial
moment upper bounds for this SAME N supply U_j=E M_j(N) or an upper
enclosure thereof. They do not supply e_j: those require the mixed
competitor/terminal incidences, through total order d+1. Nor do upper
bounds for E f supply L. A signed two-sided expansion or another lower
bound is required. If the error sum exceeds mL, the lower envelope is0
and the subtraction provides no improvement.

For a degree24 f, this isolates the negative order25 term in
E f-E Qf+(1/2)E(Q)_2 f. The positive last term still needs mixed data
through total order26. The raw-ball cumulant certificate does not establish
these estimates for selected cylinders. Conditioning on fixed containment
equations is allowed, but all moments must then use that same conditional
law and its probability must be restored in the unconditional flag sum.
Selection exclusions have not been silently included in that law.

The exact checker tests square certificates through degree24 on positively
correlated, negatively correlated, irregular and independent finite laws.
It checks(1), the absolute-difference majorizer and(2) with exact inputs;
independent mixed coefficients vanish and dependent ones exhibit both signs.
This makes the proposed lower-term calculation reviewable without claiming
the missing production mixed-moment bounds have been proved.

## Exact first mixed cancellation for an auxiliary uniform mark

Let A be any random linear map F_q^d -> F_q^m, and let v be an
independent uniform element of F_q^m. For a fixed finite candidate set
S of raw pairs(x,y), put

    N(A,v)=sum_((x,y) in S) 1{x-Ay=v}.

Each candidate specifies exactly one v. Therefore E_v N(A,v)=|S|/q^m
for every A, without any uniformity assumption on A. If Q is A-measurable
and R is a positive-probability A-only event, then under conditioning on R

    kappa_(1,1)=Cov_R(Q,N)=0.

Define the ordered collision count including diagonals

    J(A)=sum_(z,z' in S) 1{x-Ay=x'-Ay'}.

Since E_v(N)_2=(J(A)-|S|)/q^m, expansion of B/A gives

    kappa_(1,2)=Cov_R(Q,(N)_2)-2 E_R N Cov_R(Q,N)
               =q^(-m) Cov_R(Q,J(A)).

Thus the j=1 correction in(1) vanishes for fixed-flag candidate sets with
a genuinely auxiliary uniform mark; the first remaining correction depends
on collision covariance. It need not vanish: with q=3, uniform row A in
F_3^2 and S={(0,0,0),(0,1,0)}, Q=1{A_1=0} gives kappa_(1,2)=4/27,
whereas Q=1{A_1=1} gives−2/27. The checker verifies these fractions and
60 fixed-set/requirement cases exactly. Independent audit confirms the
general identities.

The set S must be fixed under the conditional experiment, or have constant
cardinality. For varying S(A), the first correction instead equals
q^(-m) Cov_R(Q,|S(A)|); it cannot be erased. A candidate cylinder fixed
by a proposed flag meets the fixed-set requirement, whereas selecting a
different cylinder for each A does not automatically meet it. Neither Q
nor R may use the auxiliary test mark v. Conditioning on all competitors
being absent would make Q=0 and the formula trivial; it would not pay the
probability of that conditioning. For weighted Bonferroni one retains the
containment law and estimates its collision covariance. No production
bound for that covariance is supplied here.

## Signed projective-input buckets for the first remaining coefficient

Under a uniform linear-map law A:F_q^d -> F_q^m, write Q and J as
weighted sums of evaluation indicators1{Ay=x}. For J the weights are
ordered candidate-pair difference multiplicities, including diagonals.
Discard zero-input equations for this covariance calculation: they are
deterministic, whether true or false. Normalize each nonzero y by making
its first nonzero coordinate1, scaling x by the same field element.
For normalized input direction l and normalized output x, let B_(l,x)
and D_(l,x) be the total competitor and collision weights. Set p=q^(-m).
Then the signed formula is

    Cov(Q,J)=sum_l [p*sum_x B_(l,x)D_(l,x)
                   -p^2*(sum_x B_(l,x))*(sum_x D_(l,x))].

Proof: two distinct input directions are linearly independent, so their
images are independent uniform outputs. For the same direction, equal
outputs specify the same event of probability p; unequal outputs are
mutually exclusive. Summing these covariances with their weights proves
the formula. It retains both the positive matching-output contribution
and the negative incompatible-output contribution. Combining it with the
auxiliary-mark identity gives kappa_(1,2)=p*Cov(Q,J).

Consistent full evaluation requirements Ay_i=x_i are allowed: subtract
a particular solution and quotient the span of the prescribed inputs.
The remaining map from that quotient to F_q^m is uniform; transform all
competitor and difference constraints before forming buckets. Arbitrary
linear constraints on matrix entries, saturation conditions, or actual
winner exclusions do not automatically preserve this residual-map law.
Unlike the preceding zero-covariance result, this bucket formula cannot
be asserted under arbitrary A-only conditioning.

The script wall1_mixed_collision_buckets.py implements the signed formula
and passes1049 exact constraint-pair checks plus weighted/repeated-event
and full-evaluation-conditioned cases. Independent audit confirms the
scope. For production use the missing quantitative inputs are the bucket
weights of the fixed-flag competitor and cylinder-difference lists, as
well as the higher mixed coefficients. This exact formula does not bound
those weights or pay the sum over selected flags.

## Matrix reformulation audit: positivity alone does not pay selection

Let b(N) be a polynomial-basis column, c=b(0), and, under a fixed
containment law, put G_j=E[1_sat (Q)_j b(N)b(N)^T]. The selected matrix is
G_sel=E[1_sat 1_(Q=0) b(N)b(N)^T]. Pointwise Bonferroni gives

    G_sel <= G_0-G_1+G_2/2                             (Loewner order).

Indeed the difference is the expectation of b(N)b(N)^T times the
nonnegative weight 1_sat 1_(Q>0) binom(Q-1,2). For c^T v=1 this gives
an upper bound v^T(G_0-G_1+G_2/2)v on the selected-and-void joint
probability conditional on containment. It is not a probability
conditional on selection without division by the selected mass.

Weighted Gram optimization, including singular matrices, already exists
in `scripts/optimal_void_square.py` and the joint-tail-square construction.
Changing from falling factorials to a Charlier basis is an invertible
change of coordinates in the same polynomial space, not a stronger
certificate. The matrix language is useful for enclosures, but those
enclosures must hold in Loewner order, not just entrywise.

Using only G_1>=0 gives the upper matrix G_0+G_2/2>=G_0. Its optimized
square bound cannot improve on the corresponding bound with selection
dropped. A potentially stronger Schur bound is

    G_1 >= z z^T/a,
    z=E[1_sat Q b(N)], a=E[1_sat Q]>0.

It follows from E[1_sat Q (b-z/a)(b-z/a)^T]>=0, but z still requires
mixed moments under the correct containment law. For a=0, G_1=z=0.
This observation does not license substituting unconditioned moments.

Even with exact z, the rank-one lower bound can discard nearly all the
useful term. As a reference calculation only, take Q independent of a
Poisson(mu) N, no saturation, and the degree-t kernel K used by the square
certificate. Its exact reference identities are E K=1 and E K^2=D,
where D=sum_(j=0)^t mu^j/j!. The Schur lower bound for E[Q K^2/D^2]
is a/D^2, whereas the true reference value is a/D. It retains only
the fraction 1/D (about2.5567e-13 at the precision audit's reference).
Thus scalar positivity or this rank-one projection does not resolve the
missing negative term. Additional mixed information is needed; no
production estimate is obtained by this reformulation alone.
