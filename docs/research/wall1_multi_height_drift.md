# Multi-height conditional void-power bound

This extends the two-layer transition bound using every selected integer
height. It retains the actual fresh-column law and permits arbitrary winner
selection, but still needs quantitative information about the incoming radial
profile. It does not close the selected-history or initialization obligations.

## Conditional lemma

Condition on the entire incoming history before exposing the next fresh column.
Suppose the finite mark group H is a vector space over F_q, q prime. This
includes the marked groups in the fresh q-ary graph process: their initial
exponent is q and projection takes a quotient. Let U,V be independent uniform
marks. Let b(U) be the actual outgoing test radius, and let B be a predictable
lower bound on every b(u). For a finite set J of integers distinct modulo q,
with |j|<=B, define

    R_j=sqrt(B^2-j^2),
    a_j=Pr[D(V)<=R_j], p_j=1-a_j,
    p0=Pr[D(V)>B].

Then for every real k>=1,

    E_U[p'_U(b(U))^k | history]
      <= p0^(k-1) / (1+sum_(j in J) a_j/p_j).               (1)

If any p_j=0 the right side is interpreted as zero, which is exact. If p0=0,
the outgoing void is zero on every branch by the zero layer; handle this
case directly rather than interpreting zero to a zero power. Otherwise the
formula holds even when 0 is not listed in J, since the zero layer remains
available independently of which heights are used for the estimate.

Proof. At height j a nearest representative of V+jU gives a lift of squared
norm D(V+jU)^2+j^2. If this is at most B^2, projection cannot increase it, so
the outgoing mark is hit. Put

    X(u)=Pr_V[ D(V+ju)>R_j for every j in J ].

The outgoing miss set is contained in this event, and also in the zero-layer
miss set of measure p0. Consequently p'_u^k<=p0^(k-1)*X(u).

For distinct j,l modulo q, the map (V,U)->(V+jU,V+lU) is a bijection of
H squared: its scalar determinant l-j is invertible. Thus the hit indicators
Z_j=1{D(V+jU)<=R_j} are pairwise independent, even for unequal radii. They
need not be mutually independent. When 0<p_j for all j, choose

    Y=sum_j Z_j/p_j,  O=sum_j a_j/p_j.

Then EY=O and Var(Y)=O. If O>0, Cauchy–Schwarz gives
Pr[Y>0]>= (EY)^2/EY^2=O/(1+O), hence EX(U)<=1/(1+O).
If O=0 this last bound is the trivial bound one. This proves (1). No
independence conditional on a selected winner or on future success was used.

The weights optimize the ordinary nonnegative weighted second-moment bound:
for any weights w_j, (sum w_j a_j)^2/(sum w_j^2 a_j p_j)
<=sum a_j/p_j by Cauchy–Schwarz. This optimality concerns only that
second-moment method, not the exact all-miss probability.

## Symmetric heights and a sufficient drift condition

Take J={-T,...,T}, 2T<q, T<=B, and L=2T+1. If

    p(sqrt(B^2-T^2)) <= pstar < 1,

monotonicity implies p0<=pstar and every p_j<=pstar. Hence

    E[p'_U(b(U))^k | history]
      <= pstar^k / (pstar+L*(1-pstar)).                     (2)

For the actual incoming observable P, a sufficient nonpositive drift
condition is that the right side of (2) be <=P^k. For example, with k=24,
T=20 and P=.18, the hypothesis p(sqrt(B^2-400))<=.208 suffices. This is
an interval-verified conditional example, **not an estimate proved for the
actual incoming histories**. If P is smaller, the right-hand comparison
must use that smaller value; P<=.18 alone is not a drift premise.

The existing two-layer bound and (1) can be minimized, since both bound the
same conditional power. Multiple heights require a slightly smaller incoming
radius, so their benefit depends on the actual profile. There is no free
replacement of p_j by the old design-radius void. Neither the new inequality
nor the example supplies the initial moment or the required profile bounds
on surviving selected histories. Reused, already exposed BKZ columns still
require a separate conditional-law argument.

## Exact verification

`scripts/wall1_multi_height_drift.py` enumerates nested hit sets in F3,F5,F7
for heights -1,0,1. It verifies the exact optimized first and second moments,
the all-miss bound, and powers 1,2,4,24 with rational arithmetic. The displayed
conditional drift example uses outward interval arithmetic. The proof itself
applies to every finite-dimensional H over F_q, not only these small tests.
No production estimate or Lean theorem is changed.
