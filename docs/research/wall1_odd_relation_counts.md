# Direct relation-count bounds in odd dimension

The draw15 raw geometry has dimension519, while several draw14 helpers
accepted only even dimensions. Their integral proofs do not require this
restriction. This note extends three direct integer counts; it does not
instantiate the entire connected-incidence cover or prove a draw15 void bound.

## Layer-cake formula

For n>=1 an integer, a>0, c>0 and A>=0, the half-cube counting argument gives

    sum_(z in Z^n) (A-||z||^2/c)_+^a
      <=2*c^(n/2)*pi^(n/2)*Gamma(a+1)/Gamma(a+n/2+1)
          *(A+n/(4c))^(a+n/2).

Indeed the number of lattice points with squared norm<=t is at most
2*V_n*(t+n/4)^(n/2). Layer-cake integrates this count against
a/c*(A-t/c)^(a-1) on[0,cA]. Substituting u=t/c+n/(4c), and enlarging
the lower integration limit to zero, leaves the beta integral on
[0,A+n/(4c)]. All integrands are nonnegative. Real a and half-integral
n/2 are permitted; no finite polynomial expansion is used in this step.

For k equal pair sums, apply this with a=k*n/2 and c=4 to the existing
intersection bound r(s)<=2*V_n*(R^2+n/4-||s||^2/4)_+^(n/2). Thus the
formula in[the equal-pair note](wall1_multiple_pair_sums.md) holds for
every positive integer n after replacing each x! by Gamma(x+1).
The same substitution in[the orthogonal-pair proof](wall1_orthogonal_pair_sums.md)
uses dimension2n and exponent n. Its only half-integral factorial is
Gamma(n/2+1) from V_n.

For[the shared-four count](wall1_seven_point_codes.md), set p=n/2 as a real
number. The outer beta integral and the term ratio

    (2n-j) U / (3B(p+j+1))

remain valid. The expanded exponent is2n, still an integer when n is odd.
The geometric-series majorant and the Cantelli margin improvements therefore
retain the same proof, replacing p! by Gamma(p+1).

The implementation evaluates Gamma(n/2+1) with exact integer factorials
and outward-rounded sqrt(pi): for odd n=2k-1 it is
(2k)!*sqrt(pi)/(4^k*k!), and for even n it is (n/2)!.
The integer dimension and counts remain unchanged; this is not padding
the raw candidate space to an even dimension. Modular alias bounds in
the existing helpers already allow every positive integer dimension and
still need to be included when bounding modular rather than integer relations.

## Verification and remaining work

`scripts/wall1_odd_relation_counts.py` checks45 exact relation counts in
dimensions1,2,3, including equal-pair, orthogonal-pair and shared-four counts.
It also checks the half-gamma recurrence, even-dimensional equal-pair
regressions through518, and evaluates all three bounds at the actual
conservative draw15 radius in dimension519. The existing short-shape and
integer-energy checker also passes. These are kernel checks, not a complete
probability certificate.

The [draw15 incidence entry point](wall1_draw15_incidence_transfer.md) now
uses these kernels with an explicit geometry state,119/519 dual-coordinate
counts and a separate signed transfer. The default draw14 reporter and its
numerical assertions remain intact. This extension does not itself port
all subsequent specialized draw14 refinements or prove a projected-void bound.
