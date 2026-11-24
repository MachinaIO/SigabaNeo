# A concrete lattice shell obstruction at corridor scale

Dimension, determinant, q-primary marking, and the existing conservative winner
cap do not by themselves give the desired moving-radius shell control. This
note constructs an actual rectangular marked lattice at g=550 inside the
stated draw-129 scale corridor. It has p(R)<0.129481 at the old design radius,
but p(B)>0.212838 at the radius furnished by the documented cap. This is not
an assertion that this lattice occurs as an algorithmic prefix, or that an
actual transition exits: its shorter horizontal vectors permit a better
winner cap than the conservative cap used below.

## Lattice and normalization

Use q=3329, rank n=505, marked dimension m=400. Let J be uniform on the
integers from -1664 through 1664, X=J^2/q^2, mu=EX and sigma^2=Var(X).
These moments and E|X-mu|^3 are computed as exact rational finite sums.
Put g=550, V506=pi^253/253!, R=sqrt((1.10g)^2-1), z=1.3, and set

    ell=R/sqrt(m*mu+z*sqrt(m)*sigma),
    c=(V506*g^506/ell^400)^(1/105),
    M=ell Z^400 direct-sum c Z^105,
    K=(ell/q) Z^400 direct-sum c Z^105.

Thus M is contained in K, K/M=(Z/qZ)^400, and det M=V506*g^506 exactly,
matching the incoming scale convention used by the two-layer model.
Coordinatewise nearest representatives prove, without any random-lattice
assumption,

    D(V)^2 = ell^2 * sum_{j=1}^400 X_j,

where the X_j are independent copies under the exact uniform mark. The
unmarked coordinates are zero in every nearest representative.

Use the same cap expression as the corridor calculation:

    S=min(q,sqrt(56.2142)*V506^(1/506)*g),
    B=sqrt((1.10g*S^(-1/506))^2-1).

The certified intervals are R=604.99917355..., S=752.11456740...,
B=597.13208868..., ell=101.86953462..., c=98.84648382....
Every graph lattice W_U contains an unmarked horizontal vector of length c,
so S is certainly an admissible upper bound on its shortest winner. However,
c itself is a stronger cap; the result here specifically blocks a universal
shell claim at the B supplied by S. It does not prove a shell crossing at the
branchwise radius determined by the actual winner.

## Certified distribution bounds and external theorem

We use the iid Berry--Esseen inequality

    sup_x |Pr[(sum X_j-m*mu)/(sqrt(m)*sigma)<=x]-Phi(x)|
      <= .4748 * E|X-mu|^3/(sigma^3*sqrt(m)).

The primary source is Irina Shevtsova, *On the absolute constants in the
Berry–Esseen type inequalities for identically distributed summands*,
[arXiv:1111.6554v1, 28 November 2011, Corollary 1, p.3](https://arxiv.org/pdf/1111.6554v1).
Equation (1) defines the uniform error; the hypotheses on p.1 are independent
identically distributed centered, unit-variance variables with finite third
absolute moment. Our finite-support standardized variables satisfy all of
these hypotheses. The paper uses a left-continuous CDF; taking a decreasing
limit of thresholds gives the same uniform bound for the right-continuous
CDF needed for strict void events. The theorem is an external mathematical
input, not reproved by the script.

Here the standardized third moment is 1.37658717... and the error is less
than .03268018. The old standardized threshold is exactly 1.3; the B
threshold is .68865912.... Therefore

    p(R) < .129481,
    p(B) > .212838,
    p(B)-p(R) > .083358.

The script computes the normal CDF by integrating the alternating series for
exp(-x^2/2), enclosing the remainder by the next term, using interval arithmetic.
The finite moments are exact fractions. No Monte Carlo or unverified normal
approximation enters these inequalities.

In particular, the sufficient k=24 two-layer condition also fails for this
cap radius: r=p(sqrt(B^2-1))>=p(B), so

    p(B)^24*r / p(R)^24 > 32236.

This is failure of a sufficient bound, not a lower bound on the actual
outgoing void. The incoming p(R) is positive since the maximal centered mark
has squared distance 400*ell^2*(1664/3329)^2>R^2.

## What torus geometry does give universally

For a full-rank lattice M in dimension n, let F_cont(R) be the Haar-uniform
fraction of the torus R^n/M covered by its radius-R ball. Its Voronoi cell
is convex and contains zero. Scaling its intersection with the R-ball by
B/R proves

    F_cont(B) >= (B/R)^n F_cont(R),  0<=B<=R.

This is a geometric bound, but at n=505 and the current relative radius loss
its factor is roughly 0.0013. It cannot preserve coverage near 0.82.

For finite marks K/M, a covering-radius bound rho for K gives the precise
regularized version, for rho<B<=R:

    1-p(B) >= ((B-rho)/(R+rho))^n * (1-p(R)).

Proof: couple each uniform mark to a uniform point in its K-Voronoi cell on
the M torus. Their torus distances differ by at most rho. Consequently
F_cont(B-rho)<=1-p(B) and 1-p(R)<=F_cont(R+rho); apply the continuous scaling
bound between those two radii. For B<=rho only the trivial lower coverage
bound follows. In the rectangular example rho is exactly
sqrt(400*(ell/q)^2+105*c^2)/2, making this regularized bound much weaker still.
Finite marks have distance atoms, so differentiable coarea reasoning cannot
be applied to their void profile without such a discrepancy argument.

## Scope and reproduction

The construction has the requested dimension, determinant convention, scale
corridor, and a mark group of rank 400. It does not establish realizability
as a projected q-ary raw-prefix history. Those histories impose further
arithmetic and algorithmic restrictions not used here. It does not refute a
shell estimate incorporating those restrictions, an improved actual winner
cap, or a directional projection-gain theorem. It does show that merely
replacing arbitrary profiles by lattice torus geometry does not justify the
existing S-based shell premise.

Run `python3 docs/research/scripts/wall1_lattice_radial_profile.py`.
Log: `/tmp/wall1_lattice_radial_profile.log`. No production files are changed.
