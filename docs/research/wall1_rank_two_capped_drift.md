# Positive capped drift in an exact rank-two marked lattice

This is a counterexample to a universal capped-drift inequality for the
specified low-dimensional geometric model. It does not establish that this
marked lattice or its incoming void probability occurs in the production
506-dimensional history.

Let K=a Z direct-sum b Z, M=qK, and H=K/M=F_q^2, with a,b>=1.
For uniform u in H the graph lattice consists of (ax,by,j) with
x=ju_1 and y=ju_2 modulo q. Choose an actual shortest nonzero vector w;
ties are resolved by lexicographic order of the integer tuple (x,y,j).
Write s^2=||w||^2. Incoming radius squared is R^2=L^2-1; outgoing projected
radius squared is L^2 (s^2)^(-1/506)-1. A coset v is hit if some integer
triple z=(ax,by,j), marked v=(x-ju_1,y-ju_2), has projected norm within
that outgoing radius. Set delta=7/25 and Phi(P)=min(1,(P/delta)^24).

## A fully explicit positive example

Take q=3, a=b=1, R^2=2 and L^2=3. Every incoming coset has a centered
representative in {-1,0,1}^2 with squared norm at most 2, so P_in=0.

For u=(0,0), the shortest winner is vertical, s^2=1, and all cosets remain
covered. For the four axis u, sign symmetry reduces to u=(1,0), with
winner (1,0,1), s^2=2. Writing A=x-j and B=y, projected squared norm is
A^2/2+B^2. Every residue pair has centered choices with norm at most 3/2.
The outgoing radius exceeds 3/2, since (6/5)^506>2. Thus P_out=0.

For the four diagonal u, sign symmetry reduces to u=(1,1), winner
(1,1,1), s^2=3. The stated deterministic winner may be its negative,
which gives the same projection. Writing A=x-j and B=y-j gives

    projected squared norm = (2/3)(A^2-AB+B^2).

Six nonzero residue classes have minimum quadratic value 1. The two
opposite classes (1,-1),(-1,1) have minimum 3: their quadratic values are
0 modulo 3, cannot be zero, and the centered choices attain 3. Hence
their exact projected minima are 2; the other seven minima are 0 or 2/3.
The outgoing radius lies strictly between 2/3 and 2, since
(9/5)^506>3 and 3^(-1/506)<1. Exactly two cosets are missed, so P_out=2/9.
The winners used above are actual shortest: a nonzero height needs
|j|>=1; at |j|=1 the required nonzero residues force one or two unit
horizontal entries, while |j|>=2 has norm squared at least 4 and height
zero has norm squared at least 9.

Consequently the exact mean drift is

    E Phi(P_out)-Phi(P_in) = (4/9)(50/63)^24
      = 238418579101562500000000000000000000000000
        /137535780487635830708722649385862219913955849
      = approximately 0.0017335022076164087 > 0.

This is not merely an incoming-boundary artifact. The same result holds at
R^2=2001/1000, L^2=3001/1000. All incoming representatives are strictly
inside the ball, and the exact integer check
3*3000^506 > 3001^506 ensures that the diagonal outgoing radius is still
less than 2. The other outgoing coverage conclusions remain valid.

## Why the finite search counts every outgoing hit

A winner has norm at most min(qa,qb), because the corresponding horizontal
M vector is available. This bounds the exhaustive winner search.
Every representative of a projected hit can be shifted by an integer
multiple of w until its parallel component has length at most s/2.
This preserves both its projection and its mark, since w has mark zero.
The shifted representative therefore has norm squared at most
b_out^2+s^2/4. Since s^2>=1, b_out^2<=R^2. The script enumerates every
integer triple within R_max^2+s^2/4 for the largest radius in each grid.
Thus every possible hit at each smaller radius occurs in this enumeration.
No nonprimitive-winner assumption is needed for this shift argument.

For rational projected squared norm p^2, membership is checked exactly by

    ((p^2+1)/L^2)^506 * s^2 <= 1.

The code clears denominators and compares integers. Missing cosets in the
finite enumeration cannot be hits by the preceding argument; this is an
exact void count, not an upper bound from selected witnesses. Displayed
decimals are not used in any decision.

## Reproduction and scope

Run `python3 docs/research/scripts/wall1_rank_two_capped_drift.py`.
The modest grid uses q=3,5; unordered (a,b) from {1,3/2,2}; radii at every
incoming norm threshold and offsets +/-1/1000, +/-1/100, retaining P_in<7/25.
The execution log is `/tmp/wall1_rank_two_capped_drift.log`.
The script verifies the strict-interior positive fixture explicitly.
The finite experiment and the explicit proof refute only the universal
inequality over this marked rectangular model with the specified moving
radius law. They do not refute a theorem with additional production-history
restrictions, and do not resolve the BKZ proof.

## Determinant consistency follow-up

Part445 checks two attempts to impose the missing normalization. The
[orthogonal506 embedding](wall1_determinant_consistent_embedding.md) creates
a shorter unmarked winner; the [dimension-three model](wall1_dimension_three_marking.md)
never enters the relevant incoming-void regime at q3. These do not invalidate
the counterexample for its stated independent-radius model. They identify
why it must not be presented as a counterexample to the normalized target.
