# Determinant-coupled dimension-three rectangular marking

This note imposes the actual determinant and dimension-three radius law on a
rank-two rectangular marked model. It gives a universal incoming-void
obstruction for q=3 and a bounded grid check for q=5. It makes no outgoing
drift claim and no claim about reachability in the 506-dimensional production
history.

Let a,b>0, K=a Z direct-sum b Z, M=qK, and H=K/M. For u in H the graph lattice
is

    W_u={(ax,by,j): x=ju_1, y=ju_2 modulo q}.

The defining congruence map onto F_q^2 has index q^2, so W_u has determinant
q^2 ab, independently of u. In its true dimension three define

    V_3=4 pi/3,  g=(q^2 ab/V_3)^(1/3),
    L=(11/10)g,  R^2=L^2-1.

The incoming hit count is the number of residue classes whose shortest
representative in K has norm squared at most R^2. A negative R^2 gives no
hits. Centered representatives minimize the rectangular norm for all a,b>0.

## Universal obstruction for q=3

The nine centered residues have squared norms

    0, a^2, b^2, a^2+b^2

with multiplicities 1,2,2,4, respectively. The four corners all have the
largest norm. Unless all nine residues are hit, all four corners are missed,
so the incoming void probability is at least 4/9. This remains true when
some displayed norm levels coincide.

Suppose all nine residues were hit. Then L^2>=1+a^2+b^2, and the prescribed
radius formula would imply

    (1+a^2+b^2)^3 <= (11/10)^6 (9/V_3)^2 a^2 b^2.

AM-GM applied to 1,a^2,b^2 gives the reverse lower bound

    (1+a^2+b^2)^3 >= 27 a^2 b^2.

But pi>3 implies V_3>4, and the coefficient on the first right-hand side is
strictly less than the exact rational number

    (11/10)^6 (9/4)^2 = 143496441/16000000 < 27.

Since a^2 b^2>0, this is a contradiction. Therefore, for every positive a,b,

    P_in >= 4/9 > 7/25.

In particular the incoming regime P_in<0.28 is impossible in this q=3
rectangular model with determinant-coupled dimension-three radius. This
explains why the independently chosen radius in the earlier rank-two
positive-drift example cannot be imported into this model.

## Certified bounded grid for q=5

The companion script checks q=3,5 and all unordered a,b in
{1/4,1/2,3/4,1,3/2,2,3}, giving 56 configurations (98 ordered ones).
It decides each incoming membership using the equivalent inequality

    (1+a^2 x^2+b^2 y^2)^3
       <= (11/10)^6 (q^2 ab/(4 pi/3))^2.

All quantities except pi are rational. Machin's identity
pi=16 arctan(1/5)-4 arctan(1/239), together with 40 and 12 terms of the
alternating arctangent series, gives rational lower and upper bounds on pi.
Every comparison is decided by these bounds; the script fails if an
interval straddles a threshold. No floating-point comparison is used.

No grid configuration has P_in<7/25. The q=3 grid minimum is 4/9, attained
at a=b=1,3/2,2. The q=5 grid minimum is 14/25, attained at
(a,b)=(1/2,3/4),(1/2,1),(3/4,1),(3/4,3/2),(1,3/2),(1,2).
These q=5 statements apply only to the stated grid; there is no universal
q=5 exclusion proved here.

Run `python3 docs/research/scripts/wall1_dimension_three_marking.py`.
The execution log is `/tmp/wall1_dimension_three_marking.log`.
The universal q=3 proof uses AM-GM and a strict rational constant comparison;
the grid supplements that proof rather than replacing it.
