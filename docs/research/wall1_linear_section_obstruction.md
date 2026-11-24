# A limitation of unprojected linear-section Chernoff bounds

This is an obstruction to a particular relaxation, not to the BKZ theorem.
It generalizes the marked-Gram reachability obstruction beyond isotropic
or orthogonal generators. It does not apply to nonlinear nearest representatives
or to estimates retaining the actual projection gain.

## Determinant forces a large average linear representative

Let K=P Z^N have dimension505, M subset K, and K/M an elementary q-group of
rank d<=400, q=3329. Write D=det M=V_506 g^506 with g>=549.
Choose any r vectors t_i in K whose classes span K/M, and use the linear
representative y(a)=sum_i center(a_i)t_i for uniform a in F_q^r.
Set mu=(q^2-1)/(12q^2). Independence and zero means give exactly

    E ||y(a)||^2 = mu q^2 sum_i ||t_i||^2.

Select d quotient-basis vectors among them. They are real-independent, by
the primitive integer relation argument in wall1_gram_multheight.md.
Extend them to a real basis using the generators P e_j of norm at most1.
Hadamard and the lattice index give D<=q^d product_(selected i)||t_i||.
Consequently AM-GM implies

    E ||y(a)||^2 >= mu d D^(2/d) >= mu 400 D^(1/200).       (1)

The case d=0 is impossible here: unit generators would give D<=1.
For 1<=d<=400 the second inequality follows by differentiating
x exp(2 log D/x): its derivative has the sign of 1-2 log D/x.
Here log D>400 (a loose sufficient bound), so this function decreases
throughout that interval. This proof allows redundant labels and a full,
non-diagonal Gram matrix; no norm majorizer is needed.

At g=549 the right side of(1) exceeds3,839,922, while (1.1g)^2=364695.21.
The exact comparison, without using that rounded decimal, is

    mu 400 (V_506 g^506)^(1/200) > 10.529 (1.1g)^2.

The ratio increases as g^(53/100), so it remains greater than one for
every g>=549. The accompanying script certifies the base comparison
using pi>3 and exact rational arithmetic, and reports interval values.

## Why the relaxed positive-tilt bound cannot help

Fix any nonempty finite integer height set J and any deterministic radius
bound B^2 <= (1.1g)^2. For uniform independent labels U,V define

    Z(U,V)=sum_(j in J) (||y(V+jU)||^2+j^2-B^2).

Every V+jU is uniform, hence E Z>0 by(1). A simultaneous miss event
bounded via the unprojected witnesses is at most exp(theta Z) for theta>0.
But Jensen gives E exp(theta Z)>=exp(theta E Z)>1.
For k replicas sharing U, the relaxed moment certificate is

    E_U [(E_V exp(theta Z(U,V)))^k] >= (E exp(theta Z))^k >1

for every integer k>=1. Larger positive scalar majorizers only worsen it.
Thus optimizing anisotropy, adding heights, or increasing the replica order
cannot rescue this particular positive-tilt certificate.

The condition on B is essential. It covers conservative winner-cap radii
B^2=(1.1g)^2 C^(-2/506)-1 with C>=1. It makes no claim for an actual
winner of length below1 with a larger radius, or for bounds using its
direction-dependent projection gain. Clipping the exponential bound before averaging or choosing the tilt as a
function of U is also outside this Jensen argument.
Nearest representatives can be much
shorter than linear ones and are also outside this obstruction.

Run `python3 docs/research/scripts/wall1_linear_section_obstruction.py`.
The script certifies numerical inequalities; the argument above supplies
the general determinant and Jensen proofs. No selected-history charge
bound follows from this negative result.
