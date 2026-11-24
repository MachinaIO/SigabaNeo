# Orthogonal determinant matching destroys the rank-two fixture's winner

This is a limitation of one proposed embedding, not a general drift theorem.
Take q=3 and incoming dimension505. Put two marked axes of length a>0 and
503 unmarked orthogonal axes of length c. Thus K/M has order9 and
det(M)=9a²c^503. Use R²=2a²+0.001, L²=R²+1 and g=L/1.1. Matching
det(M)=V506 g^506 forces

    c(a)^503 = V506 ((2a²+1.001)/1.21)^253/(9a²),
    V506 = pi^253/253!.

At a=1, outward interval evaluation gives

    0.28386400284086365 < c < 0.28386400284086367 < 1.

Here g=sqrt(3.001)/1.1=1.5748540533..., outside the earlier g≈550
corridor. The example has q=3 and mark rank2, not q=3329 and mark rank400.

Every appended graph lattice contains the unmarked horizontal vector of
length c. Therefore every actual shortest winner has s<=c<1. The moving
radius B²=L²(s²)^(-1/506)-1 is at least R². Orthogonal projection does not
increase norm, so all nine incoming covered marks remain covered. In this
embedding P=P'=0 for every branch, irrespective of winner tie-breaking.
The rank-two counterfixture's positive drift does not persist here.
More generally, in any dimension with this matched radius law, s<=1 implies
B²>=R² and hence P'<=P by projection and equal-fiber mark pushforward.
This sufficient condition does not assert s<=1 in production states.

For exact certification use pi<22/7. At a=1 it suffices to check
((22/7)*(3001/1210))^253 < 9*253!, which is a rational inequality.

## Changing the common marked scale

The former diagonal candidate (±a,±a,1) has squared length2a²+1.
The same graph lattice always contains a horizontal vector of length3a
and the vertical vector of length3. For the diagonal candidate to be
shortest it is necessary that

    1/sqrt(7) <= a <= 2.

On this whole interval c(a) increases, since

    d/da log c(a)
      = (1008a²-2.002)/(503a(2a²+1.001)) > 0.

But c(2)=0.4918677025012491...<1. This last inequality follows exactly from
((22/7)*(9001/1210))^253 < 36*253!. Consequently throughout the necessary
interval an unmarked horizontal vector is strictly shorter than the old
diagonal candidate, whose length exceeds1. Outside that interval a marked
horizontal or vertical vector already excludes it. Thus no a>0 restores
that particular diagonal winner in this family of embeddings.

This does not classify all other winners or prove nonpositive drift for
all a, all embeddings, or reachable production states. In particular the
constant ratio c/a does not persist for arbitrarily large a. The original
rank-two fixture and this embedding also retain q=3 and mark rank2.

Run `python docs/research/scripts/wall1_determinant_consistent_embedding.py`.
It checks both exact rational inequalities, the derivative sign on the
necessary interval, and outward interval values at a=1,2.
