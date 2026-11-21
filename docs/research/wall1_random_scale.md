# Random coordinate changes and the selected prefix

In the [plain planted ensemble](usvp_planted.md), let the secret coordinates undergo a uniformly random signed permutation. This preserves their Euclidean geometry and preserves the uniform law of the design matrix. There is an exact test for whether this randomization makes the prefix and the plant independent. The test also applies after conditioning on absence of capture. Even on a four-dimensional planted example, the resulting joint law can have total variation distance exactly $3/4$ from independence.

## The orbit calculation

Fix an input, its marked vector $u$, and an ordered output basis with prefix plane $W$. Let $G$ be a finite group of linear isometries acting on the instance and transport the basis along with it. Equivalently, for an equivariant randomized reducer one can first sample its output and then transport it. In the plain embedding a signed secret permutation $S$ acts by $y\mapsto Sy$, $A\mapsto AS^{-1}$, $s\mapsto Ss$, with $b$ unchanged. This averages over the orbit of the fixed secret, a distinction from the registered probability over $A$ at one fixed secret.

Write $H=G_u$ and $K=G_W$ for the two stabilizers. For uniform $g$, the law of $(gu,gW)$ has distance exactly
$$
1-\frac{|H||K|}{|G||H\cap K|}
$$
from the product of its marginals. Indeed its support is a single orbit of size $|G|/|H\cap K|$, on which it is uniform by equal fiber sizes. The product is uniform on a rectangle of size $|G|^2/(|H||K|)$. The distance is one minus the fraction occupied. Independence is therefore equivalent to $HK=G$. This fixed-orbit formula need not equal the distance of a mixture of orbits.

For any threshold $r$, the probability of $\|\pi_{gW}gu\|\le r$ on this orbit is exactly its original zero-or-one indicator, where $\pi_W$ projects onto $W^\perp$. The same holds for capture, quotient primitivity and the strict comparison with every competing line, since transport commutes with projection and maps basis rows bijectively. Consequently mixing over inputs and conditioning on noncapture of positive probability leaves the original conditional projection-length distribution exactly unchanged. Uniform marginal directions alone cannot justify substituting the independent fixed-plane bound of [Part 9](wall1_planted_prob.md). For example, on one orbit such a substitution for a threshold event has absolute error exactly the fraction of independent pairs that give the opposite indicator.

## A reduced example with a nonconstant secret direction

Take $m=1,n=2,q=17$, $e=0$, $s=(1,0)$ and $A=(2,5)$. The syndrome coefficients on $(x,y_1,y_2,t)$ are $(1,2,5,-2)$. No unit vector is in the kernel, and a squared-length-two vector must cancel two coefficients up to sign. The only matching absolute residues are the two copies of $\pm2$, so the unique shortest vectors are $\pm u=\pm(0,1,0,1)$. Use a full HKZ basis, which is fully BKZ-reduced at width three because each restricted block contains the minimizing first projected vector of its suffix. The terminal prefix is the first line, necessarily $\mathbb Ru$ for every tie rule.

The eight signed permutations on the secret pair give four equally likely marks. Their four lines are distinct because each mark has last coordinate one. The joint law occupies the diagonal of a four-by-four rectangle. In particular the squared projected length is zero with probability one, versus $1/4$ for independent draws of the plane and mark. This example has capture with probability one. It disproves the independence inference even when the prefix is forced by reduction, and supplies no lower bound on failure of capture-or-terminal recovery.

## Which scale changes transfer back?

For an invertible coordinate change $T$, using the transported norm $\|v\|'=\|T^{-1}v\|$ gives exactly the isometric experiment above as regards every marked recovery indicator. Keeping the ordinary Euclidean norm after an anisotropic change instead alters the shortest-vector comparisons. This can happen in the same explicit example. Scale both secret coordinates by $c>0$. The squared marked length becomes $1+c^2$, whereas $(2,0,0,1)$ satisfies the congruence and retains squared length five. For every $c>2$ the original unique shortest pair has lost even ambient minimality. The same issue arises for error scaling by exchanging the roles of the error and secret axes in a suitable instance: explicitly $m=n=1,q=17,A=2,e=1,s=0$ gives coefficients $(1,2,-1)$, unique shortest pair $\pm(1,0,1)$ by the same two-coordinate test, and competitor $(0,1,2)$ of constant squared length five.

Thus a fresh Euclidean reduction after a nonsimilarity needs a transfer estimate. Even with isometries, reconstructing canonical input rows after transformation may change a presentation-dependent slide trajectory. The orbit argument applies to transported outputs or equivariant output laws; canonical reinitialization needs its own selection law. Neither experiment here bounds the uncaptured failure probability of the verified slide loop or certifies a smaller block size.
