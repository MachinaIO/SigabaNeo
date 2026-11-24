# A deterministic candidate-density horizon for the selected kernel

Part 471 used a reference mean without proving a production candidate count.
For a particular next-winner cutoff, the existing projected-grid covering
lemma supplies that count through freeze 246. This removes the mean-existence
premise in that range, not the higher-moment or history-transport premises.
The covering lemma itself is already proved in
[history-free compression, Lemma 2](wall1_history_free_compression.md).

## Intrinsic covering and candidate count

Let P be a rational orthogonal projection of rank r and K=P Z^N, considered
inside its real span. Its covering radius is at most rho=sqrt(r)/2. As an
alternative proof, independently round each coordinate of any x in range(P)
to its two adjacent integers with unbiased probabilities. The projected
error has expected squared norm

    sum_i P_ii Var(round(x_i)-x_i) <= trace(P)/4=r/4.

Some rounding outcome therefore has squared error at most r/4. Rationality
ensures K is a lattice. The original proof chooses r independent projected
coordinate generators and uses backward rounding in their sublattice.

For R>rho, covering B(R-rho) by Voronoi cells centered at points of K in
B(R) gives

    #(K intersect B(R)) >= V_r*(R-rho)^r/det(K).

Let M subset K have index h>1 and determinant D=h*det(K), with qK subset M.
For the L nonzero projected points in this ball, and prime q, h>=q, so

    L/(h-1) >= V_r*(R-rho)^r/D - 1/(q-1).                 (1)

The right side can be clipped at zero. There is no conditioning or random
quotient law in this count. It counts distinct projected points, not raw
representatives whose fiber multiplicities would need separate handling.

## Application to the width-506 restart

After f freezes use r=505, q=3329, D=det(M),

    g=(D/V_506)^(1/506),  c=1.1*g,
    R=sqrt(c^2-2),       rho=sqrt(505)/2.

Then R^2+1<c^2, providing a strict height-one witness margin. The selected
section identity D=q^d/sqrt(p_F), with d<=400 and integer p_F>=1, bounds
D<=q^400. Therefore g<=g_max=(q^400/V_506)^(1/506)<3337.64.
The previously certified Hermite/period recurrence gives g>=g_f, where

    L_0=400 log(q),
    L_(f+1)=max(L_f-log(q), (505/506)L_f-log(56.2142)/2),
    g_f=exp((L_f-log(V_506))/506).

Define

    F(g)=(V_505/V_506)*(sqrt(1.21*g^2-2)-rho)^505/g^506
          -1/3328.                                      (2)

When R>rho, (1) gives L/(h-1)>=F(g). The derivative of the logarithm of
the positive term in (2) has the sign of

    506*rho*R + 1010 - R^2.

The certified inequality 1.1*g_max<506*rho makes this positive throughout
the relevant range. Thus evaluating (2) at the determinant floor g_f is
a valid uniform lower bound for all actual g in [g_f,g_max]. If the floor
radius is no larger than rho, use zero rather than evaluating its logarithm.

The outward-interval checker verifies all 407 freeze counts. The intrinsic
cover bound proves F(g_f)>58 through f=246, with

    68.43778 < F(g_246) < 68.43780,
    44.40540 < F(g_247) < 44.40542.

It proves F(g_f)>1 through f=255; the neighboring values lie in
(1.20041,1.20043) and (0.74973,0.74976). The weaker ambient cover
sqrt(505+f)/2 only gives the corresponding horizons 228 and 236.
A failure of the lower expression at the next freeze does not establish
that the actual candidate density is below the threshold. Here f is the
number of completed freezes; the proposed next winner is at draw f+1.

## What this supplies to the high-order route

For the next-winner event S_next>=c, restrict to the necessary old gate
lambda_1(M)>=c. Every nonzero point of norm at most R then has nonzero
quotient label, as proved in [Part 472](wall1_shared_mark_elimination.md).
Through f=246, there are more than 58(h-1) such points. On each fixed
geometric stratum choose deterministically exactly

    L_star=58(h-1)

of them. This is a finite existence/normalization statement, not an efficient
enumeration algorithm. For a fresh uniform nonzero mark U and height one,
the candidate count Z has conditional mean exactly 58, regardless of the
old label correlations. Equivalently M_1=M_0*L_star*p with p=1/(h-1).

This justifies the reference mean for these strata. For every h>=q, the
degree-11 binomial reference denominator also satisfies

    D_11 >= sum_{j=0}^{11}58^j/j!,
    1/D_11 < 1.301e-12.

Indeed each product factor (L_star-i)/(h-2) is at least 58 for i<=10.
The final inequality is checked exactly over the rationals. It is the
reference squared norm, NOT a bound on the actual tail: the selected
factorial-moment corrections of orders 2 through 22 remain unbounded.
Their aggregate and allocation across draws must still be controlled.

The old-minimum gate is necessary for the next shortest-vector tail. It is
not automatically necessary for the height-one empty-coset observable used
in the capped-history potential. Consequently this result cannot directly
replace that potential's remaining history estimate. It can supply candidate
normalization for a next-winner-tail route or a separately justified transport
argument. No extension of the certified BKZ horizon or failure bound is claimed.

## Verification

`scripts/wall1_intrinsic_cover_density.py` checks 160 rational independent-
rounding cases, the monotonicity inequality, all stage threshold comparisons,
and the exact reference-norm inequality. All interval calculations use 40
working decimal digits with outward endpoints. The parent reran the checker.
The covering proof and the associated Voronoi count received independent
mathematical review. A separate review also approved the density normalization,
monotonicity, exact-mean subset and next-winner versus void-potential scope,
and independently reran the stage checker. No new Lean formalization is claimed.


Part 475's [averaged-rounding count](wall1_averaged_rounding_density.md)
subsequently improves the radius loss by integrating the rounding kernel.
It guarantees candidate density above750000 throughout freezes0..406.
The horizon246 above remains the limit of the worst-case-cover expression,
not the limit of every deterministic candidate-count method.
