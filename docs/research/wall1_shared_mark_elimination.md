# Eliminating the fresh mark and matching the first selected moment

This refines Part 471 without asserting a uniform old quotient law after
selection. The fresh mark can be integrated out exactly; its remaining
high-order constraints are collisions in the old, selected quotient. On a
necessary geometric gate, the first moment matches the binomial reference
exactly. Higher-order selected collisions remain unbounded at width 506.

## One fresh mark supplies one probability factor

Fix a chronological old-state event E, a quotient H=K/M of fixed order
h=q^d>1, and a candidate list z_1,...,z_L fixed on this stratum. Let Q_E(C)
be the unconditional probability of E and the old quotient equations C.
It retains the fixed-image, saturation, and full competitor conditions of E.
Let U be uniform on H conditional on the complete old state.

For k>=1 candidate indices and nonzero heights j_1,...,j_k, the first hit
lambda(z_1)=j_1 U determines U=j_1^(-1)lambda(z_1). Every other hit is
therefore equivalent to an old quotient equation

    lambda(j_1*z_i-j_i*z_1)=0,        i=2,...,k.

If C denotes this list, the exact joint mass of E, all hits, and U!=0 is

    [Q_E(C)-Q_E(C union {z_1})]/h.                        (1)

Only the quotient equations belong in C. Replacing them by full graph
constraints would wrongly constrain the S-component. Any anchor index gives
the same mass. Dependent or repeated equations introduce no additional rank
factor: Q_E already evaluates their joint event.

For a fixed set D of J distinct nonzero height residues, let Z count candidate
indices whose labels equal some jU, j in D. On U!=0 the height events for one
index are disjoint. Thus

    M_k = (k!/h) sum_{I subset [L], |I|=k} sum_{j in D^I}
              [Q_E(C(I,j))-Q_E(C(I,j) union {z_anchor})],  (2)

where M_k=E[1_E 1_{U!=0}(Z)_k]. Candidate indices, not distinct label values,
are counted, so multiplicities are legitimate. For k=0 use separately
M_0=(h-1)Pr(E)/h. The quotient size must be fixed within the stratum;
otherwise the factor 1/h remains inside the old-state expectation.

This eliminates the extra input coordinate used in Part 471's augmented
map evaluator. It also exposes the remaining obligation: subsequent hits
are old selected collisions, not further independent fresh-mark samples.
Independent review verifies (1), (2), the pivot invariance and normalization.

## A necessary geometric gate removes all zero-label subtractions

To bound the next shortest-vector tail S_next>=c, with c>1, one may restrict
the old-state event to lambda_1(M)>=c: every old vector remains a horizontal
competitor in the next appended lattice. Denote this restricted event E_c.
The gate depends only on the old history. It must be included in Q_E and in
its mass; it does not preserve a uniform residual-map law automatically.

Suppose each candidate is a geometrically nonzero projected point in K with
norm at most R<c. On E_c no candidate has label zero, since that would give
a nonzero vector in M of norm less than c. Consequently

    Q_{E_c}(C union {z_anchor})=0

for every tuple term in (2). If a=Pr(E_c), it follows exactly that

    M_0=a*(h-1)/h,                M_1=a*J*L/h.             (3)

This uses no uniformity or independence of the candidate labels. It allows
duplicate indices, but excludes candidates whose projected point is zero.
For 0<J<h-1, put p=J/(h-1). Then M_1=M_0*L*p, so the first factorial-moment
error in Part 471 vanishes. Writing its polynomial coefficients as c_j,

    Pr(E_c,U!=0,Z=0)
      <= M_0/D_t + sum_{j=2}^{2t} |c_j| epsilon_j,
    epsilon_j >= |M_j-M_0*(L)_j*p^j|.                    (4)

The geometric height margin R^2+max_{j in D}j^2<c^2 is still necessary to
turn hits into short next-lattice vectors. For a trivial quotient the tail
at c>1 is zero; if J=h-1 and L>=1, every nonzero mark is covered and the
void is zero directly. Empty candidate lists supply no coverage. If L or h
varies, partition the old event rather than substituting an average into p.

The known candidate count L, or a rigorous treatment of its variation, is
still needed. Equation (3) does not prove the reference mean used in Part
471's benchmark occurs in the production process. It removes one error
term but does not estimate the higher selected factorial moments.

## Exact checks

`scripts/wall1_shared_mark_elimination.py` compares (1) with the augmented
fresh-column evaluator for all 106 nonempty height assignments in two
fixtures, including a nontrivial fixed image S. All 270 anchor choices
agree. The first fixture reproduces M_0,...,M_4=(64/81,64/81,8/27,0,0).
These gates alone are algebraic fixtures, not complete production histories.

`scripts/wall1_geometric_first_moment.py` separately checks the geometry
in the actual q=3 graph lattice M_A={(x,y):x=Ay mod 3}, A in F_3^2.
Take c=3/2, R=1 and height one. The old minimum gate holds exactly for the
four columns with both entries nonzero. The six signed coordinate candidates
are nonzero and obey R^2+1<c^2. Complete integer short-vector lists contain
18 old and 32 appended vectors of squared norm below c^2. Enumeration gives

    M_0=32/81,     M_1=24/81=M_0*6/8,
    Pr(old gate, S_next>=3/2)=8/81.

The example verifies the old-minimum gate and the first-moment identity
with genuine vectors, not just modular equations. The parent reran both
checkers. Neither fixture proves a production history bound or replaces
its complete selected-event evaluation. No Lean formalization is claimed.


Part 473's [same-coset cluster](wall1_minimum_gate_collision_cluster.md)
shows why the first-moment identity does not extend to small relative higher
moment errors from the old-minimum gate alone. Its q3329 example has 24
geometrically valid candidates in one nonzero class and a strict height-one
margin. Production reachability and finite-field input rank are not asserted.
