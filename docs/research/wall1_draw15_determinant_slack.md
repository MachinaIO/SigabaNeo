# A fixed raw certificate on a determinant-slack gate

This certificate retains the actual selected-length product rather than using
only the period cap s_j<=q. It does not condition the random matrix on that
product when counting candidates. Its gate complement remains unbounded.

## Fixed radius from the selected determinant

At entry to draw15, fourteen primitive directions have been removed.
Their positive Gram--Schmidt lengths s_1,...,s_14 give the retained
determinant D=q^400/prod_j s_j. Define

    C15=prod_(j=1)^14 (q/s_j)>=1.

The incoming GH scale is g15=(D/V506)^(1/506), with D=q^386*C15.
The smaller radius used by the correlation exit test has square
1.21*g15^2*S15^(-2/506)-2. Its deterministic winner cap S15<=q gives

    B15^2>=1.21*(q^385/V506)^(2/506)*C15^(2/506)-2.

Thus on C15>=c, it is at least the deterministic radius
R(c)^2=(R(1)^2+2)*c^(2/506)-2. Raw candidates in that fixed centered
ball project into the required ball. This remains true when C15 and
the selected projector depend on the raw matrix.

Let p15 be the actual projected void fraction and Z_c the number of
fixed raw-ball hits for an independent uniform raw label. Pointwise
projection domination and Markov give

    Pr(C15>=c, p15>=.280) <= Pr_(A,v)(Z_c=0)/.280.

The right side uses the original, ungated matrix law. Additional history
gates may restrict the left side without changing it. No normalization
by Pr(C15>=c) is permitted. A total exit estimate must additionally handle
C15<c; neither its probability nor its projected void is estimated here.

## Complete candidate-error calculation at c=12

Use N519, m400, input dimension119 and q3329. The existing centered-ball
lower count gives mean mu>58.5115 at R(12). Its degree12 Poisson-reference
term 1/(.280*sum_(j=0)^12 mu^j/j!) is below8.49e-13. This reference term
alone is not the actual-law certificate.

The script `scripts/wall1_draw15_slack_certificate.py` recomputes all
compatible circuit bounds, the complete two-relation cover through24,
and repeated-input cumulant errors at the new radius. Free extensions
and all error majorants use the upper candidate mean M. Let ell be the
lower mean. For the kernel K12 normalized by K12(0)=S12(mu), the exact
Poisson finite-difference weights w_k(mu) are the polynomials returned
by `difference_weights(12)`. Their absolute-coefficient evaluation at M
majorizes |w_k(mu)| for ell<=mu<=M. If b_k bounds the factorial-cumulant
correction coefficients, a valid unnormalized error is

    sum_(k=2)^24 |w_k|_majorant(M)*b_k.

Divide this by .280*S12(ell)^2 and add1/(.280*S12(ell)). This uniform
normalization permits the kernel to be defined at the exact deterministic
mean without substituting the lower mean into its cancellation identity.
The moment bounds require no independence of selected directions.

The script reports the complete numerical result; no changed-radius
certificate is inferred merely from the old draw14 or draw15 calculation.

## Result and remaining histories

The full interval computation gives

    R(12)=2901.00498441117...,
    ell=58.511538773098...,
    M=118.788506280282...,
    reference < 8.489522574e-13,
    transferred correction < 2.250382243e-13,
    total < 1.074e-12.

Therefore, under the original matrix law,

    Pr(C15>=12, p15>=.280) < 1.074e-12.

The calculation actually proves the stronger normalized first-moment bound

    E[1_(C15>=12) min(1,p15/.280)] < 1.074e-12,

because min(1,p15/.280)<=p15/.280 and projection domination holds on
the gate. Further past-history indicators can be inserted on the left.
This is a paper-and-interval result, not a Lean theorem or a conditional
probability estimate after dividing by the gate mass.

An independent algebra audit checked the determinant/radius indexing and
the gate direction, plus50 exact rational finite-difference identities
and two Poisson baselines. The complete numerical run uses all connected
strata through24, with no excluded families. The checker now asserts the
correction and total ceilings explicitly.
The asserted rerun completed successfully; `wall1_draw15_slack_checks.json`
retains its output, successful exit, log hash, and288 local Python source
hashes. Both full numerical runs gave the same interval endpoints.

The complementary event C15<12 is not known to be rare. Nor is there a
bound on its projected void. The gate is equivalent to
(prod_j s_j)^(1/14)<=q/12^(1/14), approximately2787.59. No claim that a
typical or every history satisfies it is made. This closes one production
history subset at draw15; it does not close the later-history budget or
the full BKZ proof. In a stopped budget this gated first moment may replace
the contribution of this subset, but must not be added again as a separate
failure charge for an already-counted exit event. The following extension
controls all later visits to the same physical-radius region at no extra cost.

## One fixed prefix controls every later visit to the radius region

Retain the SAME centered raw candidate set S at N519 and radius R(12).
For a realization of its first119 input columns, let r(A_119) be the
fraction of raw labels in F_q^400 not hit by S. Its actual-law certificate
above is E[r(A_119)/.280]<1.074e-12.

For every incoming draw i>=15 in the same first-tour append process,
embed each z in S by adding zero input coordinates. Its syndrome
x-A_i*y equals its original syndrome x-A_119*y_119. Zero extension
therefore induces an isomorphism of the raw quotient groups, both
identified with F_q^400. Composition with the actual orthogonal projection
is a surjection onto the projected mark group, so a uniform raw label
pushes forward uniformly even if the projected group loses rank.

Fix the entire input matrix and its selected history. Every raw hit
remains a representative of the corresponding projected label and has
projected norm at most R(12). Consequently the pulled-back projected-miss
set is contained in the SAME fixed raw-miss set whenever B_i>=R(12).
This proves, simultaneously and pointwise,

    max_(15<=i<=404) 1_(alive_i and B_i>=R(12))*min(1,b_i/.280)
      <= min(1,r(A_119)/.280).

An empty maximum is zero. Taking expectation uses only the original
unconditioned prefix marginal. Thus

    E max_(15<=i<=404) 1_(alive_i and B_i>=R(12))*min(1,b_i/.280)
      < 1.074e-12,

and in particular

    Pr(exists alive i in15..404: B_i>=R(12) and b_i>=.280)
      < 1.074e-12.

There is no factor390, no independence assumption between draws, and no
conditioning on survival or on the radius gate. The same pointwise raw
random variable controls every eligible time. Previously stopped paths
can be omitted using the alive indicator; the whole random matrix can be
sampled in advance for this argument without changing the algorithm.

## A sufficient determinant region, and its complement

Write D_(i-1)=q^400/prod_(j<i)s_j for the incoming determinant and
C_i=prod_(j<i)(q/s_j). Since

    D_(i-1)=q^(401-i)*C_i,
    B_i^2>=1.21*(D_(i-1)/(q*V506))^(2/506)-2,

each of the equivalent conditions

    D_(i-1)>=12*q^386,
    C_i>=12*q^(i-15),
    g_i>=(12*q^386/V506)^(1/506)

is sufficient for the radius gate. The last threshold is enclosed by
(2679.88980101840,2679.88980101841). Replacing the radius gate by this
determinant gate in the two preceding probability/expectation bounds is
therefore valid. No monotonicity of D or g is required: repeated exits
and re-entries to the gate do not incur extra probability charges.

This extends the draw15 result to an entire high-determinant region of
the first-tour history. It does not control failures at B_i<R(12), nor
show those times are rare. The sufficient determinant gate can also fail
when the actual radius gate still holds. In particular no inference about
the small-scale crossing near g=34.807 follows from this threshold.
Later tours, non-append changes of the raw prefix, and a different candidate
set require their own comparison. This extension is a deterministic paper
argument independently audited for quotient maps, rank loss, and indexing;
it reuses the unchanged numerical certificate rather than rerunning it.

## Formalized finite-history transfer

[CommonRawWitness.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/CommonRawWitness.lean)
now proves the counting part of the simultaneous-history argument.
`emptyCount_le_of_preserves_hits` takes a label-by-label preservation
condition and derives domination of empty counts. `history_exit_count_le_raw`
places every gated exit into a single raw exceptional input set.
`history_exit_first_moment` proves, for finite input space Omega and fixed
raw label space Alpha,

    a*|Alpha|*#{omega : exists i, gate(i,omega) and
                    a*|Alpha|<=b*emptyCount(projected(i,omega))}
      <= b*sum_omega emptyCount(raw(omega)).

There is no factor involving the number of indices; the index type is
not even required to be finite. For a=7,b=25 and nonempty input/label
spaces, division by7*|Alpha|*|Omega| gives the .280 first-moment probability
bound. The inclusive threshold includes equality at .280.

The projected occupancies are indexed by raw labels after pullback.
Zero-extension and projection geometry, identification of the actual
quotient maps, the radius gate, and the interval certificate are NOT
formalized by these declarations.
Their hypotheses require preservation of each raw hit on the gate; they
do not assume a final failure-probability bound. The stronger real-valued
maximum-of-potentials statement above remains a paper proof.

File-level validation with `lake env lean` passed. The three initial declarations
report only `propext`, `Classical.choice`, and `Quot.sound`; there are no
new axioms or sorry placeholders. No full project build is asserted.

### Uniform quotient fibers and changing label types

The same Lean module now proves the generic quotient-counting step:

- `uniform_fibers_of_surjective`: every fiber of a surjective additive
  group homomorphism has cardinality equal to its kernel.
- `card_of_uniform_fibers` and `emptyCount_pullback`: for a map with
  fiber size k, both the total label count and the empty count of a
  pulled-back occupancy multiply by k.
- `exit_pullback`: the rational-threshold exit transfers to the raw
  labels with precisely that same normalization.
- `quotient_history_exit_first_moment`: the common-raw first-moment
  bound now accepts quotient label types and fiber sizes depending on
  both entry and input, so rank loss does not introduce an extra factor.

The final theorem takes the actual maps and uniform-fiber facts as inputs;
the additive-group lemma supplies those facts for any given surjective
homomorphism. It still requires a proof that the particular lattice
quotient maps are such homomorphisms and that the raw hits survive the
geometric gate. Neither condition is replaced by the desired probability
bound. For nonempty groups, positivity of the fiber and label counts
permits cancellation to express the count identities as equality of
normalized void fractions. The Lean statements use integer identities
and threshold inequalities, avoiding division by possibly empty types.

The expanded module's eight theorems passed `lake env lean` and printed
only the same three standard axioms. This extends the formalized scope
to changing quotient labels, but supplies no new low-radius probability
estimate or numerical bound beyond the existing interval certificate.

### Actual retained-state coset representatives

[RawGraphWitness.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RawGraphWitness.lean)
now exposes `retained_coset_representative` for the actual `retained (history A) j`
state, j<=406. Given integer o,v,b satisfying the original matrix's affine
equations o=b+A_prefix*v modulo3329 and squared raw length at most r^2,
with r>=0, it produces a vector z of norm at most r whose class equals
the class of sum_i b_i*g_i in that retained state's module quotient.

This reuses the existing private inductive realization proof: append
preserves the graph equation, and freeze uses contraction of the actual
orthogonal projection. It exports the coset conclusion, whereas the older
public shortest-vector theorem required a nonzero newest coordinate.
The new conclusion allows zero representatives and does not require the
newest coordinate to be nonzero; these are essential for preserved prefix
witnesses and the zero label. It assumes no independent or uniformly random
selected projector.

The raw vector in this theorem has all105+j current input coordinates.
Its shorter-prefix version now uses the zero-extension identities proved
below. The conversion from these actual quotient classes to the finite
marked-group homomorphisms and occupancy counts in `CommonRawWitness` also
remains to be instantiated. Thus the concrete geometric representative
lemma is formalized, but the full numerical all-history result is not yet
a single Lean theorem. File-level compilation succeeded and the new
declaration uses only the three standard axioms, with no sorry placeholders.

### Zero extension from the fixed short prefix

`prefixZeroExtend` embeds an integer input vector along `Fin.castLE` and
sets every other coordinate to zero. A finite-sum identity proves both
`sqLength_prefixZeroExtend` and preservation of the affine syndrome sum.
The theorem `retained_coset_representative_of_prefix` combines them with
the actual-state theorem: for every k<=105+j and j<=406, the affine
equations and raw norm bound need mention only the first k columns, yet
the short representative belongs to the actual retained state at j.

In particular k=119 and14<=j<=403 give the prefix preservation required
for draws15..404. The coefficients of later columns are exactly zero;
no conditional independence or averaging argument is used. The theorem
retains arbitrary integer raw labels b and permits zero representatives.
File-level compilation and axiom audits passed for both new public
theorems using only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining interface is the finite marked-group map and the actual
occupancy functions supplied to `quotient_history_exit_first_moment`.
The radius/interval certificate and the low-radius history analysis also
remain outside this formalized geometric statement.
