# A square certificate retaining selection and collision dependence

The even Bonferroni sum of Part 266 is valid but can be very large when many
competitor events are present. The square certificate of Part 257 can instead
be applied to the competitor count, while retaining its joint moments with
the occupancy collision count. No independence of these counts is required.

## Pointwise bound and the exact mixed expansion

Fix a proposed flag and its next-radius cylinder. Work conditional on its
containment equations. Let B index the distinct forbidden competitor events,
Z=sum_(b in B) I_b their count, and J the ordered collision count. Let S denote
the flag's saturation event. Selection is exactly S and Z=0, by Part 266.
Let g(J)>=0 on S; examples are (J-c)^2 or the parity polynomial (J-c)^2-1
with the appropriate integer center.

For any mu>=0 and degree t>=0 use the normalized kernel from Part 257,

\[
 D_t=\sum_{j=0}^t\mu^j/j!,\quad
 K_t(z)=\sum_{l=0}^t\frac{(-1)^l D_{t-l}}{l!}(z)_l,\quad
 V_t(z)=K_t(z)^2/D_t^2.
\]

The parameter mu can be chosen deterministically for each flag; it need not be
the mean of Z. Since D_t>=1, K_t(0)=D_t and V_t>=0, one has pointwise

\[
             g(J)1_S1_{Z=0}\le g(J)1_S V_t(Z).                \tag{1}
\]

Write V_t(z)=sum_(h=0)^(2t) f_h(z)_h. The exact rational coefficients are obtained
from the falling-factorial product identity

\[
 (z)_i(z)_j=\sum_{v=0}^{\min(i,j)}
                  {i\choose v}{j\choose v}v!(z)_{i+j-v}.
\]

Set A_h(g)=sum_(T subset B, |T|=h) E[g(J)1_S product_(b in T) I_b | contain].
For each outcome, (Z)_h counts the ordered h-tuples of distinct present events.
Hence

\[
 E[g(J)1_S V_t(Z)\mid\mathrm{contain}]
                  =\sum_{h=0}^{2t} f_h h! A_h(g).             \tag{2}
\]

For g(J)=(J-c)^2, A_h(g) is obtained from the existing three subset-moment rows
as A_(h,2)-2c A_(h,1)+c^2 A_(h,0). Thus (2) uses exactly the conditional joint
rank formulas and span grouping already developed, but different coefficients.
It needs subset orders only through min(2t,|B|), and at most two additional
collision equations per term. No sum over all subset orders is required.

If tau>c, the selected collision-tail probability is consequently at most

\[
 \Pr(S,Z=0,J>\tau\mid\mathrm{contain})
       \le\frac{\sum_h f_hh! A_h((J-c)^2)}{(\tau-c)^2}.       \tag{3}
\]

For the parity polynomial use the strict integer threshold and denominator of
Part 268. Multiply by the containment weight q^(-mt_flag) and sum over a complete
canonical flag family to obtain an unconditional bound. Degree, center and mu may
depend on the fixed flag, but not on which conditioned matrix is realized.

The coefficients f_h have mixed signs. Missing moments cannot be replaced by
zero, and arbitrary termwise upper bounds cannot be substituted into negative
terms. Nor may the joint expectation be replaced by E[g(J)1_S] E[V_t(Z)]: that
would require an additional correlation argument. The implementation checks that
all required subset rows are supplied and otherwise rejects the evaluation.

## Why change the certificate?

Under a Poisson reference of mean mu, the unweighted expectation of V_t is 1/D_t,
as proved in Part 257. For the illustrative rational value mu=1.10^506/2, exact
rational arithmetic gives a degree-ten Bonferroni reference value greater than
10^199, whereas E[V_5] under that reference is less than 10^-100. This comparison
concerns only the two reference-law certificates. The displayed mu has not been
proved to be the conditional mean of any actual selected flag, and the Poisson
law has not been proved for Z. In particular these numbers are not BKZ failure
probabilities or a bound for the mixed expression (2).

The finite actual-design tests use q=3,5 in dimension three, rather than a Poisson
replacement. They check (2) by averaging g(J) V_t(Z) directly over all matrices
that contain each proposed flag. All 288 cases at degrees one, two and three
agree exactly and satisfy (3); 34 give a smaller numerator than Bonferroni at
the same degree with the same collision center. There is no uniform dominance.

## Implementation and remaining obligation

The follow-up [weighted optimal square](wall1_optimal_mixed_square.md) optimizes
the polynomial against the actual mixed moment matrix, rather than the Poisson
reference. It uses the same subset-moment orders and supplies an exact algebraic
optimality certificate; its width-506 moment inputs are still unavailable.

`scripts/void_square_polynomial.py` constructs normalized rational coefficients
and evaluates the mixed sum. `scripts/wall1_mixed_void_square.py` checks 945
polynomial evaluations, 45 Poisson identities, and rejection of incomplete input.
The selected-law checks run in `scripts/wall1_selected_flag_3d.py`.

This gives an alternative finite certificate whose reference behavior is suitable
for large competitor counts. The actual width-506 mixed moments and their sum over
selected flags remain unbounded. There is no new draw-14--404 probability estimate,
no improvement on the remaining 3.922e-12 allowance, and no full BKZ completion.
The mixed-square extension itself is a paper derivation with exact checks, not
a Lean formalization.
