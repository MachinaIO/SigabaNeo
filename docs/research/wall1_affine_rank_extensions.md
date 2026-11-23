# Extending circuit anchors to arbitrary input rank

This paper lemma bounds the grouped-moment correction of a fixed rank stratum
using one circuit plus basis extensions. At draw 13, order 12, it controls all
connected components of size at most nine, in addition to the circuits and
rank-two components already handled. The remaining connected components of sizes
10--12 are not controlled at a useful scale. This is not a complete exit bound.

## Uniform dependent-subset envelope

For an ordered support T of h distinct inputs and augmented rank r, use

\[
 L(T)=\sum_{\substack{U\subseteq T\\U\text{ dependent}}}
       |P(U)-\prod_{y\in U}\rho_y|\prod_{y\in T\setminus U}\rho_y.
\]

As in Part 255, this bounds the absolute actual-minus-independent centered product
moment for **every** positive multiplicity pattern on T. Independent subsets
have exactly zero discrepancy and are omitted. Distinct augmented inputs imply
that each dependent U has j=|U|>=3 and rank t>=2.

Let epsilon_c=Q_c q^(-m(c-1))+B_c q^(-mc), as in Part 253. Then

\[
 \sum_{\substack{T\text{ ordered, distinct}\\|T|=h,\,\operatorname{rank}T=r}}
 L(T)\le E_{h,r},
\]

where

\[
 E_{h,r}=\sum_{j=3}^h {h\choose j}
 \sum_{\substack{2\le t\le\min(j-1,r)\\r-t\le h-j}}
 \sum_{c=3}^{t+1}
 {j\choose c}{j-c\choose t-c+1}{h-j\choose r-t}
 \epsilon_c\mu^{r-c+1}
 q^{(t-1)(j-t-1)+(r-1)(h-j-r+t)}.                         \tag{1}
\]

Both exponents are nonnegative. This counts all supports of that rank, so it also
bounds the connected ones without requiring a test for connectivity in (1).

## Proof by anchors and extensions

Fix the j positions of U and its rank t. Choose a circuit of c positions inside
U; it has rank c-1. Extend it to rank t with t-c+1 additional positions of U.
Then extend the input span to rank r using r-t positions outside U. Such choices
exist for every actual support. Taking a union over the choices gives the three
binomial coefficients in (1); uniqueness is not assumed.

For the joint-probability term P(U), a compatible assignment on U has probability
q^(-mt). Its c circuit anchor full points form a full-point circuit, so there
are at most Q_c possibilities. Each of the t-c+1 inner basis extensions has at
most C candidate full points. Given a valid rank-t basis and the circuit, each
remaining point in U lies in its affine full-point span, which has q^(t-1)
points. There are j-t-1 such remaining positions.

Each of the r-t outer basis extensions is summed with its density weight rho_y,
and the unrestricted weighted sum is mu. After those valid extensions fix a
rank-r input span, each remaining outer input has weighted sum at most q^(r-1),
since the affine input span has that many points and rho_y<=1. There are
h-j-r+t remaining outer positions. Using C=q^m mu, the anchor and extension factor
is therefore

\[
 Q_c q^{-mt}C^{t-c+1}\mu^{r-t}
             =Q_c q^{-m(c-1)}\mu^{r-c+1}.
\]

For the independent-product term, the c anchor full points have circuit inputs
but may have incompatible outputs. Their weighted sum is bounded by B_c q^(-mc).
All r-c+1 basis-extension positions have weighted sum at most mu. Remaining
positions have the same affine-span weighted bounds as above. This gives
B_c q^(-mc) mu^(r-c+1) with the same q exponent. Combining the two terms and
summing all choices proves (1).

In each completion argument the selected basis extensions remain valid and
independent. Their number is bounded by the unrestricted candidate or weighted
sum; one does not assert that an arbitrary invalid extension fixes a span of
the required dimension. Dropping distinctness or membership restrictions only
increases the nonnegative completion count.

## Component aggregation and concrete limits

For connected components not already covered by Parts 254--255, h>=5 and
3<=r<=h-2. To handle these components up to size H, add
sum_(r=3)^(h-2) E_(h,r) to the size-h activity for 5<=h<=H, retaining the
old circuit and rank-two activities at every size. Apply the component generating
function bound from Part 254.

The new activities are polynomials in mu with nonnegative coefficients. Each
monomial has degree r-c+1<=h-4. A product of activated activities, with the other
inputs counted as ordinary blocks of size at least two, has total mu degree
strictly less than the moment order. Thus normalization by rho*mu^12 leaves
negative powers, and the candidate lower count can be substituted safely.

For draw 13, outward 80-digit interval arithmetic gives:

- admitting all such components through size eight: total normalized correction
  below 1.562e-23;
- admitting them through size nine: total normalized correction below 5.218e-12.

These totals also include all previously covered circuit and rank-two components,
and their mixtures. The independent baseline contributes a further <2.845e-13.
Using the size-nine version leaves a signed remainder Delta_large from supports
containing a connected component of size 10, 11 or 12, rank >=3 and nullity >=2.
The honest conclusion is only

\[
 \Pr(b_{13}>0.280)
 \le 5.503\cdot10^{-12}
                 +|\Delta_{\rm large}|/(0.280\mu^{12}).    \tag{2}
\]

The remainder has not been bounded. Equation (1) does not finish it: its size-12
activity alone, normalized by rho*mu^12, exceeds 9e32. This is a verified failure
of the displayed majorant, not evidence that the actual probability is large.
The dominant loss comes from allowing arbitrary completions in one affine span;
it retains only one circuit constraint while many relations can overlap.
Counting several constraints jointly is needed to improve this particular route.
The later selected-projection problem is also unchanged.

## Verification

Run `python3 docs/research/scripts/wall1_affine_rank_extensions.py`.
The finite verifier uses all 27 affine maps of F_3^2, three output-fiber
configurations, and 768 distinct supports of rank three and nullity at least two.
It independently computes all subset joint probabilities, their weighted
correction envelopes, and the aggregate rank-stratum bounds (1), with rational
arithmetic. The same script checks the interval estimates and the size-12
majorant limitation. The general lemma is a paper proof, not Lean-formalized;
finite regressions are not a high-dimensional selected-process simulation.
