# The nullity-one contribution to grouped affine moments

This paper calculation bounds one class of dependent-support corrections after
[Part 252's input-fiber aggregation](wall1_affine_fiber_moments.md). At draw 13,
order 12, the independent baseline divided by rho*mu^12 is below 2.845e-13,
and the absolute nullity-one correction divided by the same quantity is below
2.468e-54, for rho=0.280. **Neither is an upper bound for the total failure
probability:** supports of nullity at least two remain unbounded here.

## Exact factorization

Use J_y, rho_y, P(T) from Part 252. Compare the true central moment to that of
independent Bernoulli variables with the same individual means rho_y. For an
ordered tuple of k inputs, let T be its distinct support, e_y its multiplicities,
and define its nullity to be |T|-rank{(1,y):y in T}.

A support of nullity zero has no correction. A support of nullity one has a unique
circuit C: take the nonzero coordinates of any generator of its one-dimensional
relation kernel. Every input in T outside C is a coloop, and those inputs are
linearly independent modulo span(C). Uniform affine evaluation therefore makes
their values mutually independent and independent of all the values on C.
Since inputs are distinct and augmented with 1, j=|C|>=3.

Write

\[
 a_e(t)=(1-t)^e-(-t)^e,\qquad
 b_e(t)=t(1-t)^e+(1-t)(-t)^e.
\]

Every proper subset of C is independent. Expanding the Bernoulli powers as in
Part 252, all proper-subset terms agree with the independent model. Thus the
correction for this tuple is exactly

\[
 \left(P(C)-\prod_{y\in C}\rho_y\right)
 \prod_{y\in C}a_{e_y}(\rho_y)
 \prod_{y\in T\setminus C}b_{e_y}(\rho_y).                 \tag{1}
\]

For 0<=t<=1 and e>=1, |a_e(t)|<=1. For e>=2, |b_e(t)|<=t, by the absolute
centered Bernoulli moment bound; also b_1(t)=0. Hence only tuples where every
coloop has multiplicity at least two can contribute. These facts are valid even
when some fiber densities exceed one half.

## Summing the nullity-one correction

Let Delta_1 be the sum of the tuple corrections (1). Let Q_j be an upper bound
for the number of ordered j-point full-residue affine circuits in the fixed
candidate ball. Let B_j bound the number of ordered distinct candidate tuples
whose augmented inputs are dependent, including inconsistent output assignments.
These are exactly the two Gaussian upper bounds used in Part 250 (its circuit
bound and its input-dependency bound).

For ordered j-tuples of distinct inputs that form a circuit, equation (6) of
Part 252 gives

\[
 \sum_C\left|P(C)-\prod_{y\in C}\rho_y\right|
       \le Q_j q^{-m(j-1)}+B_j q^{-mj}.                    \tag{2}
\]

Indeed a compatible output assignment on an input circuit gives a full-point
circuit: every proper subset remains independent, and full rank equals j-1.
Summing joint probabilities is therefore bounded by the first term. Summing
products of fiber densities counts all corresponding output choices with factor
q^(-mj), which is covered by B_j. Tuples with distinct inputs have distinct full
points, as required by those bounds.

Let S(h,j) be a Stirling number of the second kind, and A(ell,b) the number of
partitions of ell positions into b blocks, each of size at least two. Define

\[
 H_{k,j,b}=\sum_{\ell=0}^k {k\choose\ell}S(k-\ell,j)A(\ell,b).
\]

Choose the ell coloop positions, partition them into b blocks, and partition the
other positions into j nonempty circuit blocks. Order circuit blocks by their
least position to use the ordered count in (2). Summing assignments to the b
coloop blocks, weighted by their rho_y, is at most mu^b: allowing repeated inputs
and overlaps with the circuit only enlarges a nonnegative sum. The original tuple
has a unique circuit, so this counts every contributing tuple. Consequently

\[
 |\Delta_1|\le
 \sum_{j=3}^k\sum_{b=0}^{\lfloor(k-j)/2\rfloor}
 H_{k,j,b}\mu^b
       \bigl(Q_j q^{-m(j-1)}+B_j q^{-mj}\bigr).           \tag{3}
\]

The comparison independent moment, for even k, is at most
sum_(b=1)^(k/2) A(k,b)*mu^b. Only partitions without singleton blocks survive,
and each surviving Bernoulli absolute centered moment is at most its mean.

## Concrete partial evaluation

The script reuses Part 250's radius, Gaussian circuit bounds (including the exact
three-point coefficient enumeration), input-dependency bounds, and lower candidate
count. At draw 13, N=517, m=400, d=117, q=3329. All powers of mu after normalizing
(3) by rho*mu^k have exponent b-k<0, so replacing mu by its lower bound has the
correct inequality direction. The same applies to the independent baseline.
At k=12, outward 80-digit interval arithmetic yields the two bounds stated above.

Let Delta_>=2 be the signed sum of actual-minus-independent corrections from
supports of nullity at least two. The resulting honest statement is only

\[
 \Pr(b_{13}>0.280)
 \le 2.845\cdot10^{-13}+2.468\cdot10^{-54}
             +\frac{|\Delta_{\ge2}|}{0.280\,\mu^{12}}.    \tag{4}
\]

The last quantity has not been bounded. Dropping it would not be justified by the
small nullity-one term, or by the exact cancellation of single coloops. Draws
14--404, the later fixed-raw-ball obstruction, and the separate score/horizontal/
prefix obligations are also unchanged. No new total exception bound is claimed.

## Verification

Run `python3 docs/research/scripts/wall1_affine_nullity_one.py` for the interval
checks. It also reruns the underlying Part 250 verifier. Run
`python3 docs/research/scripts/wall1_affine_fiber_moments.py` for exact rational
checks of (1) over all affine maps and all candidate subsets in four fixtures.
The additional fixture includes a three-input circuit and a fourth input independent
of its span, so both singleton-coloop cancellation and repeated-coloop factors are
tested. The total is 908 candidate sets at orders 2, 4, 8. These are finite regression
checks of the paper proof, not a Lean formalization or a width-506 simulation.
