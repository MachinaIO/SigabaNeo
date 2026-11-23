# Input-fiber aggregation and a barrier to input-rank-only moment bounds

This note proves that the input-rank-only majorant in Part 251 cannot certify the
initial raw affine graph at draw 13, even with exact pattern counts. It then gives
an exact aggregation that removes the offending same-input overcount. The results
are paper proofs with rational finite checks, not Lean theorems. They do not close
the width-506 selected-history probability obligation.

## An unavoidable rank-one contribution

Let S be a nonempty fixed set of distinct points (x,y) in F_q^m times F_q^d.
Write Q=q^m, p=1/Q, C=|S| and mu=C/Q. For each occupied input y, let
B_y={x:(x,y) in S}, a_y=|B_y|, and let Y be the number of occupied inputs.
Then sum_y a_y=C and Y<=q^d.

For k>=2, every ordered k-tuple of candidates with the same input has augmented
input rank one and no coloop, including tuples with repeated points. Conversely,
rank one forces all inputs to agree, because the augmented input starts with 1.
Thus T_(k,1)=sum_y a_y^k. The rank-one part alone in the normalized majorant
of Part 251, equation (9), is

\[
 \mu^{-k}p(1-p)^{k-1}\sum_y a_y^k
   =(Q-1)^{k-1}\frac{\sum_y a_y^k}{C^k}
   \ge\left(\frac{Q-1}{Y}\right)^{k-1}
   \ge\left(\frac{q^m-1}{q^d}\right)^{k-1}.             \tag{1}
\]

The first inequality is the power-mean inequality
Y^(k-1) sum_y a_y^k >= (sum_y a_y)^k. Every other term of that majorant is
nonnegative, so even perfect counts T_(k,r) cannot reduce it below (1).

At draw 13 the raw dimension is 517, with m=400 output and d=117 input
coordinates. For k=8 and q=3329, exact integer comparison gives

\[
             ((3329^{400}-1)/3329^{117})^7>10^{6977}.    \tag{2}
\]

This concerns the **majorant**, not the true moment or failure probability. It
rules out using an input-rank-only absolute bound for the individual point tuples
in this regime. The factor removed in Part 251 was a valid local improvement, but
it did not solve this much larger loss of output compatibility and cancellation.
The earlier direct eighth-moment bound in Part 250 uses a different majorant and
is not contradicted by (1).

## Aggregate candidates sharing an input before taking moments

For a uniform affine map F define J_y=1{F(1,y) in B_y} and rho_y=a_y/Q.
Because the candidate residues are distinct, exactly one output can be hit at
each input. Hence the original point count satisfies the pointwise identity

\[
              Z=\sum_y J_y,\qquad \mu=\sum_y\rho_y.       \tag{3}
\]

Each J_y is Bernoulli(rho_y). Distinct augmented inputs (1,y),(1,y') are linearly
independent, so their values under F are independent, and so are J_y,J_y'. Thus

\[
                 \operatorname{Var}Z
                    =\sum_y\rho_y(1-\rho_y)\le\mu.       \tag{4}
\]

In particular, the **exact** contribution of all point tuples sharing one input
to the k-th centered moment is

\[
 \mathbb E(J_y-\rho_y)^k
   =\rho_y(1-\rho_y)^k+(1-\rho_y)(-\rho_y)^k.             \tag{5}
\]

The reason is pointwise: sum_(x in B_y)(I_(x,y)-p)=J_y-rho_y. Expanding its
k-th power includes precisely all those ordered point tuples, with their signs.
For even k>=2, (5) lies between zero and rho_y, since |J_y-rho_y|<=1 and
its second moment is rho_y(1-rho_y). Summing over y and normalizing by mu^k
therefore contributes at most mu^(1-k), rather than the enormous value (1).
This is a bound on one class of contributions, not on the full moment.

## Exact grouped formula for the remaining dependencies

For a set T of distinct inputs let r(T) be the augmented input rank. Let N(T)
count choices x_y in B_y for y in T such that (1,y)->x_y extends linearly.
The joint incidence formula gives

\[
       P(T):=\Pr(J_y=1\text{ for all }y\in T)=N(T)/Q^{r(T)}.       \tag{6}
\]

Set P(empty)=1. If the inputs in T are independent, every output assignment is
consistent, so P(T)=product_(y in T) rho_y. No such factorization is asserted
for dependent inputs.

For positive multiplicities e_y on a support T, use the exact Bernoulli identity

\[
 (J_y-\rho_y)^{e_y}=\alpha_y J_y+\beta_y,\quad
 \alpha_y=(1-\rho_y)^{e_y}-(-\rho_y)^{e_y},\quad
 \beta_y=(-\rho_y)^{e_y}.
\]

It follows that

\[
 \mathbb E\prod_{y\in T}(J_y-\rho_y)^{e_y}
 =\sum_{U\subseteq T}P(U)
      \prod_{y\in U}\alpha_y\prod_{y\in T\setminus U}\beta_y.    \tag{7}
\]

Summing (7) over multiplicity vectors of total k with coefficients
k!/product_y(e_y!) gives the exact k-th centered moment of Z. The sign of alpha_y
is not assumed positive; this matters for even multiplicities when rho_y>1/2.
For independent supports, the expression factors into the one-input moments (5).
If a support input is independent of all the others and has multiplicity one,
its contribution vanishes, by conditioning on the other input span. These are
exact consequences of the affine law, not independence of all the inputs.

Equations (6)--(7) retain compatibility counts for genuinely distinct inputs.
They remove the rank-one obstruction above but do not estimate those counts for
the actual high-dimensional integer ball. A usable high-order bound still needs
these dependent-support counts with their signs or a suitably controlled error.
Moreover, the fixed raw-ball obstruction at draw 16 in Part 250 still applies:
no improvement to the moment method for that same ball resolves the later
selected-projection problem.

## Verification

Run `python3 docs/research/scripts/wall1_affine_fiber_moments.py`. Over every
nonempty subset of four fixtures, the script compares exact averages over all
affine maps with (6), the variance (4), and the grouped central moments (7) at
orders 2, 4, 8. It also checks (5), the power-mean bound (1), and the integer
comparison (2). There are 908 candidate sets, including varying fiber sizes,
full and partial output fibers, dependent triples of inputs, and a circuit with
an independent fourth input. The latter also checks the exact nullity-one
factorization in [Part 253](wall1_affine_nullity_one.md). Finite tests
do not replace the general proofs above; none of this note is yet formalized.
