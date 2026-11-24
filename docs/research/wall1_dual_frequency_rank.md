# Gaussian-weighted modular rank of shared completion frequencies

This bounds modular rank deficiency for the bare product discrete Gaussian
factor in [mixed Gram kernels](wall1_mixed_gram_kernel.md), retaining every
integer alias. The dual exponent is tau=pi²/(q² gamma_c), where gamma_c is
the **primal** completion weight. The two parameters must not be identified.
At gamma_c=10^(-7), rank deficiency is almost certain; at gamma_c=6.85e−6,
the same rigorous bound is very small. Neither statement incorporates a further
anchor-dependent tilt.

## Exact residue distribution and its largest atom

Let q be prime (q=3329 in the application). Write theta(tau)=sum_(z in Z) exp(−tau z²). Let the entries of an integer
k by n matrix B be independent with mass exp(−tau b²)/theta(tau).
Their reductions modulo q have the exact, generally nonuniform distribution

    p_tau(c)=theta(tau)^(-1)
                    sum_(z in Z) exp(−tau(c+qz)²).        (1)

The maximum atom is attained at c=0 and equals

    M=theta(tau q²)/theta(tau).                         (2)

To prove maximality, periodize exp(−tau x²) with period q. Its Fourier
coefficients are positive, namely sqrt(pi/tau)/q times
exp(−pi² ell²/(tau q²)). The real Fourier sum is largest at zero since
every cosine is at most one. This proves (2), including all aliases rather
than replacing (1) with either a uniform law or a nearest representative.
Poisson summation also gives

    q M = theta(pi²/(tau q²))/theta(pi²/tau).

For a=pi²/(tau q²), use j²>=1+3(j−1) for j>=1 and denominator>=1 to get

    q M <= C(tau,q):=1+2 exp(−a)/(1−exp(−3a)).            (3)

The nearly uniform residue regime corresponds to small dual tau. It does not
follow from a small primal gamma_c: these exponents are reciprocal up to pi²/q².
For the actual numerical cases below, we evaluate (2) directly with certified
theta tails instead of using the potentially loose estimate (3).

## Subspace bound via systematic coordinates

For any distribution on F_q with largest atom M, and a vector of k independent
entries from that distribution, every t-dimensional linear subspace L obeys

    Pr[column in L] <= M^(k−t).                            (4)

Choose t coordinate positions whose projection is injective on L. For each
assignment to these free coordinates there is exactly one assignment to the
remaining coordinates in L. Its conditional probability is at most M^(k−t).
Sum the probabilities of all assignments to the free coordinates; their total
is one. No uniformity of the entries was used.

Independence across the n columns therefore gives Pr[all columns in L]
<=M^(n(k−t)). Every matrix of rank at most t has column space contained in
some t-dimensional subspace. There are exactly the Gaussian binomial number

    [k choose t]_q = product_(j=0)^(t−1) (q^(k−j)−1)/(q^(t−j)−1)

of these subspaces: count their ordered independent bases and divide by the
number of bases per subspace. The union bound proves

    Pr[rank(B mod q)<=t]
       <= min(1, [k choose t]_q M^(n(k−t))).                (5)

For rank deficiency alone one may use t=k−1. Equivalently, union over the
(q^k−1)/(q−1) projective annihilators; the largest-atom bound preserves the
small-frequency structure without pretending those annihilators are uniform.
For the unnormalized integer Gaussian sum, multiply (5) by theta(tau)^(kn).

The same proof works for independent nonidentically distributed entries with
a common maximum-atom bound. It does not apply to arbitrarily correlated
rows or columns having only those one-entry marginals.

## Concrete n=118, k=6 calculation and a rank-loss tilt

First, for any d>=0 the rank-tail bound gives

    E[q^(d(k−rank(B)))]−1
      <= sum_(t=0)^(k−1) (q^(d(k−t))−1)
                            [k choose t]_q M^(n(k−t)).    (6)

Indeed split the expectation by exact rank t, then upper-bound that probability
by (5). This is useful if a separate coefficient-averaging argument bounds
its loss by q^(d(k−t)) and treats the full-rank term with unit loss.
That coefficient-averaging inequality is not proved here.

With q=3329, k=6, n=118 and d=10, outward interval arithmetic gives:

| Primal gamma_c | Dual tau=pi²/(q² gamma_c) | M, approximately | Consequence |
|---|---:|---:|---|
| 10^(-7) | 8.90578394847 | 0.999728868858 | Rank deficiency >0.9999999990246 |
| 6.85e−6 | 0.130011444503 | 0.203430401126 | Rank deficiency <1.012e−64 |

In the second case (6) is less than 1.691e−29. These statements are for the
normalized bare product Gaussian law, not absolute estimates of an
unnormalized dual series. Multiply a probability bound by theta(tau)^(kn)
when using the unnormalized sum.

The first row is a rigorous obstruction to a full-rank-dominance argument at
that primal exponent. A row of B is zero modulo q with probability M^n, and
the k row events are independent. Thus

    Pr[rank B<k] >= 1−(1−M^n)^k.                           (7)

This lower bound gives the stated 0.9999999990246. The subspace union bound
there is greater than one and supplies no improvement; the result is not a
contradiction, because the Gaussian concentrates strongly on zero frequencies.
In contrast, at the second exponent the 118 independent columns overcome the
nonuniformity even though M is far larger than 1/q.

The value 6.85e−6 is evaluated exactly as written. Identifying it with an
optimal or actual production completion exponent requires inserting that
exponent into the same formulas; no parameter optimization is claimed.

## Boundary with the actual mixed dual kernel

The joint dual expansion contains both the product Gaussian in the completion
frequency block B and terms coupling B to anchor frequencies and the shared
coefficient matrices. The n=118 rows all use the same affine coefficient
matrix, so one cannot independently average that matrix for each row.
Equations (5)--(7) apply to the product Gaussian factor before that coupling.
For an additional nonnegative multiplier G(B), a safe unnormalized estimate is

    sum_(rank B<=t) exp(−tau ||B||_F²) G(B)
       <= sup_(rank B<=t) G(B) * theta(tau)^(kn)
                                 [k choose t]_q M^(n(k−t)),

if the displayed supremum is finite. Alternatively, derive and use a bound
on the conditional expectation of G given B. A normalized tilted probability
also requires a lower bound on its normalizer. Gaussian terms involving
additional summed anchor frequencies are not bounded by one merely because
each individual summand is at most one.

Thus the result supplies a strong rank-deficiency estimate for the actual
integer Gaussian factor, with exact modular aliases. The remaining bridge is
the shared-coefficient/anchor-frequency coupling. It neither proves a new
completion envelope nor closes the selected-history BKZ argument.

## Verification

Run `python3 docs/research/scripts/wall1_dual_frequency_rank.py`.
The script enumerates small matrices over F_2 and F_3 with uniform and explicitly
nonuniform product weights; all 28 exact rational rank-tail checks pass. It
then evaluates (2), (5), (6), and (7) with 60-digit outward interval arithmetic.
For theta(t), it sums j=−100,...,100 and bounds the omitted positive tail by
2 exp(−101² t)/(1−exp(−203t)); the ratio bound follows from consecutive squares.
No random sampling or unbounded truncation error is used. The all-size proof is the systematic-coordinate argument above.
