"""Independent finite checks for the generating-column base-packing bound.

Edmonds base packing theorem: a rank-k matroid has L disjoint bases iff
|E\\X| >= L(k-rank(X)) for every X. Verified statement: Theorem 10,
de Vos--Grilnberger, Dynamic Matroids: Base Packing and Covering, ESA 2026:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol388-esa2026/html/LIPIcs.ESA.2026.57/LIPIcs.ESA.2026.57.html

For rank-deficient columns their full span is already a failure witness.
Otherwise the theorem gives W spanned by some inside columns with fewer
than L*codim(W) outside columns. Choose t=dim(W) generating columns first.
Conditional on those columns, the remaining independent columns hit W
with probability <=M**(k-t), by coordinate pivots and the max-atom bound.
The outside-count CDF is therefore dominated by Bin(n-t,1-M**(k-t)).
Union over the comb(n,t) possible generators and t=0,...,k-1.
This uses monotonicity of the whole CDF, not a termwise probability bound.

For f_j=comb(N,j)*(1-p)**j*p**(N-j),
f_(j-1)/f_j=j*p/((N-j+1)*(1-p)) increases with j. If its value rho
at cutoff b is <1, the lower CDF is at most f_b/(1-rho). This includes
all terms, without omitting a binomial tail. If rho>=1 use the bound 1.
All probabilities here concern independent auxiliary columns, not history.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from math import comb, factorial, prod


def binomial_cdf(N, b, p):
    """Exact outside-count CDF, with inside probability p (rational inputs)."""
    return sum((comb(N, j)*(1-p)**j*p**(N-j)
                for j in range(b+1)), F(0))


def geometric_cdf(N, b, p):
    assert 0 <= b < N and 0 < p < 1
    ratio = F(b, N-b+1)*p/(1-p)
    if ratio >= 1:
        return F(1)
    return min(F(1), comb(N, b)*(1-p)**b*p**(N-b)/(1-ratio))


def packing_bound(n, k, L, atom, *, geometric=False):
    """Standalone rational witness bound; production uses interval arithmetic."""
    assert n >= L*k and 0 < atom < 1
    cdf = geometric_cdf if geometric else binomial_cdf
    return min(F(1), sum((comb(n, k-c)*cdf(n-k+c, L*c-1, atom**c)
                         for c in range(1, k+1)), F(0)))


def rank(rows, q):
    rows = [list(row) for row in rows]
    if not rows:
        return 0
    pivot = 0
    for j in range(len(rows[0])):
        hit = next((i for i in range(pivot, len(rows)) if rows[i][j] % q), None)
        if hit is None:
            continue
        rows[pivot], rows[hit] = rows[hit], rows[pivot]
        inv = pow(rows[pivot][j] % q, -1, q)
        rows[pivot] = [x*inv % q for x in rows[pivot]]
        for i in range(pivot+1, len(rows)):
            factor = rows[i][j]
            rows[i] = [(x-factor*y) % q for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def has_two_bases(cols, q, k):
    return any(rank([cols[i] for i in S], q) == k
               and rank([v for i, v in enumerate(cols) if i not in S], q) == k
               for S in combinations(range(len(cols)), k))


def has_witness(cols, q, k, L):
    for t in range(k):
        for S in combinations(range(len(cols)), t):
            basis = [cols[i] for i in S]
            if rank(basis, q) != t:
                continue
            outside = sum(rank(basis+[v], q) > t for v in cols)
            if outside < L*(k-t):
                return True
    return False


def checks():
    for q, k in ((2, 2), (3, 2), (2, 3)):
        n = 2*k
        vectors = list(product(range(q), repeat=k))
        checked = 0
        for ids in combinations_with_replacement(range(len(vectors)), n):
            cols = [vectors[i] for i in ids]
            assert has_two_bases(cols, q, k) != has_witness(cols, q, k, 2)
            checked += 1
        print('Exhaustive witnesses q,k,n,multisets:', q, k, n, checked)
    # Nonuniform product law: each scalar is zero with probability 2/3.
    vectors = list(product(range(2), repeat=2))
    probs = [prod(F(2, 3) if x == 0 else F(1, 3) for x in v) for v in vectors]
    for n in (4, 8, 12):
        failure = F(0)
        total = F(0)
        for ids in combinations_with_replacement(range(4), n):
            counts = Counter(ids)
            multiplicity = factorial(n)//prod(factorial(v) for v in counts.values())
            mass = multiplicity*prod(probs[i]**count for i, count in counts.items())
            total += mass
            if not has_two_bases([vectors[i] for i in ids], 2, 2):
                failure += mass
        exact = packing_bound(n, 2, 2, F(2, 3))
        geometric = packing_bound(n, 2, 2, F(2, 3), geometric=True)
        assert total == 1 and failure <= exact <= geometric <= 1
        print('Weighted law n,actual,bound,geometric:', n, float(failure), float(exact), float(geometric))
    tested = 0
    for N in (2, 5, 20, 50):
        for b in range(N):
            for p in (F(1, 100), F(1, 3), F(2, 3), F(99, 100)):
                assert binomial_cdf(N, b, p) <= geometric_cdf(N, b, p)
                ratios = [F(j, N-j+1)*p/(1-p) for j in range(1, b+1)]
                assert ratios == sorted(ratios)
                tested += 1
    print('Passed exact CDF/geometric checks:', tested)


if __name__ == '__main__':
    checks()
