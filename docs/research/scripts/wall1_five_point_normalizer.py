"""Exhaustive canonical unit-minor charts for the six H5 girth-three codes.

Enumerate the same 15 balanced norm-four lines as five_point_short_codes.
For pairs of these lines all cancellations occur at slopes 0, 1, -1,
or infinity; other slopes retain the full support union. Thus testing
these four directions determines the prescribed supports and girth.
The unique C3 direction has one coefficient of magnitude two. Choosing
that position together with the two new positions as basis yields a
unit-minor chart, without multiplying the six-code witness count.

For every resulting chart det(I+A^T A)=15. Poisson summation therefore
gives psi_A(0)>=max(h_old^3, q^2*alpha/(pi*sqrt(15))). This is H5,
not the distinct H7 shared-four determinant-15 family.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import prod

from wall1_five_point_short_codes import rref
from wall1_short_relation_shapes import balanced_rows
from wall1_correlated_anchor_moments import inverse, ldl_pivots, multiply, transpose


def canonical_charts(q=3329, overlap=2):
    """Return code -> (basis, exact A), recovered from exhaustive short pairs."""
    rows = [row for support in combinations(range(5), 4)
            for row in balanced_rows(support, 5)]
    assert len(rows) == 15 and overlap in (1, 2)
    crossing = tuple(range(overlap)) + (3, 4)
    charts = {}
    for a, b in combinations(rows, 2):
        words = [b, a, tuple(x+y for x, y in zip(a, b)),
                 tuple(x-y for x, y in zip(a, b))]
        supports = [tuple(i for i, x in enumerate(w) if x % q) for w in words]
        if not (min(map(len, supports)) >= 3 and (0, 1, 2) in supports
                and crossing in supports):
            continue
        assert abs(sum(x*y for x, y in zip(a, b))) == 1
        short = words[supports.index((0, 1, 2))]
        assert sorted(abs(x) for x in short if x) == [1, 1, 2]
        center = next(i for i, x in enumerate(short) if abs(x) == 2)
        basis = (center, 3, 4)
        omitted = tuple(i for i in range(3) if i != center)
        dep = [[F(row[i]) for i in omitted] for row in (a, b)]
        assert abs(dep[0][0]*dep[1][1]-dep[0][1]*dep[1][0]) == 1
        rhs = [[-F(row[i]) for i in basis] for row in (a, b)]
        A = transpose(multiply(inverse(dep), rhs))
        assert multiply(dep, transpose(A)) == rhs
        assert [sum(col) for col in transpose(A)] == [1, 1]
        small = multiply(transpose(A), A)
        assert small == [[3, -1], [-1, 3]]
        assert A[0] == [1, 1] and sorted(A[1:]) == [[-1, 1], [1, -1]]
        # Reconstruct the full relation code from this exact chart.
        chart_rows = []
        for j, position in enumerate(omitted):
            row = [F(0)]*5
            row[position] = 1
            for i, point in enumerate(basis):
                row[point] = -A[i][j]
            chart_rows.append(tuple(int(x) for x in row))
        code = rref(a, b, q)
        assert rref(*chart_rows, q) == code
        value = (basis, tuple(map(tuple, A)))
        if code in charts:
            assert charts[code] == value
        charts[code] = value
    return charts


def checks():
    profiles = set()
    for q in (7, 17, 3329):
        assert not canonical_charts(q, overlap=1)
        charts = canonical_charts(q)
        assert len(charts) == 6
        assert Counter(basis[0] for basis, A in charts.values()) == {0: 2, 1: 2, 2: 2}
        for basis, A in charts.values():
            g = multiply(A, transpose(A))
            for i in range(3):
                g[i][i] += 1
            assert prod(ldl_pivots(g)) == 15 and sum(map(sum, g)) == 5
            m = inverse(g)
            E = [[F(i == j)-F(i == 2) for j in range(2)] for i in range(3)]
            full = ldl_pivots(m)
            root = ldl_pivots(multiply(transpose(E), multiply(m, E)))
            assert full == (F(1, 3), F(3, 5), F(1, 3))
            assert root == (F(14, 15), F(5, 14))
            assert prod(full) == F(1, 15) and prod(root) == F(1, 3)
            profiles.add((full, root))
        print(f'q={q}: six canonical charts, centers 2/2/2; overlap1 empty.')
    assert len(profiles) == 1
    from wall1_anchored_dual_completion import canonical_moment_profiles
    assert set(canonical_moment_profiles(5)[15]) == profiles
    print('Passed unit minors, reconstructed codes, affine sums, Gram15, and exact full/root LDL.')


def completion_checks():
    """Exercise the actual H5 dispatch, cache separation, and input fallback."""
    from mpmath import iv
    from wall1_anchored_dual_completion import correlated_moments, completion_details
    iv.dps = 45
    I = iv.mpf
    q = 3329
    R2 = I('1.21')*iv.exp(2*(386*iv.log(q)
         -iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    state = {'iv': iv, 'q': q, 'N': 518, 'radius': iv.sqrt(R2)}
    alpha = I(3*518)/(10*R2)
    h5 = correlated_moments(q, alpha, 4, 15, 5)
    h7 = correlated_moments(q, alpha, 4, 15, 7)
    assert h5 is not h7
    assert h5 is correlated_moments(q, alpha, 4, 15, 5)
    for rank in (3, 8):
        input_cap = completion_details(state, rank, 15, anchor_size=5,
                                      anchor_gram_det=15)
        full_cap = completion_details(state, rank, 15, anchor_size=5,
                                     anchor_gram_det=15, coordinate_count=518)
        assert 0 < full_cap[0] and full_cap[0].b <= input_cap[0].b
        assert full_cap is completion_details(state, rank, 15, anchor_size=5,
                                             anchor_gram_det=15, coordinate_count=518)
        print('H5 completion regression rank,size,logcap:', rank, 15, iv.log10(full_cap[0]))
    print('Passed H5/H7 cache separation and both zero/free-extension completion paths.')


if __name__ == '__main__':
    checks()
    completion_checks()
