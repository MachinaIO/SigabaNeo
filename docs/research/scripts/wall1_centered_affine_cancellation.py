"""Exact regressions for the centered affine-matroid identity (no simulations)."""
from fractions import Fraction
from itertools import combinations_with_replacement, product
from collections import Counter


def relation_vectors(rows, q):
    """Enumerate the scalar relation kernel, using free coordinates after RREF."""
    k = len(rows)
    a = [[rows[j][i] % q for j in range(k)] for i in range(len(rows[0]))]
    pivots = []
    for j in range(k):
        r = len(pivots)
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][j], -1, q)
        a[r] = [x*inv % q for x in a[r]]
        for i in range(len(a)):
            if i != r:
                c = a[i][j]
                a[i] = [(x-c*y) % q for x, y in zip(a[i], a[r])]
        pivots.append(j)
    free = [j for j in range(k) if j not in pivots]
    vectors = []
    for values in product(range(q), repeat=len(free)):
        v = [0]*k
        for j, x in zip(free, values):
            v[j] = x
        for i, j in enumerate(pivots):
            v[j] = -sum(a[i][l]*v[l] for l in free) % q
        assert all(sum(v[j]*rows[j][i] for j in range(k)) % q == 0
                   for i in range(len(rows[0])))
        vectors.append(v)
    return vectors


def relation_histogram(rows, outputs, m, q):
    """Full-support block relations, grouped by their scalar output pairing."""
    kernel = relation_vectors(rows, q)
    counts = Counter()
    extension_counts = Counter()
    assert m == 1 or (q, m) == (2, 2)
    for a in product(kernel, repeat=m):
        if all(any(a[i][j] for i in range(m)) for j in range(len(rows))):
            phase = sum(a[i][j]*outputs[j][i]
                        for i in range(m) for j in range(len(rows))) % q
            counts[phase] += 1
            extension_phase = 0
            for j in range(len(rows)):
                if m == 1:
                    extension_phase = (extension_phase+a[0][j]*outputs[j][0]) % q
                else:
                    # F_4 = F_2[t]/(t^2+t+1), coefficients in order (1,t).
                    a0, a1 = a[0][j], a[1][j]
                    b0, b1 = outputs[j]
                    value = ((a0*b0+a1*b1) % 2
                             + 2*((a0*b1+a1*b0+a1*b1) % 2))
                    extension_phase ^= value
            extension_counts[extension_phase] += 1
    return counts, extension_counts


def rank(rows, q):
    a = [list(row) for row in rows]
    r = 0
    for j in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(r, len(a)) if a[i][j] % q), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        a[r] = [x * pow(a[r][j] % q, -1, q) % q for x in a[r]]
        for i in range(len(a)):
            if i != r:
                c = a[i][j]
                a[i] = [(x-c*y) % q for x, y in zip(a[i], a[r])]
        r += 1
    return r


def check(points, m, q, extra=()):
    d = len(points[0])-m
    p = Fraction(1, q**m)
    laws = []
    for coefficients in product(range(q), repeat=m*(d+1)):
        laws.append([int(all(
            (point[row]-sum(coefficients[row*(d+1)+j]*y
                           for j, y in enumerate((1, *point[m:])))) % q == 0
            for row in range(m))) for point in points])
    tuples = [t for k in range(1, 5)
              for t in combinations_with_replacement(range(len(points)), k)] + list(extra)
    cancellations = 0
    for t in tuples:
        rows = [(1, *points[i][m:]) for i in t]
        full = [(1, *points[i]) for i in t]
        r = rank(rows, q)
        coloop = any(rank(rows[:j]+rows[j+1:], q) < r for j in range(len(t)))
        exact = sum((prod(Fraction(law[i])-p for i in t) for law in laws), Fraction(0))
        exact /= len(laws)
        expansion = Fraction(0)
        count_expansion = zero_expansion = extension_zero_expansion = 0
        for mask in range(1 << len(t)):
            selected = [j for j in range(len(t)) if mask >> j & 1]
            rs = rank([rows[j] for j in selected], q)
            consistent = rank([full[j] for j in selected], q) == rs
            dimension = m*(len(selected)-rs)
            sign = (-1)**(len(t)-len(selected))
            count_expansion += sign*q**dimension
            assert consistent or dimension > 0
            zero_expansion += sign*q**(dimension-int(not consistent))
            extension_zero_expansion += sign*(q**m)**(
                len(selected)-rs-int(not consistent))
            if consistent:
                expansion += (-p)**(len(t)-len(selected))*p**rs
        assert exact == expansion
        assert abs(exact) <= 2**len(t)*p**r
        histogram, extension = relation_histogram(rows, [points[i][:m] for i in t], m, q)
        D = sum(histogram.values())
        D0 = histogram[0]
        assert D == count_expansion and D0 == zero_expansion
        assert extension[0] == extension_zero_expansion
        assert sum(extension.values()) == D
        assert len({extension[a] for a in range(1, q**m)}) == 1
        assert exact == p**len(t)*Fraction(q**m*extension[0]-D, q**m-1)
        assert -p**len(t)*Fraction(D, q**m-1) <= exact
        # Multiplication by a nonzero scalar permutes the nonzero phase fibers.
        assert len({histogram[a] for a in range(1, q)}) == 1
        assert exact == p**len(t)*Fraction(q*D0-D, q-1)
        assert -p**len(t)*Fraction(D, q-1) <= exact <= p**len(t)*D
        assert D <= (q**m-1)**(len(t)-r)
        assert abs(exact) <= p**r*(1-p)**(len(t)-r)
        if rank(full, q) == r:
            assert D0 == D
            assert exact == p**len(t)*D
        if r == len(t)-1 and not coloop:
            assert D == q**m-1
            assert exact == (p**r*(1-p) if rank(full, q) == r else -p**len(t))
        if coloop:
            assert exact == 0
            cancellations += 1
    return len(tuples), cancellations


def prod(values):
    result = Fraction(1)
    for v in values:
        result *= v
    return result


if __name__ == '__main__':
    fixtures = [
        (list(product(range(3), repeat=2)), 1, 3, [(0,)*8]),
        (list(product(range(2), repeat=3)), 2, 2, [(0,)*8]),
        ([(0, 0), (1, 0), (1, 1), (2, 2)], 1, 5, []),
        ([(0, 0, 0, 0, 0), (1, 1, 0, 0, 0), (0, 0, 1, 0, 0),
          (0, 0, 0, 1, 0), (0, 0, 0, 0, 1), (1, 1, 1, 1, 2)],
         1, 3, [tuple(range(6)), (0, 0, 1, 1, 2, 2)])]
    total = cancelled = 0
    for args in fixtures:
        cases, zeros = check(*args)
        total += cases
        cancelled += zeros
        print(f'Passed {cases} tuple multisets; {zeros} coloop cancellations.')
    print(f'All {total} exact identities passed, including {cancelled} forced zeros.')
