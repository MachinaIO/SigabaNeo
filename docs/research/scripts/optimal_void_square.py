"""Exact weighted square optimization from supplied mixed subset moments.

PSD validation checks algebraic consistency, not the provenance of the moments.
"""
from fractions import Fraction as F
from math import comb, factorial


def weighted_gram(subset_moments, degree, *, event_count):
    if (degree < 0 or event_count < 0
            or len(subset_moments) < min(2*degree, event_count)+1
            or len(subset_moments) > event_count+1):
        raise ValueError('missing or invalid mixed moment range')
    moments = [F(value) for value in subset_moments]
    if any(value < 0 for value in moments):
        raise ValueError('nonnegative weights require nonnegative subset moments')
    moments += [F(0)]*max(0, 2*degree+1-len(moments))
    return [[sum(comb(i, v)*comb(j, v)*factorial(v)*factorial(i+j-v)*moments[i+j-v]
                 for v in range(min(i, j)+1)) for j in range(degree+1)]
            for i in range(degree+1)]


def check_psd(matrix):
    """Exact Schur-complement test, allowing zero pivots and singular matrices."""
    n = len(matrix)
    if not n or any(len(row) != n for row in matrix):
        raise ValueError('expected a nonempty square matrix')
    work = [[F(value) for value in row] for row in matrix]
    if any(work[i][j] != work[j][i] for i in range(n) for j in range(n)):
        raise ValueError('matrix is not symmetric')
    for pivot in range(n):
        value = work[pivot][pivot]
        if value < 0:
            raise ValueError('matrix is not positive semidefinite')
        if value == 0:
            if any(work[pivot][j] for j in range(pivot+1, n)):
                raise ValueError('zero diagonal with a nonzero row is not PSD')
            continue
        for i in range(pivot+1, n):
            for j in range(pivot+1, n):
                work[i][j] -= work[i][pivot]*work[pivot][j]/value


def optimal_square(matrix):
    """Return (falling-basis coefficients c with c[0]=1, c^T M c).

    For PSD M, solving the stationarity equations proves global optimality,
    including when M or its lower principal block is singular.
    """
    check_psd(matrix)
    matrix = [[F(value) for value in row] for row in matrix]
    n = len(matrix)-1
    rows = [matrix[i+1][1:]+[-matrix[i+1][0]] for i in range(n)]
    pivots = []
    for column in range(n):
        pivot = next((i for i in range(len(pivots), n) if rows[i][column]), None)
        if pivot is None:
            continue
        row = len(pivots)
        rows[row], rows[pivot] = rows[pivot], rows[row]
        denominator = rows[row][column]
        rows[row] = [value/denominator for value in rows[row]]
        for i in range(n):
            if i != row:
                factor = rows[i][column]
                rows[i] = [a-factor*b for a, b in zip(rows[i], rows[row])]
        pivots.append(column)
    if any(not any(row[:n]) and row[n] for row in rows):
        raise ValueError('inconsistent stationarity equations')
    coefficients = [F(1)]+[F(0)]*n
    for row, column in enumerate(pivots):
        coefficients[column+1] = rows[row][n]
    product = [sum(value*c for value, c in zip(row, coefficients)) for row in matrix]
    assert all(value == 0 for value in product[1:])
    value = sum(c*v for c, v in zip(coefficients, product))
    assert value >= 0 and value == product[0]
    return coefficients, value
