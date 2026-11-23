"""Joint (competitor count, collision count) square certificates, exact rationals."""
from fractions import Fraction as F
from optimal_void_square import optimal_square, weighted_gram
from void_square_polynomial import falling


def joint_gram(rows, degree, threshold, *, event_count):
    """Basis: 1, J-threshold, (Z)_1, J(Z)_1, ..., (Z)_t, J(Z)_t."""
    if any(len(row) != 3 for row in rows):
        raise ValueError('expected the three collision moment columns')
    blocks = [weighted_gram([row[p] for row in rows], degree, event_count=event_count)
              for p in range(3)]
    size = 2*(degree+1)
    raw = [[blocks[a % 2+b % 2][a//2][b//2] for b in range(size)] for a in range(size)]
    transforms = [[(i, F(1))] for i in range(size)]
    transforms[1] = [(0, -F(threshold)), (1, F(1))]
    return [[sum(x*y*raw[r][s] for r, x in left for s, y in right)
             for right in transforms] for left in transforms]


def optimal_one_sided_square(matrix):
    """Minimize c^T M c with c[0]=1 and c[1]>=0, including singular M."""
    if len(matrix) < 2:
        raise ValueError('a tail slope coordinate is required')
    coefficients, value = optimal_square(matrix)
    if coefficients[1] < 0:
        indices = [i for i in range(len(matrix)) if i != 1]
        reduced = [[matrix[i][j] for j in indices] for i in indices]
        boundary, value = optimal_square(reduced)
        coefficients = boundary[:1]+[F(0)]+boundary[1:]
    gradient = [sum(F(entry)*c for entry, c in zip(row, coefficients)) for row in matrix]
    assert coefficients[0] == 1 and coefficients[1] >= 0
    assert gradient[1] >= 0 and coefficients[1]*gradient[1] == 0
    assert all(v == 0 for v in gradient[2:])
    assert value == sum(c*v for c, v in zip(coefficients, gradient)) >= 0
    return coefficients, value


def evaluate(coefficients, z, j, threshold):
    if len(coefficients) < 2 or len(coefficients) % 2:
        raise ValueError('expected paired coefficients for each competitor degree')
    return (coefficients[0]+coefficients[1]*(j-threshold)
            + sum((coefficients[2*h]+j*coefficients[2*h+1])*falling(z, h)
                  for h in range(1, len(coefficients)//2)))
