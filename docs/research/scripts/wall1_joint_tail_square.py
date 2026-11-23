"""Exact joint-law tests and active-boundary checks for bivariate certificates."""
from fractions import Fraction as F
from itertools import product
from math import comb
from joint_tail_square import evaluate, joint_gram, optimal_one_sided_square

support = ((0, 0), (0, 2), (1, 1), (2, 3))
checks = 0
for weights in product(range(3), repeat=len(support)):
    rows = [[sum(w*j**p*comb(z, h) for w, (z, j) in zip(weights, support))
             for p in range(3)] for h in range(3)]
    for degree in range(3):
        matrix = joint_gram(rows, degree, 2, event_count=2)
        coefficients, value = optimal_one_sided_square(matrix)
        direct = sum(w*evaluate(coefficients, z, j, 2)**2
                     for w, (z, j) in zip(weights, support))
        assert direct == value >= weights[1]
        for j in range(2, 8):
            assert evaluate(coefficients, 0, j, 2) >= 1
        if degree == 2:
            # p(z,j)=(j/2)(1-z)(1-z/2) attains the exact target-event weight.
            assert value == weights[1]
        checks += 1

fixtures = (
    ([[1, 1], [1, 1]], F(1)),  # Unconstrained negative slope; boundary is required.
    ([[1, -1], [-1, 1]], F(0)),
    ([[0, 0], [0, 0]], F(0)),
    ([[1, 1, 1], [1, 1, 1], [1, 1, 1]], F(0)),  # Singular nonunique minimizers.
)
for matrix, target in fixtures:
    coefficients, value = optimal_one_sided_square(matrix)
    assert value == target
    for tail in (F(0), F(1, 2), F(1), F(3)):
        for free in product((F(-2), F(0), F(2)), repeat=len(matrix)-2):
            candidate = [F(1), tail]+list(free)
            objective = sum(candidate[i]*matrix[i][j]*candidate[j]
                            for i in range(len(matrix)) for j in range(len(matrix)))
            assert value <= objective
print(f'Passed {checks} joint finite-law optimizations and four boundary/singular fixtures.')
