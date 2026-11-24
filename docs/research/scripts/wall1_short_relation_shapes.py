"""Finite checks for short relation shapes and the integer pair-sum bound."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial
from mpmath import iv


def half_factorial(twice_argument):
    """Gamma(twice_argument/2+1), using exact integer factorials and sqrt(pi)."""
    assert isinstance(twice_argument,int) and twice_argument >= 0
    if twice_argument % 2 == 0:
        return iv.mpf(factorial(twice_argument//2))
    k = (twice_argument+1)//2
    return iv.mpf(factorial(2*k))/(4**k*factorial(k))*iv.sqrt(iv.pi)


def equal_pair_sum_ball_bound(radius_sq, dimension, pairs):
    assert dimension > 0 and pairs >= 2
    n, k = dimension, pairs
    exponent = iv.mpf((k+1)*n)/2
    return (iv.mpf(2)**(k+1+n)*iv.pi**exponent*half_factorial(k*n)
            /half_factorial(n)**k/half_factorial((k+1)*n)
            *(radius_sq+iv.mpf(5)*n/16)**exponent)


def pair_sum_ball_bound(radius_sq, dimension):
    return equal_pair_sum_ball_bound(radius_sq, dimension, 3)


def orthogonal_pair_ball_bound(radius_sq, dimension):
    """Count r(x+y) r(x-y) over x,y in the ball, with clipping dropped."""
    n = dimension
    assert n > 0
    return (8*iv.mpf(4)**n*iv.pi**(2*n)*factorial(n)
            /half_factorial(n)**2/factorial(2*n)
            *(radius_sq+iv.mpf(3)*n/8)**(2*n))


def orthogonal_pair_alias_bound(radius_sq, dimension, q):
    n = dimension
    beta = iv.mpf(n)/(3*radius_sq)
    def theta(x):
        geometric = lambda a: 1+2*iv.exp(-a)/(1-iv.exp(-3*a))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    return (iv.exp(6*beta*radius_sq)*theta(2*beta)**(4*n)
            *(theta(beta*q*q/4)**(2*n)-1))


def shared_four_gaussian_bound(radius_sq, dimension, q, *, aliases_only=False):
    """Two four-circuits sharing one point, with all modular layers."""
    n = dimension
    center = iv.mpf(n)/(4*radius_sq)
    leaf = iv.mpf(3*n)/(8*radius_sq)
    def theta(x):
        geometric = lambda a: 1+2*iv.exp(-a)/(1-iv.exp(-3*a))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    kernel = theta(2*leaf)**2*theta(iv.mpf(3)*leaf/2)**2*theta(center+2*leaf/3)
    layer = q*q*center*leaf/(3*center+2*leaf)
    layers = theta(layer)**(2*n)
    if aliases_only:
        layers -= 1
    return iv.exp((center+6*leaf)*radius_sq)*kernel**n*layers


def shared_four_ball_bound(radius_sq, dimension):
    """Sum of squared triple counts over a common point in the ball."""
    n = dimension
    assert n > 0
    p = iv.mpf(n)/2
    outer = radius_sq+iv.mpf(n)/4
    boundary = iv.mpf(8)*radius_sq/3+iv.mpf(3)*n/2
    ratio = 2*n*outer/(3*boundary*(p+1))
    assert ratio.b < 1
    factor = iv.pi**(iv.mpf(5)*n/2)/factorial(n)**2/half_factorial(n)/iv.mpf(3)**n
    best = 8*factor*outer**p*boundary**(2*n)/(1-ratio)
    # Cantelli improves the uniform half-cube loss. For the triple-sum
    # kernel G has largest eigenvalue 3, so Var(2<z,Ge>) <= 3R^2.
    # For the outer unit lattice the variance is <= R^2/3.
    radius = iv.sqrt(radius_sq)
    for triple_margin in (2,3,4,5,6,7,8):
        triple_factor = 1+iv.mpf(3)/triple_margin**2
        enlarged_boundary = boundary+triple_margin*radius
        for outer_margin in (1,2,3,4):
            outer_factor = 1+iv.mpf(1)/(3*outer_margin**2)
            enlarged_outer = outer+outer_margin*radius
            rho = 2*n*enlarged_outer/(3*enlarged_boundary*(p+1))
            if rho.b >= 1:
                continue
            candidate = (triple_factor**2*outer_factor*factor
                         *enlarged_outer**p*enlarged_boundary**(2*n)/(1-rho))
            if candidate.b < best.b:
                best = candidate
    return best


def equal_pair_sum_alias_bound(radius_sq, dimension, pairs, q):
    n, k = dimension, pairs
    beta = iv.mpf((k+1)*n)/(4*k*radius_sq)
    def theta(x):
        geometric = lambda a: 1+2*iv.exp(-a)/(1-iv.exp(-3*a))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    kernel = theta(2*beta)**k*theta(iv.mpf(k)*beta/2)
    coordinate_tail = theta(beta*q*q/(2*k))**((k-1)*n)-1
    x = beta*q*q/4
    denominator = 1-2**k*iv.exp(-3*x)
    tail = coordinate_tail
    if denominator.a > 0:
        delta = 2**k*iv.exp(-x)/denominator
        range_tail = (1+delta)**n-1
        if range_tail.b < tail.b:
            tail = range_tail
    return iv.exp(2*k*beta*radius_sq)*kernel**n*tail


def balanced_rows(support, dimension):
    for plus in combinations(support[1:], 1):
        positive = {support[0], *plus}
        yield tuple(1 if i in positive else -1 if i in support else 0
                    for i in range(dimension))


def line_words(a, b, q):
    return [tuple((x+t*y) % q for x, y in zip(a, b)) for t in range(q)]+[
        tuple(y % q for y in b)]


def short_shape_checks():
    q, checked = 17, 0
    for dimension in range(4, 10):
        first = (1, 1, -1, -1)+(0,)*(dimension-4)
        for support in combinations(range(dimension), 4):
            for second in balanced_rows(support, dimension):
                if second == first or any(not x and not y for x, y in zip(first, second)):
                    continue
                words = line_words(first, second, q)
                if any(all(x == 0 for x in word) for word in words):
                    continue
                minimum = min(sum(x != 0 for x in word) for word in words)
                if minimum < 3:
                    continue
                inner = sum(x*y for x, y in zip(first, second))
                assert abs(inner) <= 2
                if dimension == 4:
                    raise AssertionError('Two norm-four words would give a weight-two word.')
                if dimension in (5, 7):
                    assert abs(inner) == 1
                if dimension == 6:
                    assert inner in (-2, 0, 2)
                if dimension == 8:
                    assert inner == 0
                assert dimension <= 8
                if dimension >= 6:
                    assert minimum >= 4
                if dimension == 5:
                    assert minimum == 3
                    assert sum(sum(x != 0 for x in word) == 3 for word in words) == 1
                if dimension == 7:
                    assert all(sum(x != 0 for x in word) != 5 for word in words)
                checked += 1
    triangular = orthogonal = 0
    for first in balanced_rows((0, 1, 2, 3), 6):
        for second in balanced_rows((2, 3, 4, 5), 6):
            inner = sum(x*y for x, y in zip(first, second))
            words = line_words(first, second, q)
            assert min(sum(x != 0 for x in word) for word in words) >= 4
            for word in words:
                if sum(x != 0 for x in word) != 4:
                    continue
                pivot = next(x for x in word if x)
                normalized = tuple(x*pow(pivot, -1, q) % q for x in word)
                lifted = tuple(x if x <= q//2 else x-q for x in normalized)
                assert sum(lifted) == 0 and sum(x*x for x in lifted) == 4
            if abs(inner) == 2:
                triangular += 1
            else:
                assert inner == 0
                orthogonal += 1
    assert (triangular, orthogonal) == (5, 4)
    print(f'Passed {checked} full-support short-plane shape checks; fixed pair splits 5+4.')


def integer_energy_checks():
    iv.dps = 80
    checked = 0
    for dimension, radius in ((2, 1), (2, 2), (2, 3), (4, 1), (4, 2)):
        points = [x for x in product(range(-radius, radius+1), repeat=dimension)
                  if sum(v*v for v in x) <= radius*radius]
        pairs = Counter(tuple(a+b for a, b in zip(x, y)) for x in points for y in points)
        exact_real = sum(count**3 for count in pairs.values())
        assert exact_real <= pair_sum_ball_bound(iv.mpf(radius*radius), dimension)
        for q in (5, 7, 17):
            modular = Counter()
            for value, count in pairs.items():
                modular[tuple(x % q for x in value)] += count
            exact_modular = sum(count**3 for count in modular.values())
            beta = iv.mpf(dimension)/(3*radius**2)
            def theta(x):
                geometric = lambda a: 1+2*iv.exp(-a)/(1-iv.exp(-3*a))
                return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
            kernel = theta(2*beta)**3*theta(iv.mpf(3)*beta/2)
            alias = (iv.exp(6*beta*radius**2)*kernel**dimension
                     *(theta(beta*q*q/6)**(2*dimension)-1))
            # At extremely small tails subtraction can straddle zero; compare to
            # the nonnegative exact integer through the interval upper endpoint.
            assert exact_modular >= exact_real
            assert exact_modular-exact_real <= alias.b
            checked += 1
    print(f'Passed {checked} exact integer pair-sum counts against volume and alias bounds.')


if __name__ == '__main__':
    short_shape_checks()
    integer_energy_checks()
