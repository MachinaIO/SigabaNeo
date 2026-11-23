"""Several equal pair sums: exact regression and actual-parameter subfamily bounds."""
import contextlib
from collections import Counter
from itertools import product
from math import comb, factorial
from pathlib import Path
import io
import runpy
from fractions import Fraction as F
from mpmath import iv
from wall1_short_relation_shapes import equal_pair_sum_ball_bound, equal_pair_sum_alias_bound
from wall1_factorial_cumulants import difference_weights
from wall1_affine_circuit_components import exponential


def finite_checks():
    iv.dps = 80
    checked = 0
    for n, radius in ((2, 1), (2, 2), (2, 3), (4, 1), (4, 2)):
        points = [v for v in product(range(-radius, radius+1), repeat=n)
                  if sum(x*x for x in v) <= radius**2]
        pairs = Counter(tuple(a+b for a, b in zip(x, y)) for x in points for y in points)
        for k in range(2, 7):
            real = sum(count**k for count in pairs.values())
            main = equal_pair_sum_ball_bound(iv.mpf(radius**2), n, k)
            assert real <= main
            for q in (5, 7, 17):
                modular = Counter()
                for value, count in pairs.items():
                    modular[tuple(x % q for x in value)] += count
                exact = sum(count**k for count in modular.values())
                alias = equal_pair_sum_alias_bound(iv.mpf(radius**2), n, k, q)
                assert 0 <= exact-real <= alias.b
                checked += 1
    ranges = 0
    for k in range(2, 7):
        for width in range(1, 5):
            # Count quotient representatives by their range, without Gaussian arithmetic.
            exact = sum(min(v) == 0 and max(v) == width
                        for v in product(range(width+1), repeat=k))
            assert exact == (width+1)**k-2*width**k+(width-1)**k
            assert exact <= 2**(k*width)
            for v in product(range(width+1), repeat=k):
                if min(v) != 0 or max(v) != width:
                    continue
                variance = F(sum(x*x for x in v))-F(sum(v)**2, k)
                assert variance >= F(width**2, 2)
            ranges += 1
    print(f'Passed {checked} integer pair-sum power bounds and {ranges} exact layer-range checks.')


def draw14_bounds():
    with contextlib.redirect_stdout(io.StringIO()):
        s = runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    I, mu, q, n, m, radius = [s[key] for key in ('I', 'mu', 'q', 'N', 'm', 'radius')]
    order = s['order']
    weights = difference_weights(12)
    majorants = [sum((I(abs(v.numerator))/v.denominator*mu**degree
                     for degree, v in enumerate(poly)), I(0)) for poly in weights]
    def transfer(activities):
        series = [I(0), I(0)]+[activities.get(j, I(0))/factorial(j)
                              for j in range(2, order+1)]
        expanded = exponential(series, start=1)
        return s['normalizer']*sum((majorants[j]*expanded[j]
                                   for j in range(2, order+1)), I(0))
    for k in (4, 5, 6, 7, 12):
        main = equal_pair_sum_ball_bound(radius**2, n, k)
        alias = equal_pair_sum_alias_bound(radius**2, n, k, q)
        anchor = (main+alias)/q**(m*(k+1))
        print('Pair count', k, 'alias/main:', alias/main, flush=True)
        for h in sorted({max(14, 2*k), 24}):
            if h > 24:
                continue
            positions = comb(h, 2*k)*factorial(2*k)//(2**k*factorial(k))
            signs = 1+2**(k-1)
            total = I(0)
            for r in range(k+1, h-k+2):
                extensions = r-k-1
                total += (positions*signs*comb(h-2*k, extensions)*anchor*mu**extensions
                          *q**((r-1)*(h-r-k+1))/(extensions+1))
            charge = transfer({h: total})
            if k == 4 and h == 14:
                assert charge < I('3e-42')
            if k == 12 and h == 24:
                assert charge < I('1e-237')
            print('  Connected size', h, 'family-only cumulant transfer log10:',
                  iv.log10(charge), flush=True)
    print('UNBOUNDED: other connected configurations and mixtures with those families.')


if __name__ == '__main__':
    finite_checks()
    draw14_bounds()
