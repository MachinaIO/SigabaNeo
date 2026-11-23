"""Exact regressions for basis multiplicity and the unique-four-circuit theta bound."""
from fractions import Fraction as F
from itertools import product
from wall1_centered_affine_cancellation import rank


def basis_count_checks():
    q = 3
    ys = list(product(range(q), repeat=2))
    ranks = {mask: rank([(1, *p) for i, p in enumerate(ys) if mask >> i & 1], q)
             for mask in range(1 << len(ys))}
    checked = 0
    for support, r in ranks.items():
        if support.bit_count() < 3:
            continue
        if any(ranks[support ^ (1 << i)] != r
               for i in range(len(ys)) if support >> i & 1):
            continue
        anchor = support
        while True:
            k = r-ranks[anchor]
            remaining = support ^ anchor
            basis_count = 0
            chosen = remaining
            while True:
                if chosen.bit_count() == k and ranks[anchor | chosen] == r:
                    basis_count += 1
                if not chosen:
                    break
                chosen = (chosen-1) & remaining
            assert basis_count >= k+1
            checked += 1
            if not anchor:
                break
            anchor = (anchor-1) & support
    print(f'Passed {checked} no-coloop contraction basis-count checks.')


def code_lines(first, second, q):
    return [tuple((a+t*b) % q for a, b in zip(first, second)) for t in range(q)]+[second]


def four_circuit_cases():
    checked = unique = paired = 0
    for q in (5, 7):
        for u, v in product(range(1, q), repeat=2):
            first = (1, u, v, (-1-u-v) % q, 0, 0)
            if first[3] == 0:
                continue
            for a, b, c in product(range(q), repeat=3):
                second = (a, b, c, 0, 1, (-1-a-b-c) % q)
                if not second[5]:
                    continue
                lines = code_lines(first, second, q)
                weights = [sum(value != 0 for value in word) for word in lines]
                if min(weights) < 4:
                    continue
                fours = [word for word, weight in zip(lines, weights) if weight == 4]
                assert fours
                if len(fours) == 1:
                    assert fours[0] == first
                    unique += 1
                else:
                    pairs = 0
                    for left in fours:
                        for right in fours:
                            if left == right:
                                continue
                            assert all(a or b for a, b in zip(left, right))
                            pairs += 1
                    assert pairs >= 2
                    paired += 1
                checked += 1
    print(f'Passed {checked} circuit-code classifications ({unique} unique, {paired} paired).')


def reduced_gram_checks():
    checked = 0
    for first_sq in range(4, 42, 2):
        for second_sq in range(first_sq, 42, 2):
            if first_sq == second_sq == 4:
                continue  # Two independent weight-four directions are forbidden.
            for inner in range(-first_sq//2, first_sq//2+1):
                height_sq = F(first_sq*second_sq-inner**2, first_sq)
                if first_sq == 4:
                    assert height_sq >= 5
                else:
                    assert first_sq >= 6 and height_sq >= F(9, 2)
                checked += 1
    print(f'Passed {checked} reduced integer Gram bounds.')


def rational_theta_checks():
    q, cutoff = 17, 2
    assert cutoff**3 < q and 6*cutoff**2 < q**2
    first = (1, 1, -1, -1, 0, 0)
    checked = 0
    for u, v, w in ((1, 2, 3), (1, 3, 2), (2, 3, 1)):
        second = (u, v, w, 0, 1, -1-u-v-w)
        lines = code_lines(tuple(x % q for x in first), tuple(x % q for x in second), q)
        weights = [sum(value != 0 for value in word) for word in lines]
        assert min(weights) == 4 and weights.count(4) == 1
        norms = []
        for a, b in product(range(q), repeat=2):
            vector = [((a*x+b*y+q//2) % q)-q//2 for x, y in zip(first, second)]
            norms.append(sum(x*x for x in vector))
        for base in (F(1, 2), F(4, 5)):
            def theta(power):
                return 1+2*base**power/(1-base**(3*power))
            actual = sum((base**(8*norm) for norm in norms), F(0))
            upper = (theta(32)*theta(40)+base**(4*cutoff**2)
                     *(theta(16)*theta(12)+q*q*base**(q*q)))
            assert actual <= upper
            checked += 1
    print(f'Passed {checked} exact finite-code Gaussian/theta inequalities.')


if __name__ == '__main__':
    basis_count_checks()
    four_circuit_cases()
    reduced_gram_checks()
    rational_theta_checks()
