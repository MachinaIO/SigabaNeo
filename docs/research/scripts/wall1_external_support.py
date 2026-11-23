"""An independent relation direction uses all new positions and an old one."""
from itertools import product
from fractions import Fraction


def finite_checks():
    rows = directions = 0
    for q in (3, 5):
        for c in (3, 4):
            for middle in product(range(1, q), repeat=c-2):
                last = (-1-sum(middle)) % q
                if not last:
                    continue
                first = (1, *middle, last)
                for t in (4, 5):
                    for overlap in range(1, c):
                        # Normalize the first new coordinate to one; solve the
                        # affine sum condition for the last overlapping entry.
                        for free in product(range(1, q), repeat=overlap+t-2):
                            old = (*free[:overlap-1], (-1-sum(free)) % q)
                            if not old[-1]:
                                continue
                            second = (*old, *((0,)*(c-overlap)), 1, *free[overlap-1:])
                            assert len(second) == c+t and sum(second) % q == 0
                            extended = (*first, *((0,)*t))
                            for scale in range(q):
                                word = tuple((b+scale*a) % q for a, b in zip(extended, second))
                                assert all(word[c:])
                                assert any(word[:c])
                                assert sum(bool(x) for x in word) >= t+1 > 4
                                directions += 1
                            rows += 1
    print(f'Passed {rows} coefficient pairs and {directions} independent-direction support checks.')


def reduced_height_checks():
    checked = 0
    for t in range(1, 22):
        external_sq = 2*((t+2)//2)
        for first in range(6, 198, 2):
            for second in range(max(first, external_sq), 198, 2):
                for dot in range(-first//2, first//2+1):
                    height = second-Fraction(dot*dot, first)
                    assert height >= Fraction(3*max(6, external_sq), 4)
                    checked += 1
        if t >= 4:
            for second in range(max(6, external_sq), 198, 2):
                for dot in range(-2, 3):
                    assert second-Fraction(dot*dot, 4) >= max(5, external_sq-1)
                    checked += 1
    print(f'Passed {checked} exact reduced-Gram height checks.')


if __name__ == '__main__':
    finite_checks()
    reduced_height_checks()
