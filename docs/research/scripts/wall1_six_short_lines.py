"""Exact classification of pairs of balanced six-support rows."""
from itertools import combinations


def finite_checks():
    tested = eligible = four_eligible = six_eligible = 0
    for size in range(6, 13):
        first = (1,1,1,-1,-1,-1)+((0,)*(size-6))
        for old in combinations(range(6), 12-size):
            support = (*old, *range(6,size))
            assert len(support) == 6
            for plus_tail in combinations(support[1:], 2):
                plus = {support[0], *plus_tail}
                second = tuple(1 if i in plus else -1 if i in support else 0
                               for i in range(size))
                if second == first or second == tuple(-v for v in first):
                    continue
                for q in (7, 17):
                    weights = [6]+[sum((a+k*b) % q != 0 for a,b in zip(first,second))
                                   for k in range(q)]
                    if 3 in weights:
                        assert size <= 7
                    if min(weights) >= 5 and 5 in weights:
                        assert size == 8
                        eligible += 1
                    if min(weights) == 6:
                        assert size >= 8
                        dot = sum(a*b for a,b in zip(first,second))
                        if size == 8:
                            assert dot == 0
                        if size == 10:
                            assert abs(dot) <= 2
                        if size == 11:
                            assert abs(dot) == 1
                        if size == 12:
                            for scalar in range(q):
                                word = tuple((a+scalar*b)%q for a,b in zip(first,second))
                                assert sum(bool(x) for x in word[:6]) == 6
                        six_eligible += 1
                    if min(weights) == 4:
                        has_norm_four = False
                        for k in range(q):
                            word = tuple((a+k*b) % q for a,b in zip(first,second))
                            if sum(x != 0 for x in word) != 4:
                                continue
                            for scale in range(1,q):
                                scaled = tuple((scale*x) % q for x in word)
                                if all(x in (0,1,q-1) for x in scaled):
                                    signed = tuple(-1 if x == q-1 else x for x in scaled)
                                    if sum(signed) == 0:
                                        has_norm_four = True
                        if not has_norm_four:
                            assert size == 7
                            four_eligible += 1
                    tested += 1
    assert eligible > 0
    assert four_eligible > 0
    print(f'Passed {tested} full-code weight classifications; {eligible} eligible cases, all size eight.')
    print(f'Girth four with no norm-four line: {four_eligible} cases, all size seven.')
    print(f'Girth-six pair geometry checked in {six_eligible} cases.')


if __name__ == '__main__':
    finite_checks()
