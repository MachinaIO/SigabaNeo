"""Exclude reduced norm-eight pairs for a four-circuit on ten positions."""
from collections import defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows


def checks():
    groups = defaultdict(set)
    for row in norm_rows(10, 8):
        if not all(row[4:]):
            continue
        assert all(abs(x) <= 1 for x in row)
        assert sum(bool(x) for x in row[:4]) == 2
        row = tuple(row[4]*x for x in row)
        groups[row[4:]].add(row)
    checked = 0
    for rows in groups.values():
        for a, b in combinations(sorted(rows), 2):
            if not all(b[i]-a[i] for i in range(4)):
                continue
            dot = sum(x*y for x,y in zip(a,b))
            assert dot == 6
            assert 2*abs(dot) > 8
            checked += 1
    assert checked == 165
    print(f'Excluded {checked} eligible norm-eight pairs: none is Gauss reduced.')


if __name__ == '__main__':
    checks()
