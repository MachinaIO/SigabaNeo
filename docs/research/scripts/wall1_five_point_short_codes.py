"""Exhaustive exact norm-four pair classification on five positions."""
from itertools import combinations
from wall1_short_relation_shapes import balanced_rows


def rref(a,b,q):
    rows = [list(a),list(b)]
    pivot = 0
    for j in range(5):
        hit = next((i for i in range(pivot,2) if rows[i][j] % q), None)
        if hit is None:
            continue
        rows[pivot], rows[hit] = rows[hit], rows[pivot]
        inverse = pow(rows[pivot][j] % q,-1,q)
        rows[pivot] = [x*inverse % q for x in rows[pivot]]
        for i in range(2):
            if i != pivot:
                scalar = rows[i][j]
                rows[i] = [(x-scalar*y)%q for x,y in zip(rows[i],rows[pivot])]
        pivot += 1
        if pivot == 2:
            break
    assert pivot == 2
    return tuple(map(tuple,rows))


def exact_counts():
    rows = [row for support in combinations(range(5),4)
            for row in balanced_rows(support,5)]
    assert len(rows) == 15
    for q in (7,17,3329):
        codes = set()
        for a,b in combinations(rows,2):
            # All possible coordinate cancellations are at 0,+1,-1,infinity.
            # Every other direction has the full support union.
            words = [b]+[tuple((x+t*y)%q for x,y in zip(a,b)) for t in (0,1,q-1)]
            supports = [tuple(i for i,x in enumerate(w) if x) for w in words]
            if (min(map(len,supports)) >= 3 and (0,1,2) in supports
                    and (0,1,3,4) in supports):
                codes.add(rref(a,b,q))
                assert abs(sum(x*y for x,y in zip(a,b))) == 1
        assert len(codes) == 6
        print(f'q={q}: exactly six eligible codes among all 105 short-row pairs.')


if __name__ == '__main__':
    exact_counts()
