"""Exact quotient-basis multiplicity checks after arbitrary contractions."""
from itertools import combinations, product
from wall1_centered_affine_cancellation import rank


def finite_checks():
    checked = 0
    for q, dimension in ((3,2),(2,3)):
        rows = [(1,*p) for p in product(range(q), repeat=dimension)]
        ranks = {mask:rank([v for i,v in enumerate(rows) if mask>>i&1],q)
                 for mask in range(1<<len(rows))}
        for support,r in ranks.items():
            indices = [i for i in range(len(rows)) if support>>i&1]
            if any(ranks[support^(1<<i)] != r for i in indices):
                continue
            anchor = support
            while True:
                outside = [i for i in indices if not anchor>>i&1]
                e = r-ranks[anchor]
                bases = sum(ranks[anchor|sum(1<<i for i in subset)] == r
                            for subset in combinations(outside,e))
                assert bases >= e+1
                assert all(ranks[support^(1<<i)]-ranks[anchor] == e for i in outside)
                checked += 1
                if anchor == 0:
                    break
                anchor = (anchor-1)&support
    print(f'Passed {checked} exact contracted no-coloop basis-count checks.')


if __name__ == '__main__':
    finite_checks()
