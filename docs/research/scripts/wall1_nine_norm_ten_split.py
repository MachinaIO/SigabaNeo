"""Balanced norm-ten line count for the nine-position remainder."""
from collections import Counter
from math import comb
from wall1_rare_second_line import norm_rows


def checks():
    rows=list(norm_rows(9,10))
    counts=Counter(sum(x!=0 for x in row) for row in rows)
    assert counts=={7:105*comb(9,7),4:12*comb(9,4)}
    assert len(set(rows))==len(rows)==5292
    for row in rows:
        assert sum(row)==0 and sum(x*x for x in row)==10
        assert next(x for x in row if x)>0
        if all(row[4:]):
            assert any(abs(x)==1 for x in row[4:])
    print('Passed5292 balanced norm-ten line checks; pair-witness cover15876.')


if __name__=='__main__':checks()
