"""Exact short-line counts used by the five-circuit ten-position split."""
from collections import Counter
from math import comb
from wall1_rare_second_line import norm_rows


def checks():
    rows=list(norm_rows(10,8,minimum_support=5))
    assert len(set(rows))==len(rows)
    counts=Counter(sum(x!=0 for x in row) for row in rows)
    assert counts=={5:20*comb(10,5),8:35*comb(10,8)}
    for row in rows:
        assert sum(row)==0 and sum(x*x for x in row)==8
        assert next(x for x in row if x)>0
    assert len(rows)==6615
    assert comb(len(rows),2)==21875805
    print('Passed6615 exact balanced-line checks; unordered pair cover21875805.')


if __name__=='__main__':checks()
