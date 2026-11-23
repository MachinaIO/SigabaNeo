"""Norm-eight witnesses for eleven-position seven-circuit planes."""
from collections import Counter
from math import comb,gcd
from wall1_rare_second_line import norm_rows


def checks():
    rows=list(norm_rows(11,8,minimum_support=7))
    assert len(rows)==len(set(rows))==35*comb(11,8)==5775
    a=(1,)*4+(-1,)*4+(0,)*3
    eligible=0
    for b in rows:
        assert all(abs(x)<=1 for x in b)
        assert sum(b)==0 and sum(x*x for x in b)==8
        if not all(x or y for x,y in zip(a,b)):continue
        dot=sum(x*y for x,y in zip(a,b))
        if abs(dot)>4:continue
        groups=Counter()
        for x,y in zip(a,b):
            d=gcd(x,y)
            direction=(x//d,y//d)
            if direction[0]<0 or (direction[0]==0 and direction[1]<0):
                direction=tuple(-v for v in direction)
            groups[direction]+=1
        if max(groups.values())!=4:continue
        assert abs(dot)==3
        eligible+=1
    assert eligible==624
    print('Checked5775 short lines; pair-witness cover',comb(len(rows),2))
    print('Eligible fixed-first-row reduced pairs of exact girth seven:',eligible)


if __name__=='__main__':checks()
