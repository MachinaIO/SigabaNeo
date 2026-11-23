"""Girth-four reduced norm-six pairs on seven positions have Gram35."""
from wall1_rare_second_line import norm_rows
from collections import Counter

def checks():
    firsts=list(norm_rows(6,6,minimum_support=6))
    seconds=list(norm_rows(7,6))
    checked=0
    for a0 in firsts:
        a=a0+(0,)
        for b in seconds:
            if not b[6]:continue
            dot=sum(x*y for x,y in zip(a,b))
            if abs(dot)>3:continue
            groups=Counter()
            for x,y in zip(a,b):
                sign=x if x else y
                groups[sign*x,sign*y]+=1
            if max(groups.values())>3:continue
            assert abs(dot)==1
            assert 36-dot*dot==35
            checked+=1
    assert checked>0
    print('Passed',checked,'full-support reduced girth-four pair checks.')

if __name__=='__main__':checks()
