"""H11, girth six: a prescribed six-support forbids a reduced (8,8) pair."""
from collections import Counter
from itertools import combinations

def check():
    a=(1,1,1,1,-1,-1,-1,-1,0,0,0)
    checked=eligible=0
    for old in combinations(range(8),5):
        support=old+(8,9,10)
        for positive in combinations(support,4):
            b=tuple(1 if i in positive else -1 if i in support else 0 for i in range(11))
            dot=sum(x*y for x,y in zip(a,b))
            # Exclusive groups have size3. A six-support codeword needs
            # a zero-column-direction group of size5 among shared columns.
            # Normalize the b-only columns as well (their signs are irrelevant).
            classes=Counter()
            for x,y in zip(a,b):
                classes[(1,y*x) if x else (0,1)]+=1
            checked+=1
            if 5 not in classes.values():continue
            eligible+=1
            assert abs(dot)==5
            sign=1 if dot>0 else -1
            assert sum((x-sign*y)**2 for x,y in zip(a,b))==6
            assert abs(dot)>4  # violates Gauss reduction
    assert checked==3920 and eligible>0
    print(f'Passed {checked} balanced full-support pairs; {eligible} six-support cases all have norm-six difference.')

if __name__=='__main__':check()
