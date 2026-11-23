"""Girth filtering for both balanced determinant-twenty anchor types."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant


UPPER_COUNTS={44:12,50:24,56:32,60:8,64:12,66:20,74:36,76:25,80:12}


def exact_counts():
    a=(1,1,-1,-1,0,0,0,0,0)
    representatives=((1,1,0,0,1,-1,-1,-1,0),(1,0,-1,0,1,1,-1,-1,0))
    expected=({44:9,50:24,56:32,60:2,64:12,66:12,74:36,76:25,80:4},
              {44:12,50:20,56:24,60:8,64:12,66:20,74:32,76:16,80:12})
    results=[]
    for b,target in zip(representatives,expected):
        count=0
        valid=Counter()
        for v in norm_rows(9,4):
            if not v[-1]:
                continue
            count+=1
            x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
            gram=80-6*x*x+4*x*y-4*y*y
            columns=list(zip(a,b,v))
            minors={indices:determinant(*(columns[i] for i in indices))
                    for indices in combinations(range(9),3)}
            assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
            if all(any(minors[indices] for indices in combinations(complement,3))
                   for complement in combinations(range(9),6)):
                valid[gram]+=1
        assert count==168 and valid==target
        results.append(valid)
    assert {d:max(c[d] for c in results) for d in UPPER_COUNTS}==UPPER_COUNTS
    print('Passed both balanced anchor types, 336 short lines and 84 complements per line.')
    print('Uniform Gram-stratum witness upper counts:',UPPER_COUNTS)


if __name__=='__main__':
    exact_counts()
