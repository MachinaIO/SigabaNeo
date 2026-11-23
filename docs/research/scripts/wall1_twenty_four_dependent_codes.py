"""Both affine sign types of a determinant24 one-point extension."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant

UPPER_COUNTS={54:12,56:16,60:8,68:16,72:16,74:20,80:14,86:26,90:18,92:20,96:10}


def exact_counts():
    a=(1,1,-1,-1,0,0,0,0,0)
    representatives=((1,-1,0,0,1,1,-1,-1,0),(1,0,1,0,1,-1,-1,-1,0))
    expected=({54:10,56:16,60:8,68:8,72:16,74:20,80:8,86:26,90:16,92:20,96:8},
              {54:12,56:14,60:6,68:16,72:10,74:18,80:14,86:24,90:18,92:14,96:10})
    results=[]
    for b,target in zip(representatives,expected):
        total=0
        valid=Counter()
        for v in norm_rows(9,4):
            if not v[-1]:continue
            total+=1
            x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
            gram=96-6*x*x-4*y*y
            columns=list(zip(a,b,v))
            minors={indices:determinant(*(columns[i] for i in indices))
                    for indices in combinations(range(9),3)}
            assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
            if all(any(minors[indices] for indices in combinations(complement,3))
                   for complement in combinations(range(9),6)):
                valid[gram]+=1
        assert total==168 and valid==target
        results.append(valid)
    assert {d:max(c[d] for c in results) for d in UPPER_COUNTS}==UPPER_COUNTS
    print('Passed 336 short lines, both affine sign types, and 84 complements per line.')


if __name__=='__main__':
    exact_counts()
