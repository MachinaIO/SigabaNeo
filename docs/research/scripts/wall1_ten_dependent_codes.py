"""Both affine sign types of one-point determinant28 anchor extensions."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant

UPPER_COUNTS={68:12,76:18,80:104,84:12,96:66,104:88,108:68,112:18}


def exact_counts():
    a=(1,1,-1,-1,0,0,0,0,0,0,0)
    representatives=((1,1,0,0,1,1,-1,-1,-1,-1,0),
                     (1,0,-1,0,1,1,1,-1,-1,-1,0))
    results=[]
    for b in representatives:
        assert sum(a)==sum(b)==0
        assert sum(x*y for x,y in zip(a,b))==2
        total=0
        valid=Counter()
        for v in norm_rows(11,4):
            if not v[-1]:continue
            total+=1
            x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
            gram=112-8*x*x+4*x*y-4*y*y
            columns=list(zip(a,b,v))
            minors={indices:determinant(*(columns[i] for i in indices))
                    for indices in combinations(range(11),3)}
            assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
            if all(any(minors[indices] for indices in combinations(complement,3))
                   for complement in combinations(range(11),8)):
                valid[gram]+=1
        assert total==360
        results.append(valid)
        print(dict(sorted(valid.items())))
    upper={d:max(c[d] for c in results) for d in sorted(set().union(*results))}
    assert upper==UPPER_COUNTS
    print('UPPER_COUNTS',upper)
    print('Passed720 short lines, two affine sign types, and165 complements per line.')
    return upper


if __name__=='__main__':
    exact_counts()
