"""Girth-filtered norm-four rows adding two points to a shared four/four anchor."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant

COUNTS={44:20,50:14,54:13,56:8,60:8}


def exact_counts():
    a=(1,1,-1,-1,0,0,0,0,0)
    b=(1,0,0,0,1,-1,-1,0,0)
    raw,valid=Counter(),Counter()
    for v in norm_rows(9,4):
        if not all(v[7:]):continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        gram=60-4*x*x+2*x*y-4*y*y
        raw[gram]+=1
        columns=list(zip(a,b,v))
        minors={indices:determinant(*(columns[i] for i in indices))
                for indices in combinations(range(9),3)}
        assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
        if all(any(minors[indices] for indices in combinations(complement,3))
               for complement in combinations(range(9),6)):
            valid[gram]+=1
    assert sum(raw.values())==63
    assert raw==valid==COUNTS
    print('raw',dict(sorted(raw.items())))
    print('valid',dict(sorted(valid.items())))
    return valid


if __name__=='__main__':
    exact_counts()
