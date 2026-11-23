"""Exact girth-four short-code strata over a determinant-23 anchor."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant

COUNTS={56:18,60:26,66:25,68:24,74:23,76:11,80:7,84:14,86:42,88:41,92:9}


def exact_counts():
    a=(1,1,-1,-1,0,0,0,0,0,0)
    b=(1,0,0,0,1,1,-1,-1,-1,0)
    raw,valid=Counter(),Counter()
    for v in norm_rows(10,4):
        if not v[-1]:
            continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        gram=92-6*x*x+2*x*y-4*y*y
        raw[gram]+=1
        columns=list(zip(a,b,v))
        minors={indices:determinant(*(columns[i] for i in indices))
                for indices in combinations(range(10),3)}
        assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
        if all(any(minors[indices] for indices in combinations(complement,3))
               for complement in combinations(range(10),7)):
            valid[gram]+=1
    assert sum(raw.values())==252
    assert raw=={38:1,40:3,56:18,60:26,66:25,68:24,74:23,76:11,80:9,84:18,86:44,88:41,92:9}
    assert valid==COUNTS
    print('Passed 252 short lines and all 120 complementary supports per line.')
    print('Girth-four Gram strata:',COUNTS)


if __name__=='__main__':
    exact_counts()
