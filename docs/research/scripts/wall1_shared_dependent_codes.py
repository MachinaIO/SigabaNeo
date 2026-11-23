"""Exact girth-four short-line strata for one dependent shared-anchor point."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows


def determinant(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            -a[1]*(b[0]*c[2]-b[2]*c[0])
            +a[2]*(b[0]*c[1]-b[1]*c[0]))


def exact_counts():
    a=(1,1,-1,-1,0,0,0,0)
    b=(1,0,0,0,1,-1,-1,0)
    raw,valid=Counter(),Counter()
    for v in norm_rows(8,4):
        if not v[-1]:
            continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        gram=60-4*x*x+2*x*y-4*y*y
        raw[gram]+=1
        columns=list(zip(a,b,v))
        minors={indices:determinant(*(columns[i] for i in indices))
                for indices in combinations(range(8),3)}
        assert 1 in map(abs,minors.values())
        assert max(map(abs,minors.values()))<7
        # A codeword on <=3 positions exists iff deleting some three
        # columns leaves column rank less than three. All minors are <7,
        # so the test is identical over Q and every prime field q>=7.
        good=all(any(minors[indices] for indices in combinations(complement,3))
                 for complement in combinations(range(8),5))
        if good:
            valid[gram]+=1
    assert sum(raw.values())==105
    assert raw=={24:2,26:6,36:24,44:28,50:4,54:8,56:28,60:5}
    assert valid=={36:24,44:28,56:24,60:5}
    print('Exact shared-dependent Gram strata:',dict(sorted(valid.items())))
    print('Checked 105 lines, unit minors, and all 56 complementary supports per line.')
    return valid


if __name__=='__main__':
    exact_counts()
