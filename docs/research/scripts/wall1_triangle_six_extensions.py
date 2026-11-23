"""Norm-six third rows with three to five new positions, excluding new norm-four planes."""
from collections import Counter
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows
from itertools import combinations
from wall1_shared_dependent_codes import determinant

UPPER_COUNTS={3:{56:72,60:36,68:72,72:20},4:{56:18,60:72,68:60,72:18},5:{68:60}}


def exact_counts():
    upper={}
    for t in (3,4,5):
        size=6+t
        fours=[v for v in norm_rows(size,4) if all(v[6:])]
        sixes=[v for v in norm_rows(size,6,minimum_support=4) if all(v[6:]) and any(v[:6])]
        results=[]
        for a in balanced_rows((0,1,2,3),size):
            for b in balanced_rows((2,3,4,5),size):
                dot=sum(x*y for x,y in zip(a,b))
                if abs(dot)!=2:continue
                def projection_numerator(w):
                    x,y=sum(z*u for z,u in zip(w,a)),sum(z*u for z,u in zip(w,b))
                    return 12*sum(z*z for z in w)-4*x*x+2*dot*x*y-4*y*y
                counts=Counter()
                for v in sixes:
                    assert all(abs(x)<=1 for x in v)
                    has_four=False
                    for w in fours:
                        scalar=w[6]*v[6]
                        if any(w[i]!=scalar*v[i] for i in range(6,size)):continue
                        difference=tuple(x-scalar*y for x,y in zip(w,v))
                        if projection_numerator(difference)==0:
                            has_four=True
                            break
                    if has_four:continue
                    columns=list(zip(a,b,v))
                    assert any(abs(determinant(*(columns[i] for i in indices)))==1
                               for indices in combinations(range(size),3))
                    counts[projection_numerator(v)]+=1
                results.append(counts)
        assert len(results)==5
        upper[t]={d:max(c[d] for c in results) for d in sorted(set().union(*results))}
        assert upper[t]==UPPER_COUNTS[t]
        print(t,upper[t], 'per-pattern', [dict(sorted(c.items())) for c in results])
    return upper


if __name__=='__main__':
    exact_counts()
