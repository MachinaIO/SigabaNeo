"""Girth-six one-point norm-six extensions of the determinant32 anchor."""
from collections import Counter
from itertools import combinations
from wall1_six_ten_projection import REPRESENTATIVES
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant


UPPER_COUNTS={120:162,138:80,144:216,168:132,170:90,176:176,184:212,186:354,192:112}

def exact_counts():
    results=[]
    for first,second in REPRESENTATIVES:
        a=first+(0,);b=second+(0,)
        counts=Counter();total=0
        for v in norm_rows(11,6,minimum_support=6):
            if not v[-1]:continue
            total+=1
            x=sum(i*j for i,j in zip(a,v));y=sum(i*j for i,j in zip(b,v))
            gram=192-6*x*x+4*x*y-6*y*y
            columns=list(zip(a,b,v))
            minors={indices:determinant(*(columns[i] for i in indices))
                    for indices in combinations(range(11),3)}
            assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
            if all(any(minors[indices] for indices in combinations(complement,3))
                   for complement in combinations(range(11),6)):
                counts[gram]+=1
        assert total==2520
        results.append(dict(sorted(counts.items())))
    assert {d:max(c.get(d,0) for c in results) for d in UPPER_COUNTS}==UPPER_COUNTS
    print('Eligible extension counts:',results)
    return results


if __name__=='__main__':exact_counts()
