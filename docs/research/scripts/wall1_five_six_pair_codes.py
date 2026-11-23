"""Norm-six pairs on eight positions with a prescribed five-circuit."""
from collections import defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows

COUNTS={2:0,3:36,4:36}


def exact_counts():
    rows=list(norm_rows(8,6,minimum_support=5))
    results=[]
    for q in (7,17,3329):
        codes=defaultdict(set)
        for a,b in combinations(rows,2):
            if not all(x or y for x,y in zip(a,b)):continue
            if any(a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(5,8),2)):continue
            p=next(i for i in range(5,8) if a[i] or b[i])
            first=tuple((b[p]*a[i]-a[p]*b[i])%q for i in range(8))
            if not all(first[:5]):continue
            dot=sum(x*y for x,y in zip(a,b))
            assert abs(dot)==2
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(8),2))
            f=tuple(x*pow(first[0],-1,q)%q for x in first)
            for overlap in (2,3,4):
                k=overlap
                second=tuple((b[k]*a[i]-a[k]*b[i])%q for i in range(8))
                target=tuple(range(overlap))+(5,6,7)
                if tuple(i for i,x in enumerate(second) if x)!=target:continue
                v=tuple((second[i]-second[0]*f[i])*pow(second[5],-1,q)%q for i in range(8))
                codes[overlap].add((f,v))
        counts={k:len(v) for k,v in codes.items()}
        assert {k:counts.get(k,0) for k in COUNTS}==COUNTS
        results.append(counts)
        print(q,counts)
    assert results[0]==results[1]==results[2]
    return results[0]


if __name__=='__main__':
    exact_counts()
