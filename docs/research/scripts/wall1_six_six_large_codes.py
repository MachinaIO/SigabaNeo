"""Exact prescribed-support norm-six pairs on ten and eleven positions."""
from collections import defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows

COUNTS={10:{2:((32,52),(36,48)),3:(),4:((32,52),),5:((36,240),)},
        11:{1:((35,100),),2:(),3:(),4:(),5:((35,100),)}}
EIGHT_COUNTS={1:(),2:(),3:((39,95),(47,255)),4:((47,340),),5:((47,850),)}


def exact_counts():
    results={}
    for size in (10,11):
        for q in (7,17,3329):
            codes=defaultdict(set)
            for first0 in norm_rows(6,6,minimum_support=6):
                first=first0+(0,)*(size-6)
                for second in norm_rows(size,6,minimum_support=6):
                    if not all(second[6:]):continue
                    dot=sum(x*y for x,y in zip(first,second))
                    gram=36-dot*dot
                    assert gram in ((32,36) if size==10 else (35,))
                    assert any(abs(first[i]*second[j]-first[j]*second[i])==1
                               for i,j in combinations(range(size),2))
                    key=(first,tuple((x-second[0]*y)*pow(second[6]%q,-1,q)%q
                                     for x,y in zip(second,first)))
                    for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(6)}:
                        support=tuple(i for i in range(6) if (second[i]+scalar*first[i])%q)
                        for overlap in range(max(1,12-size),6):
                            if support==tuple(range(overlap)):
                                codes[overlap,gram].add(key)
            counts={k:len(v) for k,v in codes.items()}
            assert counts=={(a,d):n for a,entries in COUNTS[size].items() for d,n in entries}
            if size in results:assert counts==results[size]
            results[size]=counts
            print(size,q,dict(sorted(counts.items())))
    return results


def six_eight_counts():
    seconds=[b for b in norm_rows(11,8,minimum_support=6) if all(b[6:])]
    for q in (7,17,3329):
        codes=defaultdict(set)
        for first0 in norm_rows(6,6,minimum_support=6):
            first=first0+(0,)*5
            for second in seconds:
                assert all(abs(x)<=1 for x in second)
                dot=sum(x*y for x,y in zip(first,second))
                gram=48-dot*dot
                assert gram in (39,47)
                assert any(abs(first[i]*second[j]-first[j]*second[i])==1
                           for i,j in combinations(range(11),2))
                key=(first,tuple((x-second[0]*y)*pow(second[6]%q,-1,q)%q
                                 for x,y in zip(second,first)))
                for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(6)}:
                    support=tuple(i for i in range(6) if (second[i]+scalar*first[i])%q)
                    for overlap in range(1,6):
                        if support==tuple(range(overlap)):
                            codes[overlap,gram].add(key)
        assert {k:len(v) for k,v in codes.items()}=={
            (a,d):n for a,entries in EIGHT_COUNTS.items() for d,n in entries}
        print(f'q={q}: exact six/eight determinant39/47 planes and primitive minors passed.')


if __name__=='__main__':
    exact_counts()
    six_eight_counts()
