"""One-point norm-four extensions of the eleven-position determinant31 anchor."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant


UPPER_COUNTS={84:36,86:18,88:30,92:34,96:51,104:48,108:15,110:15,114:30,116:90,120:103,124:13}

def exact_counts():
    a=(1,1,-1,-1)+(0,)*8
    b=(1,0,0,0,1,1,1,-1,-1,-1,-1,0)
    assert sum(a)==sum(b)==0
    valid=Counter()
    total=0
    for v in norm_rows(12,4):
        if not v[-1]:continue
        total+=1
        x=sum(i*j for i,j in zip(a,v))
        y=sum(i*j for i,j in zip(b,v))
        gram=124-8*x*x+2*x*y-4*y*y
        columns=list(zip(a,b,v))
        minors={indices:determinant(*(columns[i] for i in indices))
                for indices in combinations(range(12),3)}
        assert 1 in map(abs,minors.values())
        assert max(map(abs,minors.values()))<7
        if all(any(minors[indices] for indices in combinations(complement,3))
               for complement in combinations(range(12),9)):
            valid[gram]+=1
    assert total==495
    assert dict(valid)==UPPER_COUNTS
    witnesses=0
    for old in norm_rows(4,4,minimum_support=4):
        first=old+(0,)*7
        for second in norm_rows(11,8):
            if not all(second[4:]):continue
            shared=[i for i in range(4) if second[i]]
            assert len(shared)==1
            j=shared[0]
            u=tuple(first[j]*x for x in first)
            w=tuple(second[j]*x for x in second)
            order=([j]+[i for i in range(4) if i!=j and u[i]>0]
                   +[i for i in range(4) if u[i]<0]
                   +[i for i in range(4,11) if w[i]>0]
                   +[i for i in range(4,11) if w[i]<0])
            assert tuple(u[i] for i in order)==a[:11]
            assert tuple(w[i] for i in order)==b[:11]
            witnesses+=1
    assert witnesses==420
    print('Eligible counts:',dict(sorted(valid.items())))
    print('Checked495 extension lines,220 complements per line, and420 balance-preserving anchor maps.')
    return dict(sorted(valid.items()))


if __name__=='__main__':exact_counts()
