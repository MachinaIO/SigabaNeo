"""Exact grouped inclusion-exclusion for overlapping actual-winner events.

q=3,m=d=3, w=(-1,-1,0,-1,0,0). Containment fixes the first column
of A to (1,1,0), with probability 1/27. All integer vectors of norm^2<=3
have entries in {-1,0,1}; direct sorted enumeration therefore completely
checks the actual shortest vector with lexicographic tie breaking.

Twenty forbidden membership events are processed without truncation.
Canonical full graph-constraint spans group compatible overlaps, while
inconsistent spans are discarded only after the generic evaluator returns
zero. Coefficients remain signed integers. This is a finite test, not a
production geometric or selected-history estimate.
"""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from time import perf_counter
from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace

Q=3
W=(-1,-1,0,-1,0,0)


def label(matrix,z):
    return tuple((z[i]-sum(matrix[i][j]*z[3+j] for j in range(3)))%Q
                 for i in range(3))


def main():
    start=perf_counter()
    model=FixedQuotientGraphSpace(Q,3,3,0,(W,),(W,))
    axes=tuple(tuple(int(i==j) for i in range(6)) for j in range(6))
    a=(1,1,0)
    bad={(0,0,0),a,tuple(-x%Q for x in a)}
    for i in range(3):
        for sign in (1,-1):
            bad.add(tuple(sign%Q if j==i else 0 for j in range(3)))
    assert len(bad)==9
    forbidden=[]
    for col in (1,2):
        for value in sorted(bad):
            forbidden.append(value+tuple(int(j==col) for j in range(3)))
    for sign in (1,-1):
        forbidden.append((0,0,0,0,1,(-sign)%Q))
    assert len(forbidden)==20

    @lru_cache(maxsize=None)
    def joint(full,quotient=()):
        return model.joint_probability(full,quotient)

    base=row_basis((W,),Q)
    assert joint(base)==F(1,27)
    states={base:1}
    peak=1
    discarded=0
    for event in forbidden:
        updated=defaultdict(int)
        for constraints,coefficient in states.items():
            updated[constraints]+=coefficient
            extended=row_basis(constraints+(event,),Q)
            if joint(extended)==0:
                discarded+=1
            else:
                updated[extended]-=coefficient
        states={basis:c for basis,c in updated.items() if c}
        peak=max(peak,len(states))
    # One column-2 and one column-3 event can hold simultaneously.
    overlap=row_basis(base+(forbidden[0],forbidden[9]),Q)
    assert joint(overlap)==F(1,3**9)>0

    def collision(constraints,z,zp,t):
        difference=tuple((b-t*a)%Q for a,b in zip(z,zp))
        return (joint(constraints,row_basis((difference,),Q))
                -joint(constraints,row_basis((difference,z),Q)))

    def terms(constraints):
        mass=joint(constraints)
        n=sum((mass-joint(constraints,row_basis((z,),Q)) for z in axes),F(0))
        j=sum((collision(constraints,z,zp,1) for z,zp in product(axes,repeat=2)),F(0))
        c=sum((collision(constraints,z,zp,t) for z,zp,t in product(axes,axes,(1,2))),F(0))
        return mass,n,j,c

    totals=[F(0)]*4
    for constraints,coefficient in states.items():
        totals=[v+coefficient*t for v,t in zip(totals,terms(constraints))]

    short=sorted((sum(x*x for x in z),z) for z in product((-1,0,1),repeat=6)
                 if 0<sum(x*x for x in z)<=3)
    direct=[0]*4
    columns=list(product(range(Q),repeat=3))
    for b,c in product(columns,repeat=2):
        matrix=tuple((a[i],b[i],c[i]) for i in range(3))
        winner=next(z for _,z in short if not any(label(matrix,z)))
        selected=winner==W
        absent=(b not in bad and c not in bad
                and b!=c and b!=tuple(-x%Q for x in c))
        assert selected==absent
        if not selected:
            continue
        labels=[label(matrix,z) for z in axes]
        direct[0]+=1
        direct[1]+=sum(any(v) for v in labels)
        direct[2]+=sum(any(v) and v==w for v,w in product(labels,repeat=2))
        direct[3]+=sum(any(v) and w==tuple(t*x%Q for x in v)
                       for v,w,t in product(labels,labels,(1,2)))
    assert direct[0]==288
    assert tuple(totals)==tuple(F(v,3**9) for v in direct)
    assert totals[0]==F(32,2187)
    print('Forbidden overlapping events:',len(forbidden),'complete shortest vectors:',len(short))
    print('Grouped IE peak states:',peak,'final states:',len(states),
          'by full constraint rank:',dict(sorted(Counter(map(len,states)).items())))
    print('Inconsistent transition branches discarded:',discarded)
    print('Compatible two-event intersection probability:',joint(overlap))
    print('Direct selected counts (mass,N,J,C):',tuple(direct),'out of729 first-column-conditioned maps.')
    print('Generic evaluator unconditional selected terms:',tuple(totals))
    print('Evaluator cache:',joint.cache_info())
    print('Elapsed seconds:',round(perf_counter()-start,3))
    print('Full grouped inclusion-exclusion and actual-winner incidence checks passed.')


if __name__=='__main__':
    main()
