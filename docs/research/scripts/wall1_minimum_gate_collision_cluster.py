"""A same-coset high-moment cluster surviving the old-minimum gate.

An abstract rank-seven q-ary lattice at q=3329, not a reachable production
history. Its 24 candidates have genuine geometry and a strict height margin.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial


def rank(rows):
    rows=[list(map(F,row)) for row in rows]
    pivot=0
    for col in range(len(rows[0])):
        found=next((i for i in range(pivot,len(rows)) if rows[i][col]),None)
        if found is None:
            continue
        rows[pivot],rows[found]=rows[found],rows[pivot]
        value=rows[pivot][col]
        rows[pivot]=[x/value for x in rows[pivot]]
        for i in range(pivot+1,len(rows)):
            value=rows[i][col]
            rows[i]=[x-value*y for x,y in zip(rows[i],rows[pivot])]
        pivot+=1
        if pivot==len(rows):
            break
    return pivot


def in_m0(v):
    return (v[0]==v[1] and all(x.denominator==1 for x in v)
            and sum(v[2:])%2==0)


def main():
    q=3329
    # M0=Z*(1,1,0^6) orthogonal-sum D6, M=3M0, K=M/q.
    k=(F(1,2),F(1,2),F(1),F(0),F(0),F(0),F(0),F(0))
    original=[]
    for s,t,j in product((-1,1),(-1,1),range(6)):
        original.append((F(s,2),F(s,2))+tuple(F(t if i==j else 0) for i in range(6)))
    candidates=[tuple(3*(x-y/q) for x,y in zip(p,k)) for p in original]
    assert len(set(candidates))==24
    for x in candidates:
        assert in_m0(tuple(q*a/3 for a in x)) # x in K
        assert not in_m0(tuple(a/3 for a in x)) # nonzero class in K/M
    distances=[]
    for i,x in enumerate(candidates):
        for y in candidates[i+1:]:
            difference=tuple(a-b for a,b in zip(x,y))
            assert in_m0(tuple(a/3 for a in difference))
            distances.append(sum(a*a for a in difference))
    assert min(distances)==18
    radius2=max(sum(a*a for a in x) for x in candidates)
    assert radius2==F(27,2)*(1+F(1,q))**2<14
    assert 14+1<18 # a uniform R^2=14, c^2=18, height 1
    assert rank([tuple(a-b for a,b in zip(x,candidates[0])) for x in candidates[1:]])==7
    # Every nonzero M0 vector has norm^2>=2: a nonzero first coordinate
    # contributes 2*a^2; a nonzero D6 vector cannot be a signed unit vector.
    assert in_m0((F(1),F(1))+(F(0),)*6)
    h=q**7
    m0=F(h-1,h)
    for order in range(1,25):
        falling=factorial(24)//factorial(24-order)
        moment=F(falling,h) # all candidates hit the same single nonzero U
        reference=m0*falling*F(1,h-1)**order
        assert moment/reference==(h-1)**(order-1)
    print('Candidates:24; real affine rank:7; quotient order:3329^7')
    print('Minimum M squared:18; maximum candidate squared:',radius2)
    print('Uniform radius squared14 plus height squared1 is strictly below18.')
    print('All 276 pair differences lie in M; all 24 labels coincide and are nonzero.')
    print('All orders1..24: actual/reference factorial moment ratio=(h-1)^(order-1).')
    print('This excludes a minimum-only moment argument, not the production BKZ theorem.')


if __name__=='__main__':
    main()
