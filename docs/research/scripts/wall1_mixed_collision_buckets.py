"""Exact signed covariance of weighted linear-constraint counts."""
from fractions import Fraction as F
from itertools import product


def buckets(constraints,q):
    result={}
    for weight,y,x in constraints:
        y=tuple(a%q for a in y); x=tuple(a%q for a in x)
        pivot=next((a for a in y if a),None)
        if pivot is None:
            continue  # Deterministic true/false events contribute zero covariance.
        inv=pow(pivot,-1,q)
        line=tuple(a*inv%q for a in y)
        target=tuple(a*inv%q for a in x)
        cell=result.setdefault(line,{})
        cell[target]=cell.get(target,F(0))+weight
    return result


def covariance(left,right,q,m):
    B,D=buckets(left,q),buckets(right,q)
    p=F(1,q**m)
    answer=F(0)
    for line in B.keys() & D.keys():
        b,d=B[line],D[line]
        matching=sum((weight*d.get(x,F(0)) for x,weight in b.items()),F(0))
        answer+=p*matching-p*p*sum(b.values())*sum(d.values())
    return answer


def value(constraints,A,q):
    return sum((weight for weight,y,x in constraints
                if all(sum(a*b for a,b in zip(row,y))%q==target%q
                       for row,target in zip(A,x))),F(0))


def main():
    checked=0
    for q,m,d in ((2,1,2),(3,1,2),(2,2,2)):
        matrices=[tuple(flat[i*d:(i+1)*d] for i in range(m))
                  for flat in product(range(q),repeat=m*d)]
        constraints=[(F(1),y,x) for y in product(range(q),repeat=d)
                     for x in product(range(q),repeat=m)]
        values=[[value([b],A,q) for A in matrices] for b in constraints]
        means=[sum(v)/len(matrices) for v in values]
        for i,b in enumerate(constraints):
            for j,c in enumerate(constraints):
                exact=sum(x*y for x,y in zip(values[i],values[j]))/len(matrices)-means[i]*means[j]
                assert covariance([b],[c],q,m)==exact
                checked+=1
        # Weighted, repeated constraints and forced events in the same calculation.
        left=[(F(i+1,3),b[1],b[2]) for i,b in enumerate(constraints[::2])]
        right=[(F(i+2,5),b[1],b[2]) for i,b in enumerate(constraints[::3])]+constraints[:2]
        lv=[value(left,A,q) for A in matrices];rv=[value(right,A,q) for A in matrices]
        assert covariance(left,right,q,m)==sum(x*y for x,y in zip(lv,rv))/len(matrices)-sum(lv)*sum(rv)/len(matrices)**2
    # Conditional law A e_0=1: subtract the prescribed contribution, quotient input.
    left=[(F(2),(1,1,0),(1,)),(F(1),(2,0,1),(0,))]
    right=[(F(3),(0,2,0),(0,)),(F(4),(1,0,2),(2,))]
    reduce=lambda C:[(w,y[1:],((x[0]-y[0])%3,)) for w,y,x in C]
    matrices=[((1,a,b),) for a,b in product(range(3),repeat=2)]
    lv=[value(left,A,3) for A in matrices];rv=[value(right,A,3) for A in matrices]
    assert covariance(reduce(left),reduce(right),3,1)==sum(x*y for x,y in zip(lv,rv))/9-sum(lv)*sum(rv)/81
    print(f'Passed {checked} exact constraint-pair covariance checks, plus weighted and conditioned cases.')


if __name__=='__main__':
    main()
