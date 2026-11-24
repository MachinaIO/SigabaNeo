"""Exact weighted diagonal majorizers for every certified H6/H7 chart."""
from fractions import Fraction as F
from itertools import product
from wall1_short_relation_shapes import balanced_rows


def check_chart(cols,determinant):
    rows=list(zip(*cols));r=len(rows)
    G=[[F(i==j)+sum(x*y for x,y in zip(rows[i],rows[j]))
        for j in range(r)] for i in range(r)]
    shared=[i for i,row in enumerate(rows) if all(row)]
    assert len(shared)==(1 if determinant==15 else 2)
    checked=0
    for t in (F(1),F(3,2),F(2),F(3)):
        w=[F(1) if i in shared else t for i in range(r)]
        d=[G[i][i]+sum(abs(G[i][j])*w[j]/w[i] for j in range(r) if j!=i)
           for i in range(r)]
        if determinant==12:expected=[5+2*t]*2+[2+2/t]*2
        elif determinant==15:expected=[3+4*t]+[3+1/t]*4
        else:continue  # D16 retains the previous scalar spectral majorizer.
        assert sorted(d)==sorted(expected)
        for x in product((-1,0,1),repeat=r):
            lhs=sum(d[i]*x[i]**2 for i in range(r))-sum(
                G[i][j]*x[i]*x[j] for i in range(r) for j in range(r))
            rhs=sum(abs(G[i][j])*w[i]*w[j]*(F(x[i])/w[i]
                    -(1 if G[i][j]>=0 else -1)*F(x[j])/w[j])**2
                    for i in range(r) for j in range(i+1,r))
            assert lhs==rhs and rhs>=0
            checked+=1
    return checked


def checks():
    total=0;charts=0
    for u in balanced_rows((0,1,2,3),6):
        for v in balanced_rows((0,1,4,5),6):
            cols=[tuple(-F(row[i],row[p]) for i in (0,1,2,4))
                  for row,p in ((u,3),(v,5))]
            det=16-sum(x*y for x,y in zip(*cols))**2
            total+=check_chart(cols,det);charts+=1
    for shared in (0,3):
        C={0,1,2,3};e=max(C-{shared})
        basis=tuple(i for i in range(7) if i not in (e,6))
        for a in balanced_rows(tuple(sorted(C)),7):
            for b in balanced_rows(tuple(sorted({shared,4,5,6})),7):
                cols=[tuple(-F(row[i],row[p]) for i in basis)
                      for row,p in ((a,e),(b,6))]
                total+=check_chart(cols,15);charts+=1
    print('Passed canonical charts:',charts,'weighted-square identities:',total)

if __name__=='__main__':checks()
