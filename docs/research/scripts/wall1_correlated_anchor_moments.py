"""Exact correlated-moment profiles for the certified H6/H7 anchor charts.

For H(x)=sum_z exp(-tau*(x+q*z)^T M*(x+q*z)), M=G^-1,
write w_i=z_i-z_1, w_1=0, and y=x+q*z_1. Completing squares gives
  sum_i ||y+q*w_i||_M^2
    = L*||y+q*mean(w)||_M^2
      +q^2*(sum_i ||w_i||_M^2-L*||mean(w)||_M^2).
The second term is at least q^2/(L*lambda)*sum_{i>1} ||w_i||^2
when G<=lambda*I. Never round mean(w): its arbitrary real shift is
handled by the shifted-lattice theta maximum, proved by Poisson summation.
Thus the alias factor is C=theta(tau*q^2/(L*lambda))^(r*(L-1)).

The full normalized L-moment is bounded by
  C/q^r * Theta_Zr(L*tau*M).
For any affine coordinate-sum hyperplane, it is bounded by
  C/q^(r-1) * Theta_Z^(r-1)(L*tau*E^T*M*E)
             * theta(L*tau*q^2/H0),
where E=[e_1-e_r,...,e_(r-1)-e_r]. Indeed the congruence kernel
Lambda={y:sum(y)=0 mod q} decomposes into sum(y)=q*j layers.
Subtract their real M-orthogonal centers q*j*G*1/(1^T*G*1),
and apply the shifted theta maximum on ker(sum) in each layer.
Since A^T*1=(1,1), 1^T*G*1=H0 and det(E^T*M*E)=H0/det(G).

For a positive definite rational Gram matrix, its LDL diagonal (s_i)
gives Theta(t*Gram)<=product_i theta(t*s_i), by eliminating coordinates
and bounding each shifted one-dimensional Gaussian by its centered sum.
This script enumerates ALL charts from the two existing normalizer scripts;
callers must maximize each complete candidate over the returned profiles.
It does not select one convenient chart for the whole determinant family.
"""
from collections import Counter
from fractions import Fraction as F
from math import prod

from wall1_short_relation_shapes import balanced_rows


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def inverse(a):
    n=len(a)
    work=[[F(x) for x in a[i]]+[F(i==j) for j in range(n)] for i in range(n)]
    for i in range(n):
        p=next(j for j in range(i,n) if work[j][i])
        work[i],work[p]=work[p],work[i]
        pivot=work[i][i]
        work[i]=[x/pivot for x in work[i]]
        for j in range(n):
            if j!=i:
                scale=work[j][i]
                work[j]=[x-scale*y for x,y in zip(work[j],work[i])]
    result=[row[n:] for row in work]
    assert multiply(a,result)==[[F(i==j) for j in range(n)] for i in range(n)]
    return result


def ldl_pivots(a):
    work=[[F(x) for x in row] for row in a]
    assert work==transpose(work)
    pivots=[]
    for i in range(len(work)):
        pivot=work[i][i]
        assert pivot>0
        pivots.append(pivot)
        for j in range(i+1,len(work)):
            for k in range(i+1,len(work)):
                work[j][k]-=work[j][i]*work[i][k]/pivot
    return tuple(pivots)


def canonical_charts():
    basis=(0,1,2,4)
    for a in balanced_rows((0,1,2,3),6):
        for b in balanced_rows((0,1,4,5),6):
            assert a[5]==b[3]==0 and abs(a[3]*b[5])==1
            cols=[tuple(-F(row[i],row[p]) for i in basis)
                  for row,p in ((a,3),(b,5))]
            yield transpose(cols)
    first={0,1,2,3}
    for shared in (0,3):
        second={shared,4,5,6}
        e=max(first-{shared})
        basis=tuple(i for i in range(7) if i not in (e,6))
        for a in balanced_rows(tuple(sorted(first)),7):
            for b in balanced_rows(tuple(sorted(second)),7):
                assert a[6]==b[e]==0 and abs(a[e]*b[6])==1
                cols=[tuple(-F(row[i],row[p]) for i in basis)
                      for row,p in ((a,e),(b,6))]
                yield transpose(cols)


def moment_profiles():
    """Return D -> distinct (full LDL pivots, hyperplane LDL pivots)."""
    result={12:set(),16:set(),15:set()}
    counts=Counter()
    for a in canonical_charts():
        r=len(a);h=r+2
        assert [sum(col) for col in transpose(a)]==[1,1]
        small=multiply(transpose(a),a)
        assert small[0][0]==small[1][1]==3
        determinant=16-small[0][1]**2
        spectral=4+abs(small[0][1])
        assert spectral=={12:6,16:4,15:5}[determinant]
        g=multiply(a,transpose(a))
        for i in range(r):g[i][i]+=1
        assert prod(ldl_pivots(g))==determinant
        assert sum(map(sum,g))==h
        m=inverse(g)
        e=[[F(i==j)-F(i==r-1) for j in range(r-1)] for i in range(r)]
        root=multiply(transpose(e),multiply(m,e))
        full_profile=ldl_pivots(m)
        root_profile=ldl_pivots(root)
        assert prod(full_profile)==F(1,determinant)
        assert prod(root_profile)==F(h,determinant)
        result[int(determinant)].add((full_profile,root_profile))
        counts[int(determinant)]+=1
    assert counts=={12:5,16:4,15:18}
    return {d:tuple(sorted(profiles)) for d,profiles in result.items()}


def main():
    for d,profiles in moment_profiles().items():
        print('D',d,'distinct profiles',len(profiles))
        for full,root in profiles:
            print(' full',tuple(map(str,full)),'root',tuple(map(str,root)))
    print('Passed all 27 canonical charts: inverse identities, positive LDL, determinants and affine sums.')


if __name__=='__main__':
    main()


def square_identity_checks():
    tested=0
    def norm(m,x):
        return sum(x[i]*m[i][j]*x[j] for i in range(len(x)) for j in range(len(x)))
    for a in canonical_charts():
        r=len(a);g=multiply(a,transpose(a))
        for i in range(r):g[i][i]+=1
        m=inverse(g);h=r+2
        e=[[F(i==j)-F(i==r-1) for j in range(r-1)] for i in range(r)]
        root=multiply(transpose(e),multiply(m,e))
        for L in (2,3,5):
            for seed in range(5):
                y=[F((seed+i)%3-1) for i in range(r)]
                ws=[[F(0)]*r]+[[F((seed+i+j)%3-1) for i in range(r)] for j in range(1,L)]
                mean=[sum(w[i] for w in ws)/L for i in range(r)]
                variance=sum(norm(m,w) for w in ws)-L*norm(m,mean)
                direct=sum(norm(m,[y[i]+3*w[i] for i in range(r)]) for w in ws)
                assert direct==L*norm(m,[y[i]+3*mean[i] for i in range(r)])+9*variance
                assert variance>=sum(norm(m,w) for w in ws)/L
                # Orthogonal center for an arbitrary fractional vector.
                v=[y[i]+3*mean[i] for i in range(r)];total=sum(v)
                center=[total*sum(row)/h for row in g]
                tangent=[v[i]-center[i] for i in range(r)]
                assert sum(tangent)==0
                assert norm(m,v)==total**2/h+norm(root,tangent[:-1])
                tested+=1
    print('Passed exact moment and hyperplane square identities:',tested)

if __name__=='__main__':square_identity_checks()
