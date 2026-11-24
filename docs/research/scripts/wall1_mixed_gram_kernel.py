"""Exact algebraic and modular-alias checks for the mixed Gram kernel."""
from fractions import Fraction as F
from itertools import product


def transpose(a): return list(map(list,zip(*a)))
def mul(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b): return [[x+y for x,y in zip(row,col)] for row,col in zip(a,b)]
def neg(a): return [[-x for x in row] for row in a]
def diag(v): return [[F(x) if i==j else F(0) for j in range(len(v))] for i,x in enumerate(v)]
def inv(a):
    n=len(a); b=[list(map(F,row))+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        pivot=next(i for i in range(j,n) if b[i][j]);b[j],b[pivot]=b[pivot],b[j]
        t=b[j][j];b[j]=[x/t for x in b[j]]
        for i in range(n):
            if i!=j:
                t=b[i][j];b[i]=[x-t*y for x,y in zip(b[i],b[j])]
    return [row[n:] for row in b]
def quad(v,a): return mul(mul([v],a),transpose([v]))[0][0]


def main():
    checks=0
    dual_checks=0
    for w in ([[1],[0]],[[2],[-1]],[[2,3],[-1,-2]],[[6,-4],[-5,5]]):
        # Every coefficient column is affine, including large integer lifts.
        assert all(sum(col)==1 for col in zip(*w))
        s=len(w[0]); d=diag([F(2,3),F(4,5)]); lam=diag([F(j+1,2) for j in range(s)])
        g=add(d,mul(mul(w,lam),transpose(w))); gi=inv(g)
        schur=add(lam,neg(mul(mul(mul(mul(lam,transpose(w)),gi),w),lam)))
        # Woodbury identity, retaining full alias dimension.
        assert schur==inv(add(inv(lam),mul(mul(transpose(w),inv(d)),w)))
        for q in (3,5):
            top=mul(w,lam)
            joint=[g[i]+[-q*v for v in top[i]] for i in range(2)]
            bottom=mul(lam,transpose(w))
            joint += [[-q*v for v in bottom[j]]+[q*q*v for v in lam[j]] for j in range(s)]
            joint_inv=inv(joint)
            for a in product(range(-1,2),repeat=2):
                for b in product(range(-1,2),repeat=s):
                    wb=mul(w,transpose([b]))
                    shifted=[a[i]+F(wb[i][0],q) for i in range(2)]
                    assert quad(a+b,joint_inv)==quad(shifted,inv(d))+quad(b,inv(lam))/(q*q)
                    dual_checks+=1

            for x in product(range(-2,3),repeat=2):
                xw=mul([x],w)[0]
                for z in product(range(-1,2),repeat=s):
                    residual=[a-q*b for a,b in zip(xw,z)]
                    shift=mul(mul(mul([z],lam),transpose(w)),gi)[0]
                    delta=[a-q*b for a,b in zip(x,shift)]
                    assert quad(x,d)+quad(residual,lam)==quad(delta,g)+q*q*quad(z,schur)
                    checks+=1
            # Exactly one centered alias for each centered basis row.
            for x in product(range(-(q//2),q//2+1),repeat=2):
                xw=mul([x],w)[0]
                residues=[(a+q//2)%q-q//2 for a in xw]
                z=[(a-b)//q for a,b in zip(xw,residues)]
                assert all(a-q*b==c for a,b,c in zip(xw,z,residues))
                assert all(abs(c)<=q//2 for c in residues)
                checks+=1
    # A fixed-X example where the nonzero alias removes an arbitrarily cheap
    # unwrapped-coefficient heuristic: x=(2,-2), affine v=(2,-1), q=5.
    x=(2,-2); v=(2,-1); raw=sum(a*b for a,b in zip(x,v)); centered=(raw+2)%5-2
    assert raw==6 and centered==1
    print('Passed exact Schur, Woodbury, and centered-alias checks:',checks+1)
    print('Passed exact joint dual inverse checks:',dual_checks)
    print('Explicit q=5 unwrapped square / modular square:',raw*raw,centered*centered)

if __name__=='__main__': main()
