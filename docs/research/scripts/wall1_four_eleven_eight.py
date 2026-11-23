"""Reduced short pairs with a four-circuit and seven new positions."""
from wall1_rare_second_line import norm_rows

def checks():
    firsts=[v for v in norm_rows(11,8) if all(v[4:])]
    checked=0
    attained=False
    for norm in (8,10):
        seconds=list(norm_rows(11,norm))
        for a in firsts:
            assert sum(bool(x) for x in a[:4])==1 and all(abs(x)<=1 for x in a)
            for b in seconds:
                # Both rows reduce to a one-dimensional space on new positions.
                if any(b[i]*a[4]!=b[4]*a[i] for i in range(4,11)):continue
                diff=tuple(b[i]*a[4]-b[4]*a[i] for i in range(4))
                if not all(diff):continue
                dot=sum(x*y for x,y in zip(a,b))
                if 2*abs(dot)>8:continue
                assert norm==10 and not any(b[4:])
                assert abs(dot)<=2
                assert 8*norm-dot*dot>=76
                attained |= 8*norm-dot*dot==76
                checked+=1
    assert checked and attained
    print('Passed',checked,'reduced pair checks; minimum Gram76 attained.')
    a=(2,-2,1,-1)+(0,)*7
    b=(1,-1,1,0)+(-1,)*4+(1,)*3
    assert sum(a)==sum(b)==0
    assert sum(x*x for x in a)==sum(x*x for x in b)==10
    assert sum(x*y for x,y in zip(a,b))==5
    # Primitive Gram [[10,5],[5,10]]: every nonzero integer combination
    # has norm at least10, since u^2+u*v+v^2 is a positive integer.
    assert a[2]*b[4]-a[4]*b[2]==-1
    print('Verified norm-ten boundary witness: determinant75, second height15/2.')

if __name__=='__main__':checks()
