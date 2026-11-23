"""All-integer projected minimum for the eleven-position determinant31 anchor."""
from fractions import Fraction as F
from itertools import combinations,product
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def checks():
    a=(1,1,1,1)+(0,)*7
    b=(1,0,0,0)+(1,)*7
    assert sum(x*y for x,y in zip(a,b))==1
    def energy(v):
        x=sum(u*w for u,w in zip(a,v))
        y=sum(u*w for u,w in zip(b,v))
        return 31*sum(w*w for w in v)-8*x*x+2*x*y-4*y*y
    checked=0
    best=31
    for norm in range(4):
        for support in combinations(range(11),norm):
            for signs in product((-1,1),repeat=norm):
                v=[0]*11
                for i,sign in zip(support,signs):v[i]=sign
                value=energy(v)
                assert value>=0
                if value>0:best=min(best,value)
                checked+=1
    assert checked==1563 and best==21
    assert energy((1,)+(0,)*10)==21
    radius=(F(4)+F(31,4))/4
    assert radius==F(47,16)
    assert radius+F(21,31)==F(1793,496)<4
    witnesses=0
    outside=[v for v in norm_rows(11,8) if all(v[4:])]
    for first in balanced_rows((0,1,2,3),11):
        for second in outside:
            shared=[i for i in range(4) if second[i]]
            assert len(shared)==1 and all(abs(x)<=1 for x in second)
            dot=sum(x*y for x,y in zip(first,second))
            assert abs(dot)==1
            # Flip row2 so shared entries agree, then flip coordinate signs.
            second=tuple(dot*x for x in second)
            j=shared[0]
            order=[j]+[i for i in range(4) if i!=j]+list(range(4,11))
            columns=[]
            for i in order:
                sign=first[i] if first[i] else second[i]
                columns.append((sign*first[i],sign*second[i]))
            assert tuple(columns)==tuple(zip(a,b))
            witnesses+=1
    assert witnesses==420
    assert 31*24**4<3329**2
    print('Passed1563 exact projection checks and420 signed-permutation certificates.')
    print('Projected squared minimum21/31; rounding squared radius47/16; cutoff1793/496<4.')


if __name__=='__main__':checks()
