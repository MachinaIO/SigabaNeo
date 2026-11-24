"""Exact shared-four H7 chart checks, including the prescribed six-circuit."""
from fractions import Fraction as F
from wall1_short_relation_shapes import balanced_rows


def checks():
    checked=0
    C={0,1,2,3}
    for shared in (0,3):
        second={shared,4,5,6};e=max(C-{shared})
        basis=tuple(i for i in range(7) if i not in (e,6))
        for a in balanced_rows(tuple(sorted(C)),7):
            for b in balanced_rows(tuple(sorted(second)),7):
                assert a[6]==b[e]==0 and abs(a[e]*b[6])==1
                u=tuple(-F(a[i],a[e]) for i in basis)
                v=tuple(-F(b[i],b[6]) for i in basis)
                assert sum(u)==sum(v)==1
                assert sum(x*x for x in u)==sum(x*x for x in v)==3
                dot=sum(x*y for x,y in zip(u,v))
                assert abs(dot)==1 and 16-dot*dot==15
                six=tuple(b[shared]*x-a[shared]*y for x,y in zip(a,b))
                assert {i for i,x in enumerate(six) if x}==(C-{shared})|{4,5,6}
                assert abs(a[shared])==1  # determinant of relation-row change
                checked+=1
    print('Passed exact H7 canonical-chart and six-circuit checks:',checked)


def completion_checks():
    from mpmath import iv
    from wall1_anchored_dual_completion import completion_details
    iv.dps=60;I=iv.mpf;q=3329
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    s={'iv':iv,'q':q,'N':518,'radius':iv.sqrt(R2)}
    tested=0
    for r,h in ((5,7),(5,9),(9,24)):
        for free in (None,I(518)/(2*R2)):
            kw=dict(anchor_size=7,free_beta=free)
            generic=completion_details(s,r,h,coordinate_count=518,**kw)
            full=completion_details(s,r,h,coordinate_count=518,anchor_gram_det=15,**kw)
            inputs=completion_details(s,r,h,anchor_gram_det=15,**kw)
            assert 0<full[0] and full[0].b<=generic[0].b and full[0].b<=inputs[0].b
            if h>r+2:
                assert completion_details(s,r,h,coordinate_count=518,anchor_gram_det=15,**kw) is full
            tested+=1
    try:completion_details(s,5,9,anchor_size=6,anchor_gram_det=15)
    except AssertionError:pass
    else:raise AssertionError('D15 used outside H7')
    print('Passed H7 normalized completion/cache cases:',tested)


if __name__=='__main__':
    checks()
    completion_checks()
