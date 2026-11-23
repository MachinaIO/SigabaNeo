"""Girth-eight restriction for norm-eight pairs on eleven positions."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows


def finite_checks():
    a=(1,1,1,1,-1,-1,-1,-1,0,0,0)
    checked=0
    accepted=Counter()
    for b in norm_rows(11,8,minimum_support=8):
        if not all(b[8:]):continue
        assert sum(bool(x) for x in b[:8])==5
        dot=sum(x*y for x,y in zip(a,b))
        assert abs(dot) in (1,3,5)
        # Nonzero two-row column directions are precisely these four types.
        groups=Counter()
        for x,y in zip(a,b):
            assert x or y
            groups[(0,1) if x==0 else (1,y*x)]+=1
        girth=11-max(groups.values())
        assert girth==11-max(3,(5+abs(dot))//2)
        assert (girth>=8)==(abs(dot)==1)
        if girth>=8:
            assert 64-dot*dot==63
            accepted[girth]+=1
        checked+=1
    assert checked==1960 and sum(accepted.values())>0
    print(f'Passed all {checked} norm-eight partners; girth-eight pairs have Gram determinant63.')


def girth_seven_checks():
    checked=0
    for size in range(8,12):
        a=(1,1,1,1,-1,-1,-1,-1)+(0,)*(size-8)
        accepted=Counter()
        for b in norm_rows(size,8,minimum_support=7):
            if not all(b[8:]):continue
            if b==a:continue
            groups=Counter((0,1) if x==0 else (1,y*x) for x,y in zip(a,b))
            girth=size-max(groups.values())
            dot=sum(x*y for x,y in zip(a,b))
            checked+=1
            if size<=10:
                assert girth<8
            if girth>=6:
                assert size>=10
                if size==10:assert abs(dot)<=2
                if size==11 and abs(dot)<=4:assert abs(dot)<=3
            if girth<7:continue
            assert size>=10
            assert abs(dot)<=(0 if size==10 else 3)
            assert 64-dot*dot >= (64 if size==10 else 55)
            accepted[64-dot*dot]+=1
        if size>=10:assert accepted
        print(f'H={size}: girth-seven norm-eight pair determinants {dict(accepted)}')
    print(f'Passed {checked} girth-seven partner checks.')


def all_shapes_eleven_checks():
    checked=0
    for a in ((1,1,1,1,-1,-1,-1,-1,0,0,0),
              (2,1,-1,-1,-1,0,0,0,0,0,0)):
        for b in norm_rows(11,8):
            if not all(x or y for x,y in zip(a,b)):continue
            dot=sum(x*y for x,y in zip(a,b))
            if abs(dot)>4:continue  # Gauss reduction for two norm-eight rows.
            assert abs(dot)<=3
            assert 64-dot*dot>=55
            checked+=1
    assert checked>0
    print(f'Passed {checked} full-support reduced pairs including support-five shapes.')


def norm_ten_girth_eight_checks():
    checked=0
    for size in (10,11):
        for first_norm in (8,10):
            a=(1,)*(first_norm//2)+(-1,)*(first_norm//2)+(0,)*(size-first_norm)
            for b in norm_rows(size,10,minimum_support=8):
                assert all(abs(x)<=1 for x in b)
                if b==a or not all(x or y for x,y in zip(a,b)):continue
                groups=Counter((0,1) if x==0 else (1,y*x) for x,y in zip(a,b))
                assert size-max(groups.values())<8
                checked+=1
    print(f'Passed{checked} norm-eight/ten and ten/ten exclusion checks.')


if __name__=='__main__':
    finite_checks()
    girth_seven_checks()
    all_shapes_eleven_checks()
    norm_ten_girth_eight_checks()
