"""Short reduced pairs on twelve positions with prescribed girth four to seven."""
from collections import Counter
from math import gcd
from wall1_rare_second_line import norm_rows


def finite_checks():
    representatives={8:((1,)*4+(-1,)*4+(0,)*4,(2,1,-1,-1,-1)+(0,)*7),
                     10:((1,)*5+(-1,)*5+(0,)*2,(2,1,1,-1,-1,-1,-1)+(0,)*5,
                         (2,-2,1,-1)+(0,)*8)}
    checked=0
    for first_norm,second_norm in ((8,8),(8,10),(10,10)):
        seconds=list(norm_rows(12,second_norm,minimum_support=4))
        eligible=Counter()
        for a in representatives[first_norm]:
            for b in seconds:
                if not all(x or y for x,y in zip(a,b)):continue
                dot=sum(x*y for x,y in zip(a,b))
                if 2*abs(dot)>first_norm:continue
                groups=Counter()
                for x,y in zip(a,b):
                    g=gcd(x,y)
                    direction=(x//g,y//g)
                    if direction[0]<0 or (direction[0]==0 and direction[1]<0):
                        direction=tuple(-z for z in direction)
                    groups[direction]+=1
                supports={12-v for v in groups.values()}|{12}
                gram=first_norm*second_norm-dot*dot
                for c in (4,5,6,7):
                    if c not in supports or min(supports)<c:continue
                    # The second prescribed circuit meets a proper nonempty
                    # subset of C, so its length lies in [13-c,11].
                    if not supports.intersection(range(13-c,12)):continue
                    if c==7:
                        assert (first_norm,second_norm)!=(8,8)
                    elif c==5:
                        assert first_norm==8
                        assert gram >= (60 if second_norm==8 else 64)
                    else:
                        assert first_norm!=8
                        assert gram>=84
                    eligible[c,gram]+=1
                checked+=1
        if first_norm==10:assert eligible
        print((first_norm,second_norm),'eligible circuit/determinant counts',dict(eligible))
    print(f'Passed{checked} full-support reduced pair checks, including coefficient-two shapes.')


if __name__=='__main__':
    finite_checks()
