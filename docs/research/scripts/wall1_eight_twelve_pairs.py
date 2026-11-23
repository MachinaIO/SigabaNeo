"""Short reduced pairs of girth at least eight on twelve positions."""
from collections import Counter
from math import comb, gcd
from wall1_rare_second_line import norm_rows


def checks():
    counts=Counter()
    for first,second in ((8,8),(8,10),(10,10)):
        a=(1,)*(first//2)+(-1,)*(first//2)+(0,)*(12-first)
        for b in norm_rows(12,second,minimum_support=8):
            assert all(abs(x)<=1 for x in b)
            if not all(x or y for x,y in zip(a,b)):continue
            dot=sum(x*y for x,y in zip(a,b))
            if 2*abs(dot)>first:continue
            groups=Counter()
            for x,y in zip(a,b):
                d=gcd(x,y)
                direction=(x//d,y//d)
                if direction[0]<0 or (direction[0]==0 and direction[1]<0):
                    direction=tuple(-v for v in direction)
                groups[direction]+=1
            if max(groups.values())>4:continue
            if (first,second)==(8,10):assert abs(dot)<=2
            if (first,second)==(10,10):assert dot==0
            counts[first,second]+=1
    assert counts=={(8,8):2450,(8,10):2688,(10,10):1500}
    lines=list(norm_rows(12,8,minimum_support=8))
    assert len(lines)==35*comb(12,8)==17325
    print('Passed eligible reduced-pair checks:',dict(counts))
    print('Norm-eight line count:',len(lines),'unordered pair cover:',comb(len(lines),2))


if __name__=='__main__':checks()
