"""Universal q=3 rectangular obstruction and a certified finite q=5 grid."""
from fractions import Fraction as F
from itertools import product


def atan_bounds(m, count):
    partial = sum((F((-1)**j, (2*j+1)*m**(2*j+1))
                   for j in range(count)), F(0))
    next_partial = partial + F((-1)**count, (2*count+1)*m**(2*count+1))
    return min(partial, next_partial), max(partial, next_partial)


def pi_bounds():
    a0,a1 = atan_bounds(5,40)
    b0,b1 = atan_bounds(239,12)
    return 16*a0-4*b1, 16*a1-4*b0


def main():
    # pi>3 gives V_3=4*pi/3>4.  This rational upper bound already
    # contradicts the necessary AM-GM coefficient 27 for covering corners.
    coefficient_upper = F(11,10)**6 * F(9,4)**2
    assert coefficient_upper < 27
    lo,hi = pi_bounds()
    assert lo > 3
    print('Universal q=3 coefficient <',coefficient_upper,'<27: verified')
    values = list(map(F, ['1/4','1/2','3/4','1','3/2','2','3']))
    rows=[]
    for q in (3,5):
        for a,b in product(values, repeat=2):
            if a>b:
                continue
            coefficient = F(11,10)**6 * (q*q*a*b)**2 / F(4,3)**2
            lower = coefficient/(hi*hi)
            upper = coefficient/(lo*lo)
            hits=0
            for x,y in product(range(-(q//2),q//2+1), repeat=2):
                threshold = (1+a*a*x*x+b*b*y*y)**3
                if threshold <= lower:
                    hits += 1
                else:
                    assert threshold > upper, 'Undecided pi interval comparison'
            p = F(q*q-hits,q*q)
            assert p >= F(7,25)
            if q==3:
                assert p >= F(4,9)
            rows.append((p,q,a,b))
    print('Certified unordered grid configurations:',len(rows))
    print('Undecided memberships: 0; incoming P<7/25: 0')
    for q in (3,5):
        minimum=min(p for p,qq,_,_ in rows if qq==q)
        fixtures=[(a,b) for p,qq,a,b in rows if qq==q and p==minimum]
        print('q:',q,'minimum incoming P:',minimum,'at:',fixtures)


if __name__=='__main__':
    main()
