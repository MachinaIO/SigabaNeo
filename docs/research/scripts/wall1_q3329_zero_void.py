"""Exact zero-to-positive void example at q=3329 and appended width 506.

K=Z^505; M=ker(H mod q), where H has 20 scalar 21-column blocks
and 5 scalar 17-column blocks. Thus rank(H)=25 and det(M)=q^25.
This is a rank-25 marked example, NOT a reachable state within the first
406 exact width-506 restart freezes from determinant q^400. A deterministic
determinant floor excludes it (see the accompanying note). A positive, tiny
branch does not refute a quantitative production probability budget.

Radius law checked here: n=506, V_n=pi^253/253!, g=(det(M)/V_n)^(1/n),
L=1.1*g, incoming R^2=L^2-1, outgoing B^2=L^2*(s^2)^(-1/n)-1.
For U=the first column in the first 21-column block, the actual shortest
append winner is (e_1,1), up to sign, with s^2=2. Projection replaces the
first coordinate cost by half its square and leaves other costs unchanged.
"""
from collections import Counter
from fractions import Fraction as F
from math import factorial, isqrt, exp, lgamma, log, pi

Q = 3329
COLS21 = [scale*i for scale in (1,15,225) for i in range(1,8)]
COLS17 = [1062,53,895,434,402,699,981,747,1567,1399,
          1381,769,516,568,278,1348,117]


def exact_distances(columns, weights, cap):
    """Minimize sum w_i*z_i^2 for each residue, truncated above cap.

    All weights are positive integers. Any competitor of cost<=cap has
    |z_i|<=floor(sqrt(cap/w_i)). Costs cannot decrease as coordinates are
    appended, so discarded partial costs cannot later become relevant.
    The sentinel cap+1 means cost>cap. Once all entries<=cap, the array
    is the exact unrestricted minimum for every residue, not just a bound.
    """
    assert len(columns)==len(weights) and all(w>0 for w in weights)
    distance = [cap+1]*Q
    distance[0] = 0
    for h,w in zip(columns,weights):
        options = [(z*h % Q, w*z*z)
                   for z in range(-isqrt(cap//w),isqrt(cap//w)+1)]
        updated = [cap+1]*Q
        for residue,oldcost in enumerate(distance):
            if oldcost>cap:
                continue
            for shift,cost in options:
                newcost=oldcost+cost
                if newcost<=cap:
                    target=(residue+shift)%Q
                    if newcost<updated[target]:
                        updated[target]=newcost
        distance=updated
    assert max(distance)<=cap, 'Increase cap: unrestricted maxima not certified'
    return distance


def atan_bounds(m,terms):
    partial=sum((F((-1)**j,(2*j+1)*m**(2*j+1))
                 for j in range(terms)),F(0))
    adjacent=partial+F((-1)**terms,(2*terms+1)*m**(2*terms+1))
    return min(partial,adjacent),max(partial,adjacent)


def pi_bounds():
    # Machin identity and alternating-series remainder bounds, entirely rational.
    a0,a1=atan_bounds(5,40)
    b0,b1=atan_bounds(239,12)
    return 16*a0-4*b1,16*a1-4*b0


def main():
    assert 20*len(COLS21)+5*len(COLS17)==505
    for columns in (COLS21,COLS17):
        assert all(0<h<Q for h in columns)
        assert len(set(min(h,Q-h) for h in columns))==len(columns)
    # Distinct nonzero columns up to sign within a block, and disjoint support
    # across blocks, exclude all horizontal kernel vectors of norm^2=1 or 2.
    # Every block contains a nonzero entry, giving rank 25 over prime F_3329.
    # Selected U is column 1. A norm-1 vertical vector cannot match U!=0;
    # (e_1,1) is available with norm^2=2. Hence it is an actual shortest winner.

    d21=exact_distances(COLS21,[1]*21,4)
    d17=exact_distances(COLS17,[1]*17,4)
    # Twice the projected cost. At cap 6, |z_1|<=2; other |z_i|<=1.
    projected21=exact_distances(COLS21,[1]+[2]*20,6)
    assert Counter(d21)=={0:1,1:42,2:600,3:2686}
    assert Counter(d17)=={0:1,1:34,2:500,3:2182,4:612}
    assert Counter(projected21)=={0:1,1:2,2:40,3:58,4:542,5:416,6:2270}
    assert d21[114]==3 and projected21[114]==6 and d17[6]==4
    assert 20*max(d21)+5*max(d17)==80
    assert F(max(projected21),2)+19*max(d21)+5*max(d17)==80

    # With T=L^2, T^506 = (121/100)^506 * (q^25*253!)^2 / pi^506.
    # Strict comparisons certify R^2>80 and B^2<80, without real roots.
    lo,hi=pi_bounds()
    assert F(3)<lo<hi<F(22,7)
    A=F(121,100)**506*(Q**25*factorial(253))**2
    assert 81**506*hi**506 < A
    assert A < 2*81**506*lo**506

    # Deterministic restart exclusion: Minkowski's cube bound gives
    # D_f >= D_(f-1)^(505/506)/sqrt(506), D_0=q^400.
    # For f<=406 its log2 lower bound exceeds 6215/9 > 57*12.
    assert 9*505**406 > 4*506**406
    assert 2**11 < Q < 2**12 and 506 < 2**9
    log2_floor = F(4,9)*400*11 - 253*F(5,9)*9
    assert log2_floor == F(6215,9) > 57*12

    # Product separation makes the global coset distances sums of scalar ones.
    # The concrete mark (114,...,114,6,...,6), with 20 and 5 repetitions,
    # has projected distance^2 exactly 80. In fact this many marks do:
    far_marks=2270*2686**19*612**5
    assert 0<far_marks<Q**25
    print('Exact scalar histograms:',sorted(Counter(d21).items()),
          sorted(Counter(d17).items()))
    print('Twice projected 21-block cost histogram:',sorted(Counter(projected21).items()))
    print('Rank 25; input width 505; appended width 506; determinant 3329^25.')
    print('Incoming covering norm^2 = 80; projected covering norm^2 = 80.')
    print('Exact radius inequalities: incoming R^2 > 80 > outgoing B^2.')
    print('Incoming void = 0; outgoing void >=',F(far_marks,Q**25))
    print('Selected update probability = 1/3329^25; no quantitative budget refutation.')
    print('Restart exclusion: D_f > q^57 for f<=406, so D=q^25 is unreachable.')
    T=1.21*exp((25*log(Q)+lgamma(254))/253)/pi
    print('Display-only radii:',T-1,T*exp(-log(2)/506)-1)
    print('All integer DP and rational radius checks passed.')


if __name__=='__main__':
    main()
