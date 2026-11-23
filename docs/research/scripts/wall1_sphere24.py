"""Rank-24 search in the spherical polynomial family of wall1_hermite_caps.md.

The exact certificate minimizes the unextended-ball objective on the *continuous*
interval [0,1/2], for both parities and 1 <= m <= 59 (the repository search).
Then it optimizes the 160-bin signed-slice certificate on the 1e-7 threshold
grid and 0.001-nat enlargement grid, retaining the original axial cutoff 0.02.
Finally it excludes 4.09 for the full lens, allowing the radius to vary
continuously up to separation one. No signed-slice estimates enter that test.

For the ansatz q_j=h_j(1+a P_j(t)+c(-1)^j), truncation coincides with
the zeros at m (and m+1 for parity one). The Gegenbauer recurrence gives
v_j/h_j=2^e(1-t) for j<m, where v=(1+x)^e(x-t)q. Hence the constant
coefficient of qv is 2^e(1-t) sum(q_j), and the LP ratio B is sum(q_j).
"""
from fractions import Fraction as Q
from math import comb, factorial
from mpmath import mp, iv

MAX_M = 59
SCALE = 1 << 100


def multiplicity(j):
    return comb(23+j, j) - (comb(21+j, j-2) if j >= 2 else 0)


def bernstein_basis():
    """Enclose every Bernstein coefficient of P_j on [0,1/2] in fixed point."""
    prev, cur = [Q(1)], [Q(0), Q(1, 2)]
    polys = [prev, cur]
    for j in range(1, MAX_M+1):
        # Represent x P_j and twice degree-elevated P_{j-1} in degree j+1.
        elevated = prev
        for k in (j, j+1):
            left, right = [0]+elevated, elevated+[0]
            elevated = [(i*left[i]+(k-i)*right[i])/k for i in range(k+1)]
        nxt = [((2*j+22)*Q(i, 2*(j+1))*([0]+cur)[i]-j*elevated[i])/(j+22)
               for i in range(j+2)]
        prev, cur = cur, nxt
        polys.append(cur)
    return [([int(v*SCALE//1) for v in p], [-int(-v*SCALE//1) for v in p]) for p in polys]


def halves(bounds):
    """Outward de Casteljau subdivision at one half."""
    lo, hi = bounds
    left_lo, left_hi, right_lo, right_hi = [], [], [], []
    while lo:
        left_lo.append(lo[0])
        left_hi.append(hi[0])
        right_lo.append(lo[-1])
        right_hi.append(hi[-1])
        lo = [(x+y)//2 for x, y in zip(lo, lo[1:])]
        hi = [(x+y+1)//2 for x, y in zip(hi, hi[1:])]
    return (left_lo, left_hi), (right_lo[::-1], right_hi[::-1])


def exclude_other_branches():
    """Every branch except (2,0) is infeasible or has unextended cap > 4.55."""
    limit = (Q(455, 100)*Q(355, 113))**12 / factorial(12)
    pairs = [(m, e) for m in range(1, MAX_M+1) for e in (0, 1) if (m, e) != (2, 0)]

    def exceeds_limit(m, e, a, b, lo, hi, denominator_upper):
        numerator_lower = sum(multiplicity(j)*lo[j] for j in range(m))
        return numerator_lower*(2*(1-b))**12 > denominator_upper*limit

    return subdivisions(pairs, exceeds_limit)


def subdivisions(pairs, excluded):
    """Bisect until coefficient signs or the supplied bound exclude each branch."""
    def check(a, b, polys, active):
        lo, hi = zip(*[(min(l), max(h)) for l, h in polys])
        undecided = []
        for m, e in active:
            # Divide the following numerators by den to get q_j / h_j.
            dl, dh = -hi[m], -lo[m]
            if e:
                dl, dh = dl-hi[m+1], dh-lo[m+1]
            if dh <= 0:
                continue
            lows, highs = [], []
            for j in range(m):
                if e:
                    k = m+(m-j)%2
                    l, h = 2*(lo[j]-hi[k]), 2*(hi[j]-lo[k])
                else:
                    l, h = dl+lo[j], dh+hi[j]
                if h < 0:
                    break
                lows.append(max(0,l))
                highs.append(h)
            else:
                if not excluded(m,e,a,b,lows,highs,dh):
                    undecided.append((m,e))
        if not undecided:
            return 1
        assert b-a > Q(1, 2**40), (a,b,undecided)
        mid = (a+b)/2
        needed = max(m+e for m,e in undecided)+1
        left, right = zip(*(halves(p) for p in polys[:needed]))
        return check(a,mid,left,undecided)+check(mid,b,right,undecided)

    return check(Q(0),Q(1,2),bernstein_basis(),pairs)


def unextended():
    # B = 24(1-t)(25t+2)/(1-24t^2). The derivative of B(1-t)^12
    # has the sign of this cubic, which has just one positive root (Descartes).
    p = lambda t: 7200*t**3+1128*t*t-254*t-1
    a, b = Q(12782306436390958,10**17), Q(12782306436390960,10**17)
    assert p(a) < 0 < p(b)
    # At this t, P_2(t)<0, q0,q1>0, v0=q1/24-t*q0>0,
    # v1=q0-t*q1>0, v2=23*q1/24>0.
    assert b < Q(1,6)
    mp.dps = 40
    t = mp.findroot(p, .13)
    B = 24*(1-t)*(25*t+2)/(1-24*t*t)
    gamma = (factorial(12)*B)**(mp.mpf(1)/12)*2*(1-t)/mp.pi
    print("exact winning threshold: positive root of 7200t³+1128t²−254t−1")
    print("unextended cap", gamma, "optimistic one-nat cap", gamma/mp.exp(mp.mpf(1)/12))
    print("other branches excluded by Bernstein subdivision:", exclude_other_branches(), "leaves")


def enlarged():
    # E is the factor on squared radius. The repository axial test implies
    # E < A(t), where A is the positive root obtained by equating the angle
    # at squared distances U and U-.04 to t. In particular A(t) <= 1.04.
    # Thus the certified 4.55 exclusion above covers every other branch.
    assert Q(455,100)/Q(104,100) > Q(437201,100000)
    iv.dps = 45
    R = iv.mpf
    grid = 10**7
    winner, gain = 1245798, 412
    factors = [iv.exp(R(k)/12000) for k in range(1000)]

    def t_of(i):
        return R(i)/grid

    def ratio(t):
        return 24*(1-t)*(25*t+2)/(1-24*t*t)

    def aperture(t):
        c = R(1)/25
        return 1+c*(1-t)-c*c*t*(1-t)/(1+iv.sqrt(1-c*c*(1-t*t)))

    def objective(t, k):
        return ratio(t)*(2*(1-t)/factors[k])**12

    t = t_of(winner)
    E = factors[gain]
    optimum = objective(t,gain)
    assert E < aperture(t)
    # Verify the 160 log-radius bins at the winning threshold. At n=24
    # the old assertion xmin>0 fails. On an interval crossing zero the
    # maximum of 1-x^2 is 1 and its minimum uses the larger endpoint square.
    S = 1/(2*(1-t))
    U = E*S
    xmax = 1-1/(2*U)
    xmin = xmax-R(5)/23
    Y = (S-R(".52")**2)*iv.exp(-R(10)/23)
    assert -1 < xmin < 0 < xmax and Y > 0 and U < 1
    low = (1-max(xmin**2,xmax**2))/iv.sqrt(1+R(".04")**2/Y)
    assert xmax-t-low*5/23 < 0
    a = 23/(1-24*t*t)
    q0, q1 = 1+a, 24*(1+a*t)
    assert min(q0,q1,q1/24-t*q0,q0-t*q1,23*q1/24) > 0
    slope = q1/(q0+t*q1)
    total = R(0)
    for j in range(160):
        l, r = R(j)/32, R(j+1)/32
        X = R([(xmax-t-r/23).a, (xmax-t-low*l/23).b])
        total += (iv.exp(-l)-iv.exp(-r))*X*(1+slope*X)**2
    assert total < 0

    def prove(first, last):
        if first > last:
            return
        # Split at the pole of B before interval division.
        lo, hi = t_of(first), t_of(last)
        if 24*lo**2 >= 1:
            return
        if 24*hi**2 < 1:
            T = R([lo.a,hi.b])
            A = aperture(T)
            left, right = 0, len(factors)
            while right-left > 1:
                mid = (left+right)//2
                if factors[mid].a > A.b:
                    right = mid
                else:
                    left = mid
            if objective(T,left).a > optimum.b:
                return
            if first == last == winner:
                assert left == gain
                return
        assert first < last, (first,last)
        mid = (first+last)//2
        prove(first,mid)
        prove(mid+1,last)

    prove(0,grid//2)
    gamma = (optimum*factorial(12))**(R(1)/12)/iv.pi
    assert gamma < R("4.37201")
    print("signed-slice grid optimum: t=1245798/10^7, g=412/1000")
    print("Hermite coefficient",gamma,"signed quadrature upper endpoint",total.b)


def full_lens_obstruction():
    """Prove the *integrated* lens fails at some displacement if gamma <= 4.09.

    Use integer boxes on one half of the lens. At radius R in separation-one
    coordinates let h=(R-1/2)u and y=sqrt(Y)v, where Y=R²-(1/2+h)².
    The positive weight is Y^(23/2) v^22 du dv, up to a constant. The angle
    cosine (z-ab)/sqrt((z-ab)²+z), z=y², a=1/2+h, b=1/2-h, increases
    in both z and h separately (for z>0, ab>0). Rounding the resulting
    endpoint values outwards covers each entire rectangle.
    """
    from functools import lru_cache
    from math import isqrt
    bins = 64
    needed = [(Q(409,100)*Q(355,113)*(Q(k,512)**2))**12/factorial(12)
              for k in range(513)]

    @lru_cache(maxsize=16)
    def basis(k, m, n):
        # All squared distances in angle() have denominator D.
        half = 256*n
        D = (512*n*n)**2
        def angle(z,ab):
            t = z-ab*n*n
            d = t*t+z*D
            value = isqrt((t*t*SCALE*SCALE)//d)
            return (value,value+1) if t >= 0 else (-value-1,-value)
        out = []
        for i in range(n):
            hl, hh = (k-256)*i, (k-256)*(i+1)
            yl = (k*n)**2-(half+hh)**2
            yh = (k*n)**2-(half+hl)**2
            wl, wh = isqrt(yl**23*SCALE**2), isqrt(yh**23*SCALE**2)+1
            for j in range(n):
                weight = (j+1)**23-j**23
                xl = max(-SCALE,angle(yl*j*j,half**2-hl**2)[0])
                xh = min(SCALE,angle(yh*(j+1)**2,half**2-hh**2)[1])
                P = [(SCALE,SCALE),(xl,xh)]
                for d in range(1,m-1):
                    pl, ph = P[-1]
                    products = (xl*pl,xh*pl,xl*ph,xh*ph)
                    denom = (d+22)*SCALE
                    P.append((((2*d+22)*min(products)-d*P[-2][1]*SCALE)//denom,
                              -((-(2*d+22)*max(products)+d*P[-2][0]*SCALE)//denom)))
                out.append((wl*weight, wh*weight, xl, xh, P[:m]))
        return out

    def impossible(m,e,a,b,lo,hi,dh):
        from bisect import bisect_right
        lower = [multiplicity(j)*lo[j] for j in range(m)]
        B = Q(sum(lower),dh)
        if B > needed[-1]:
            return True   # The method assumes radius < separation.
        k = bisect_right(needed,B)-1
        if m > 7 or b-a > Q(1,128) or k <= 256:
            return False
        upper = [multiplicity(j)*hi[j] for j in range(m)]
        n = bins if b-a > Q(1,1024) else 2*bins
        total = 0
        for wl,wh,xl,xh,P in basis(min(k,511),m,n):
            # Denominator-free q: all omitted scale factors are positive.
            ql = sum(pl*(h if pl < 0 else l) for (pl,_),l,h in zip(P,lower,upper))
            qh = sum(ph*(l if ph < 0 else h) for (_,ph),l,h in zip(P,lower,upper))
            coefficient = xl + int((-b*SCALE)//1)
            if coefficient < 0:
                factor = max(ql*ql,qh*qh)
                if e:
                    factor *= SCALE+xh
            else:
                factor = max(0,ql,-qh)**2
                if e:
                    factor *= SCALE+xl
            total += (wh if coefficient < 0 else wl)*coefficient*factor
        return total > 0

    pairs = [(m,e) for m in range(1,MAX_M+1) for e in (0,1)]
    leaves = subdivisions(pairs,impossible)
    print("4.09 excluded by full signed lens or required radius >= 1:",leaves,"leaves")


if __name__ == "__main__":
    unextended()
    enlarged()
    full_lens_obstruction()
