"""Finite geometry certificates only. Python 3 + mpmath, no reduction or CVP runs."""
from functools import cache
from itertools import accumulate, islice
from math import isqrt

from mpmath import iv

iv.dps = 45
I = iv.mpf
Q, N, MAX = 3329, 511, 1023
SCALE = 10**9
RATES = (50, 1)  # per cent
LOG_Q = iv.ln(Q)


def down(x):
    # Give away two grid units, then independently verify the direction.
    ans = int(float(x.a) * SCALE) - 2
    assert I(ans) <= x * SCALE
    return ans


def up(x):
    return -down(-x)


def cap_costs():
    sharp = {2: I(4)/3, 3: I(2), 4: I(4), 5: I(8), 6: I(64)/3,
             7: I(64), 8: I(256)}
    special = {506: '56.21420', 510: '56.79788', 520: '57.84689',
               530: '58.89576', 550: '60.99269'}
    costs = [0, 0]
    last = None
    for h in range(2, MAX+1):
        options = [iv.ln(2/iv.pi) + 2*iv.loggamma(2+I(h)/2)/h]
        if last is not None:
            options.append(last * (h-1)/(h-2))
        if h in sharp:
            options.append(iv.ln(sharp[h])/h)
        if h in special:
            options.append(iv.ln(I(special[h])))
        last = min(options, key=lambda x: float(x.b))
        costs.append(up(h*last/2))
    return costs


C = cap_costs()


@cache
def envelope(width):
    # P bounds log(g_i/g_{i+j}). H gives the sum over pairs within an interval.
    p, sums, hsum = [0], [0, 0], [0, 0]
    for j in range(1, MAX):
        p.append(min((C[h] + sums[j]-sums[j-h+1]+h-2)//(h-1)
                     for h in range(2, min(j+1, width)+1)))
        sums.append(sums[-1]+p[-1])
        hsum.append(hsum[-1]+sums[-1])
    return p, hsum


def raw(d, exponent):
    # Probability <= 1/200 for each raw exit. Distances for the scaled dual.
    t = iv.pi*iv.exp(1-2*exponent*LOG_Q/d)
    z = iv.exp(-iv.pi**2/t)
    log_h = iv.ln(iv.pi/t)/2 + iv.log1p(2*z/(1-z))
    r2 = (exponent*LOG_Q - iv.ln(100) - d*log_h)/t
    if r2.a <= 1:
        return 0  # integer lattice minimum >= 1, deterministically
    return min(down(iv.ln(r2)/2), down(iv.ln(Q-1)))


def energies(d, limit):
    # [z^j](10+15z+6z^4+z^9)^d from the logarithmic derivative.
    w = [10**d]
    for j in range(1, limit+1):
        total = sum(c*((d+1)*v-j)*w[j-v] for v, c in ((1,15),(4,6),(9,1)) if j >= v)
        a, rem = divmod(total, 10*j)
        assert rem == 0 and a >= 0
        w.append(a)
    return w


@cache
def design(m):
    d = N+m
    r, a = raw(d, m), raw(d, N)-up(LOG_Q)
    w = energies(d, 2*d)
    thresholds = {}
    mass = 32**d
    for percent in RATES:
        j = next(j for j, s in enumerate(accumulate(w)) if 99*s >= percent*mass)
        thresholds[percent] = up(iv.ln(4*j)/2)
    return r, a, thresholds


def ceildiv(x,y):
    return -((-x)//y)


def profile(m, width):
    d = N+m
    r, a, _ = design(m)
    det_lo, det_hi = down(m*LOG_Q), up(m*LOG_Q)
    p, hsum = envelope(width)
    log_q_floor = down(LOG_Q)
    for i in range(d):
        j, c = i+1, d-i-1
        det_floor = max(j*r-C[j], det_lo+c*a-C[c], max(0,j-N)*log_q_floor)
        # Sum log g_h - log g_t over all h<i<=t.
        cutoff = ceildiv(i*det_hi + hsum[d]-hsum[i]-hsum[d-i], d)
        yield max(r-p[i], det_floor-cutoff)


@cache
def projected(b, percent):
    u = I(percent)/99 + I(1)/500
    energy = 3*I(b)/2 + iv.sqrt(9*I(b)*u/(2*(1-u)))
    return up(iv.ln(4*energy)/2)


def scan(width, samples=range(1,513)):
    best = {(p,nonempty): (MAX+1,None) for p in RATES for nonempty in (False,True)}
    for m in samples:
        d = N+m
        prefix = 10**20
        strip = up(iv.ln(12*iv.ln(1000*d))/2)
        for i, g in enumerate(profile(m,width)):
            b = d-i
            if b <= width:
                for p in RATES:
                    radial = min(prefix,g) > design(m)[2][p]
                    separate = prefix > strip and g > projected(b,p)
                    if radial or separate:
                        for nonempty in ([False,True] if i else [False]):
                            if b < best[p,nonempty][0]:
                                best[p,nonempty] = b,m
            prefix = min(prefix,g)
    return best


def shells(d, limit):
    # [z^j](1+2z+2z^4+...)^d, same logarithmic-derivative identity.
    squares = [i*i for i in range(1,isqrt(limit)+1)]
    a = [1]
    for j in range(1,limit+1):
        total = 0
        for v in squares:
            if v > j:
                break
            total += ((d+1)*v-j)*a[j-v]
        value, rem = divmod(2*total,j)
        assert rem == 0 and value >= 0
        a.append(value)
    return accumulate(a)


def ball_counts(d, factor, limit):
    if factor == 16:
        # First-line Hermite loss squared is 4/3; diameter squared is 16J/3.
        populations = list(shells(d,16*limit//3))
        return (populations[16*j//3] for j in range(limit+1))
    return islice(shells(d,factor*limit),0,None,factor)


def run_work(d, last, factor):
    if factor == 16:
        return 64*d*d*(Q*Q*(4*Q+1)**d+(2*Q+1)**d)
    return 64*d*d*list(shells(N,last))[-1]


def ball_gain(d, samples, factor, limit=1650):
    # factor 4 tests the diameter (signed pairs), factor 1 the translated ball.
    # d and samples are separate to allow monotone bounds on a range of designs.
    den = (1 if factor == 1 else 2)*Q**samples
    w = energies(d,limit)
    gain = 0
    for j,pop in enumerate(ball_counts(d,factor,limit)):
        if pop-1 >= den:
            return gain,den*32**d,j-1
        gain += w[j]*(den+1-pop)
    raise ArithmeticError('increase energy cutoff')


def ball_first(factor, upper):
    # For all l<=m<=h, the expression at dimension N+l and denominator Q^h
    # dominates the expression for m, by padding integer points and CBD samples.
    found = {}
    for lo in range(1,upper+1,10):
        hi = min(lo+9,upper)
        num,den,_ = ball_gain(N+lo,hi,factor)
        if all(p in found or 100*num < p*den for p in RATES):
            continue
        for m in range(lo,hi+1):
            num,den,last = ball_gain(N+m,m,factor)
            for p in RATES:
                if p not in found and 100*num >= p*den:
                    prev,prevden,_ = ball_gain(N+m-1,m-1,factor)
                    cost = run_work(N+m,last,factor).bit_length()
                    print('factor, percent, width, m, previous, current, cutoff, cost bits',
                          factor,p,N+m-(factor == 16),m,prev/prevden,num/den,last,cost)
                    found[p] = m
            if len(found) == len(RATES):
                return
    raise ArithmeticError('no crossing')


def split_bounds(m, factor, last):
    from fractions import Fraction
    d = N+m
    h = Q**m*(1 if factor == 1 else 2)
    credit = [h+1-pop for pop in ball_counts(d,factor,last)]
    errors = energies(m,min(9*m,last))
    secrets = energies(N,last)
    # Positive polynomial product computes each conditional convolution exactly.
    # Each coefficient is <= h*32^m, so these radix digits cannot carry.
    step = (h*32**m).bit_length()//8+1
    def packed(seq):
        return int.from_bytes(b''.join(x.to_bytes(step,'little') for x in seq),'little')
    prod = packed(credit[::-1])*packed(errors)
    digits = prod.to_bytes(step*(len(credit)+len(errors)),'little')
    grid = 10**9
    floors = []
    for t in range(last+1):
        j = last-t
        v = int.from_bytes(digits[step*j:step*(j+1)],'little')
        floors.append(grid*v//(h*32**m))
    results = []
    per = run_work(d,last,factor)
    for r in range(1,512//m+1):
        held = 512-r*m
        if r > 1 and held == 0:
            continue
        gain = sum(s*(grid**r-(grid-f)**r) for s,f in zip(secrets,floors))
        bound = Fraction(gain,32**N*grid**r)
        if r > 1:
            bound -= r*Fraction(7,Q)**held
        operations = r*(per + 64*(1+held)*d)
        results.append((bound,r,held,operations.bit_length()))
    return max(results)


def split_first(factor,upper):
    found = set()
    for lo in range(1,upper+1,10):
        hi = min(lo+9,upper)
        num,den,_ = ball_gain(N+lo,hi,factor)
        if all(p in found or (512//lo)*100*num < p*den for p in RATES):
            continue
        for m in range(lo,hi+1):
            num,den,last = ball_gain(N+m,m,factor)
            if all(p in found or (512//m)*100*num < p*den for p in RATES):
                continue
            bound,r,held,bits = split_bounds(m,factor,last)
            for p in RATES:
                if p not in found and 100*bound >= p:
                    print('split factor, target, width, m, runs, validation, bound, cost bits',
                          factor,p,N+m-(factor == 16),m,r,held,float(bound),bits)
                    found.add(p)
            if len(found) == len(RATES):
                return
    raise ArithmeticError('no split crossing')


def main():
    # Width MAX relaxes all inequalities for every smaller width. Recheck each winner.
    best = scan(MAX)
    print('half-minimum (percent, require nonempty prefix): (width, samples)', best)
    for (p,nonempty),(b,m) in best.items():
        assert scan(b,[m])[p,nonempty] == (b,m)
        r,a,_ = design(m)
        print(p, nonempty, b, m, 'floor, dual, terminal',
              *(float(iv.exp(I(x)/SCALE).a) for x in (r,a,list(profile(m,b))[N+m-b])))
    for width in (506,999,1000,1023):
        g = list(profile(512,width))[MAX-width]
        print('full sample',width,'terminal floor',float(iv.exp(I(g)/SCALE).a))
    print('512 sample crossings', scan(MAX,[512]))
    at_506 = max((list(profile(m,506))[N+m-506],m) for m in range(1,513))
    print('best 506 floor and sample count',float(iv.exp(I(at_506[0])/SCALE).b),at_506[1])
    for d in (735,727):
        box_work = 64*d*d*(Q*Q*(4*Q+1)**d + (2*Q+1)**d)
        print('one-line reduction finite work exponent',d-1,box_work.bit_length())
    ball_first(1,135)
    ball_first(4,205)
    split_first(1,135)
    split_first(4,205)
    ball_first(16,225)
    split_first(16,225)


if __name__ == '__main__':
    main()
