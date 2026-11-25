"""MATZOV.Nf, Hf and Theorem 7.6 cost with the upstream nested early-abort searches."""
from . import fx, reduction as r
from .num_dual import delta, short_bits, logn


def local(f, stop):
    lo, hi = 40, stop-1
    x, direction, best, seen = hi, -1, None, set()
    while 40 <= x < stop and x not in seen:
        seen.add(x)
        v = f(x)
        improved = best is None or (v is not None and v <= best)
        if improved:
            best = v
            if abs(direction) != 1:
                direction, x = -1, x-1
            elif direction == -1:
                direction, hi = -2, x
                x = (lo+hi+1)//2
            else:
                direction, lo = 2, x
                x = (lo+hi)//2
        elif direction == -1:
            direction, x = 1, x+2
        elif direction == 1:
            break
        elif direction == -2:
            lo = x
            x = (lo+hi+1)//2
        else:
            hi = x
            x = (lo+hi)//2
    return best


def cost(params):
    p = params.normalize()
    s, e = p.Xs.stddev, p.Xe.stddev
    if min(p.n,p.q-2,s,e) <= 0:
        return None
    ls, le, lq = fx.log2(s), fx.log2(e), logn(p.q)
    alpha = fx.mul(fx.mul(fx.PI,s),fx.mul(fx.PI,s))
    minus = fx.exp(-2*alpha)
    tanh = fx.div(fx.ONE-minus,fx.ONE+minus)
    if tanh == 0:
        return None
    h = fx.LOG2E//2 + fx.log2(fx.SQRT2PI) + ls - fx.log2(tanh)
    enum = fx.ONE - fx.LOG2E//2 + fx.mul(8*fx.mul(fx.mul(alpha,minus),tanh),fx.LOG2E) + h
    den = fx.ONE-fx.exp(-fx.div(fx.ONE,2*fx.mul(s,s))) if fx.mul(s,s) else fx.ONE
    coeff = -fx.log2(den) if den else fx.ONE + 2*ls
    best = None
    best_t = 0
    for mod in range(2,p.q):
        lp = logn(mod)
        be = None
        te = 0
        for k in range(0,p.n,10):
            bt = None
            tt = 0
            for t in range(0,p.n-k,10):
                lat = p.n-k-t
                d = lat+p.n
                base = (p.n*le+lat*(ls+lq))//d-lq + fx.log2(fx.of_rat(4,3))//2
                extra = fx.mul(t*alpha//(3*mod*mod),fx.LOG2E) + fx.log2(k*h+fx.mul(t*lp,fx.LN2)+fx.LN2)
                fft = 10*fx.ONE+logn(t)+(t+1)*lp if t else None

                def candidate(b):
                    v = base+(logn(b)-r.LOG2_2PIE)//2+(d-b)*delta(b)
                    if v > 10*fx.ONE:
                        return None
                    count = fx.mul(4*fx.mul(fx.PI,fx.PI),fx.mul(fx.LOG2E,fx.exp2(2*v)))+extra
                    red = short_bits(b,d,count)
                    if red is None:
                        return None
                    table = logn(640)+count
                    guess = coeff+k*enum+(fx.log2_add(table,fft) if t else table)
                    return fx.log2_add(red,guess)

                stop = max(41,min(r.MAX_BETA,r.MAX_BETA if p.m is None else p.m-k-t))
                val = local(candidate,stop)
                if bt is not None and (val is None or val > bt):
                    break
                bt,tt = val,t
            if be is not None and (bt is None or bt > be):
                break
            be,te = bt,tt
        if best is not None and (be is None or be > best):
            break
        best,best_t = be,te
        if mod > 2 and best_t == 0:
            break
    return best
