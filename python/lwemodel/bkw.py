"""Coded-BKW (lwe_bkw.py), GJS15 coding noise and the estimator's nested local search.

The test dimension uses Brent interpolation and an integer scan. The
success correction uses the five-term Abramowitz–Stegun erf approximation.
"""
from math import comb
from . import fx as F
from .num_misc import local, width


def erf(x):
    if x >= 7*F.ONE:
        return F.ONE
    t = F.div(F.ONE,F.ONE+F.mul(F.of_rat(3275911,10**7),x))
    a = 0
    for c in (1061405429,-1453152027,1421413741,-284496736,254829592):
        a = F.mul(t,a+F.of_rat(c,10**9))
    return F.ONE-F.mul(a,F.exp(-F.mul(x,x)))


def candidate(p, se, b, steps, lq):
    def code(i,x):
        return (2*b*lq*x)//(2*(b-1)*lq*F.ONE+i*x*F.ONE)
    def test(t1,t2):
        rem = p.n-t1*b
        if rem <= 0:
            return 0
        def residual(x):
            return (rem-sum(code(i,x) for i in range(1,t2+1)))*F.ONE-x
        a,bx = 2*F.ONE,(rem+1)*F.ONE
        fa,fb = residual(a),residual(bx)
        start = 2
        if fa >= 0 >= fb:
            block,fc,old,step = a,fa,bx-a,bx-a
            for _ in range(100):
                if fa*fb < 0:
                    block,fc,old,step = a,fa,bx-a,bx-a
                if abs(fc)<abs(fb):
                    a,bx,block,fa,fb,fc = bx,block,bx,fb,fc,fb
                tol = (bx//10+281)//2
                half = (block-bx)//2
                if fb == 0 or abs(half)<tol:
                    break
                trial = None
                if abs(old)>tol and abs(fb)<abs(fa):
                    if a == block:
                        trial = -fb*(bx-a)//(fb-fa)
                    else:
                        # Inverse quadratic interpolation of the zero.
                        trial = ((a-bx)*fb*fc//((fa-fb)*(fa-fc))
                                 + (block-bx)*fa*fb//((fc-fa)*(fc-fb)))
                if trial is not None and 2*abs(trial)<min(abs(old),3*abs(half)-tol):
                    old,step = step,trial
                else:
                    old,step = half,half
                a,fa = bx,fb
                bx += step if abs(step)>tol else (tol if half>0 else -tol)
                fb = residual(bx)
            start = max(2,F.floor(bx+F.ONE//2)-1)
        best = 1
        for v in range(start,rem+1):
            if abs(residual(v*F.ONE)) >= abs(residual(best*F.ONE)):
                break
            best = v
        return best
    x = test(0,steps)
    t1 = min(p.n//b,sum(code(i,x*F.ONE)<=b for i in range(1,steps+1)))
    t2 = steps-t1
    x = test(t1,t2)
    if not x:
        return None
    codes = [code(i,x*F.ONE) for i in range(1,t2+1)]
    ntot = sum(codes)+x
    top = max(0,p.n-ntot-t1*b)
    # Compute the variance divided by q^2 before exponentiation.
    noise = ((1<<steps)*F.mul(se,se))//(p.q*p.q)
    quant = F.mul(F.mul(p.Xs.stddev,p.Xs.stddev),F.exp2(-2*(b-1)*lq//x))*ntot//12
    u = F.mul(4*F.mul(F.PI,F.PI),noise+quant)
    if u > 1020*F.LN2:
        return None
    if u <= -2*F.ln(F.of_rat(99,100)):
        M = 1
    else:
        # Upstream amplify subtracts advantage squared from one in an MPFR
        # field selected from the advantage exponent. Preserve that rounding.
        exponent = F.mul(u,F.LOG2E)
        prec = max(53,2*F.ceil(exponent//2))
        mant = F.floor(F.exp2(prec*F.ONE-exponent)+F.ONE//2)
        if exponent > 25*F.ONE:
            M = F.ceil((-2*F.ln(F.of_rat(1,50)) << prec)//mant)
        else:
            M = F.ceil(F.div(2*F.ln(F.of_rat(1,50)),F.ln(F.ONE-F.exp(-u))))
    table = p.q**b
    half = (table-1)*F.ONE//2
    samples = steps*half + F.of_int(M)
    n = p.n-t1*b
    C = (samples-F.of_int(n))*(p.n+1)*((n+b-2)//(b-1)) if p.Xs.stddev>se else 0
    for i in range(1,t1+1):
        C += (p.n+1-i*b)*(samples-i*half)
    prefix = top+x
    for i,v in enumerate(codes,1):
        prefix += v
        C += 4*(F.of_int(M)+i*half)*v + prefix*(F.of_int(M)+(i-1)*half)
    z = width(p.Xs)
    if p.Xs.is_gaussian_like:
        z = min(z,6*p.Xs.stddev+F.ONE)
    guesses = (2*z+F.ONE)**top // F.ONE**max(0,top-1) if top else F.ONE
    C += guesses*M*top + F.of_int(4*M*x) + F.mul(guesses,table*(b*lq+F.ONE))
    bits = F.log2(C)-top*F.log2(erf(F.div(z,F.sqrt(2*se)))) if top and se else F.log2(C)
    if bits >= 1024*F.ONE:
        return None
    # Upstream stores sample counts in a binary64 field before amplifying.
    shift = max(0,samples.bit_length()-53)
    units,r = divmod(samples,1<<shift)
    rounded = (units + (2*r > 1<<shift or (2*r == 1<<shift and units%2))) << shift
    return bits,F.ceil(rounded)


def huge_modulus_infinite(p):
    """`Bkw.cost_eq_none`: at `q = 2^e`, `e >= 1024`, every candidate pays for a table of `q^b`
    entries and exceeds the 2^1024 cap (no need to evaluate it)."""
    q = p.q
    if q <= 0 or q & (q - 1) or q.bit_length() - 1 < 1024:
        return False
    if p.Xs.stddev > p.Xe.stddev:
        return False
    z = width(p.Xs)
    if p.Xs.is_gaussian_like:
        z = min(z, 6*p.Xs.stddev+F.ONE)
    return z >= 0 and erf(F.div(z, F.sqrt(2*p.Xe.stddev))) == F.ONE


def cost(params):
    p = params.normalize()
    if huge_modulus_infinite(p):
        return None
    se,m = p.Xe.stddev,p.m
    lq = F.log2_nat(p.q)
    while True:
        def smaller(a,b):
            if a is None:
                return b is None
            return b is None or (a[0]<=b[0] and not (m is not None and b[1]<=m<a[1]))
        def outer(b):
            return local(2,max(3,p.n//b),lambda t:candidate(p,se,b,t,lq),smaller)
        result = local(2,3*F.ceil(lq),outer,smaller)
        if result is None:
            return None
        bits,required = result
        if m is None or required <= m:
            return bits
        if p.Xe.mean or not p.m:
            return None
        k = next((k for k in range(required.bit_length()) if comb(p.m,k)*2**k-1>=required),None)
        if k is None:
            return None
        m,se = required,F.mul(F.sqrt(F.of_int(k)),p.Xe.stddev)


coded_bkw = cost
