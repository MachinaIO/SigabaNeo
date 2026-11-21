"""Fixed-point approximations for the GSA projection and Babai probabilities."""
from functools import lru_cache
from . import fx as f

O = f.ONE
COEF = [f.of_rat(x, 10**9) for x in
        (1061405429, -1453152027, 1421413741, -284496736, 254829592)]


def erf(x):
    """Abramowitz-Stegun 7.1.26."""
    if x >= 8 * O:
        return O
    t = f.div(O, O + f.mul(f.of_rat(3275911, 10**7), x))
    a = 0
    for c in COEF:
        a = f.mul(a + c, t)
    return O - f.mul(a, f.exp(-f.mul(x, x)))


@lru_cache(None)
def threshold(k):
    # (log(volume of unit (k+1)-ball) + (k+1)/2 log(k+1))/k.
    # Stirling expansion of log Gamma(1+x), shifted past x=8.
    n = k + 1
    x = n * O // 2
    acc = 0
    while x < 8*O:
        x += O
        acc += f.log2(x)
    corr = f.div(O, 12*x) - f.div(O, 360*f.mul(x, f.mul(x,x)))
    gamma = (f.mul(x+O//2, f.log2(x)) - f.mul(x, f.LOG2E)
             + f.log2(f.SQRT2PI) + f.mul(corr, f.LOG2E) - acc)
    return ((f.log2(f.PI) + f.log2_nat(n))*n//2 - gamma)//k


def repetitions(lp):
    if lp >= f.log2(f.of_rat(99,100)):
        return 0
    if lp < -20*O:
        return f.log2(f.ln(100*O)) - lp
    return f.log2_nat(f.ceil(f.div(-f.ln(100*O), f.ln(O-f.exp2(lp)))))


def profile(k, first, step, mitm):
    """Composite midpoint quadrature of the log product, with finite-sphere correction."""
    if not k:
        return 0
    total = 0
    i = 0
    while i < k:
        width = min(k-i, max(1, O//(16*step)))
        l = first - step*i - step*(width-1)//2
        if l < (48 if mitm else 4)*O:
            x = f.exp2(l)
            if mitm:
                y = f.mul(x, f.of_rat(707106781,10**9))
                if y >= 8 * O:
                    v = O - f.div(O, f.mul(y, f.sqrt(f.PI)))
                elif y < O // 1024:
                    v = f.div(y, f.sqrt(f.PI))
                else:
                    v = erf(y) - f.div(O - f.exp(-f.mul(y, y)), f.mul(y, f.sqrt(f.PI)))
            else:
                # x is length/sigma. Coordinate radius is half this value.
                t = x//2
                if f.mul(t,t) >= k*O or t >= 9*O:
                    v = O
                else:
                    t2 = f.mul(t,t)
                    phi = f.div(f.exp(-t2//2),f.SQRT2PI)
                    v = erf(f.div(t,f.sqrt(2*O))) + f.mul(f.mul(t,t2-3*O),phi)//(2*k)
            total += width*f.log2(max(1,min(O,v)))
        i += width
    return total


def minimize(lo, hi, fn):
    """Eight-way grid followed by successive local fourfold refinements; include boundaries."""
    best, value = hi, None
    left, right = lo, hi
    while left <= right:
        stride = max(1,(right-left+7)//8)
        for i in [right,*range(left,right,stride)]:
            v = fn(i)
            if v is not None and (value is None or v < value):
                best,value = i,v
        if stride == 1:
            break
        left,right=max(lo,best-stride),min(hi,best+stride)
    return best,value


def local_minimum(start, stop, precision, fn):
    """Estimator local_minimum with an exclusive upper bound and neighborhood refinement."""
    left = (start+precision-1)//precision
    right = stop//precision-1
    i, direction = right, -1
    best, value = i*precision, None
    seen = set()
    while (start <= i*precision < stop and i <= stop//precision-1 and i not in seen):
        seen.add(i)
        v = fn(i*precision)
        if value is None or (v is not None and v<=value):
            best,value=i*precision,v
            if abs(direction)==2:
                direction,i=-1,i-1
            elif direction==-1:
                right,direction=i,-2
                i=(left+right+1)//2
            else:
                left,direction=i,2
                i=(left+right)//2
        elif direction==-1:
            direction,i=1,i+2
        elif direction==1:
            break
        elif direction==-2:
            left=i
            i=(left+right+1)//2
        else:
            right=i
            i=(left+right)//2
    if precision>1:
        for i in range(max(start,best-precision),min(stop,best+precision)):
            v=fn(i)
            if value is None or (v is not None and v<=value):
                best,value=i,v
    return best,value
