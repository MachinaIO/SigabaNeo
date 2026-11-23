"""Actual H10/c6 frontier: optimize the already selected D32 weighted kernel."""
from fractions import Fraction as F
from math import comb

OLD=F(11,12)
NEW=F(921,1000)

def geometry_checks():
    def product(w):
        z=(10-2*w)/8
        determinant=16/(w*z)+16/(z*z)
        return w*w*z**8*determinant
    assert product(NEW)>product(OLD)>32
    # d(log(product))/dw has the sign of z^2+w*z/4-3*w^2/2.
    for w in (OLD,NEW,F(922,1000)):
        z=(10-2*w)/8
        derivative=z*z+w*z/4-3*w*w/2
        print('weight',w,'exclusive',z,'weighted product',float(product(w)),
              'derivative sign',(derivative>0)-(derivative<0))


def kernels(s):
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    beta=I(8*n)/(20*R**2);a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=s['geometry']['theta_upper']
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    def scalar(f):return I(f.numerator)/f.denominator
    def kernel(weight):
        w=scalar(weight);z=(10-2*w)/8
        first=2/w+4/z
        second=(16/(w*z)+16/z**2)/first
        scaled=alpha/z;scaled_a=a/z
        delta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
        periodic=sum((comb(10,j)*delta**j for j in range(1,11)),I(0))
        tail=iv.exp(-648*scaled)*theta(I(5)*scaled/2)**2
        return (iv.pi/beta)**5/(w*z**4)*(
            (theta(first*alpha)*theta(second*alpha)+tail)/q**2+periodic)
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(10,j)*delta**j for j in range(1,11)),I(0))
    tail=iv.exp(-648*alpha)*theta(I(5)*alpha/2)**2
    def plain(det):
        return (iv.pi/beta)**5*((theta(6*alpha)*theta(I(det)*alpha/6)+tail)/q**2+periodic)
    return kernel(OLD),kernel(NEW),plain


def diagnostic():
    import contextlib,io
    from wall1_general_two_relations import draw14_bounds
    from wall1_high_order_frontier import _capture_copy
    states={}
    wrapped=_capture_copy(draw14_bounds,lambda value,state:states.update(state))
    with contextlib.redirect_stdout(io.StringIO()):
        s,_,strata=wrapped(exclude_nine_twenty_seven=True)
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    old,new,plain=kernels(s)
    old=min((old,plain(32)),key=lambda x:x.b)
    new=min((new,old),key=lambda x:x.b)
    print('weighted D32 N-power new/old log10',iv.log10((new/old)**n))
    anchors=states['anchors'];ratios={}
    for o in (2,4):
        p=s['six_circuit_split_parts'][4,o];Q=q**(6+o)
        oldtwo=I(52)/Q*old**n+(I(48)/Q*plain(36)**n if o==2 else 0)
        newtwo=I(52)/Q*new**n+(I(48)/Q*plain(36)**n if o==2 else 0)
        tolerance=I('1e-60')
        assert (oldtwo/p['two-six']).a>(1-tolerance).b
        assert (oldtwo/p['two-six']).b<(1+tolerance).a
        candidate=p['one-six']+newtwo+p['no-six']
        selected=min((p['selected'],candidate),key=lambda x:x.b)
        beta=I(8*n)/(20*R**2)
        actual=anchors[6,4,o]*q**(s['m']*8)/iv.exp(10*beta*R**2)
        assert (actual/p['selected']).a>(1-tolerance).b
        assert (actual/p['selected']).b<(1+tolerance).a
        ratios[4,o]=selected/actual
        print('overlap',o,'branch shares log10',
              {k:str(iv.log10(p[k]/actual)) for k in ('one-six','two-six','no-six')})
        print('overlap',o,'actual selected new/old log10',iv.log10(ratios[4,o]))
    h,r,c=19,10,6;M=states['completions'][r];mu=s['mu']
    terms={}
    for t in range(2,7):
        for o in range(1,6):
            if t+o<c:continue
            choices=comb(h,c)*comb(h-c,t)*comb(c,o)*comb(h-c-t,r-c-t+2)
            terms[t,o]=choices*q**(c+t+o-4)*anchors[c,t,o]*mu**(r-c-t+2)*M**(h-r-2)/(r-c-t+3)
    oldtwo=sum(terms.values(),I(0))
    newtwo=sum((v*ratios.get(k,I(1)) for k,v in terms.items()),I(0))
    one=comb(h,c)*comb(h-c,r-c+1)*s['epsilon'][c]*mu**(r-c+1)*M**(h-r-1)/(r-c+2)
    oldselected=min((one,oldtwo),key=lambda x:x.b)
    newselected=min((one,newtwo),key=lambda x:x.b)
    assert (oldselected/strata[h,r,c]).a>I('0.999999999999').b
    assert (oldselected/strata[h,r,c]).b<I('1.000000000001').a
    print('size19 rank10c6 restricted residual new/old log10',iv.log10(newselected/oldselected))

if __name__=='__main__':
    geometry_checks()
    diagnostic()
