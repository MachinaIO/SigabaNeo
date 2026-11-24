"""Sign feasibility of a quadratic Gaussian primal/dual lens majorant."""
from mpmath import iv
from fractions import Fraction as F
from math import comb


def feasible_broad_width():
    """A valid continuum majorant at another width, with an ineffective cost."""
    I=iv.mpf
    b=I(505)/2
    a=I(57)/500
    sigma=I(443)/500
    tau=I(3)/2
    coefficients=(F(-2552541,102010000),F(898692,6375625),F(43543,50500),F(1))
    B=F(505,2)
    S,T=F(443,500),F(3,2)
    radial=((F(1),),(F(1),F(-1)),
            ((B+1)/B,-2*(B+1)/B,F(1)),
            ((B+1)*(B+2)/B**2,-3*(B+1)*(B+2)/B**2,3*(B+2)/B,F(-1)))
    transformed=[F(0)]*4
    for weight,poly in zip((S*T*T,-2*S*T-T*T,S+2*T,F(-1)),radial):
        for j,c in enumerate(poly):
            transformed[j]+=weight*c
    assert tuple(transformed)==coefficients
    def polynomial(v):
        out=I(0)
        for c in reversed(coefficients):
            out=out*v+I(c.numerator)/c.denominator
        return out
    assert all(c>0 for c in coefficients[1:])
    v0=iv.pi/(a*b)
    margin=polynomial(v0)
    assert margin.a>I('.00193').b
    assert (2*iv.pi/a).b<168
    threshold=iv.sqrt(sigma*b/(iv.pi*a))
    assert threshold.b<25
    f1=2*sum((F(comb(505,j))*F(1,4)**j*F(3,4)**(505-j)
              for j in range(253,506)),F(0))
    logvol=b*iv.ln(iv.pi)-iv.loggamma(b+1)
    # Drop the positive diagonal and -P(0)/nu terms to bound the
    # value of THIS certificate from below, not the true collision ratio.
    logcost=(iv.ln(I(f1.numerator)/f1.denominator)+iv.pi/a-iv.ln(margin)
             +b*iv.ln(a)+iv.ln(sigma*tau*tau)-logvol)/iv.ln(10)
    assert logcost.a>100
    print('Feasible broad width a=57/500; boundary polynomial:',margin)
    print('Required normalized dual minimum:',threshold)
    print('Lower log10 of this certificate value, independent of mean:',logcost)
    # Production candidate ball has eta²=1-2/r_phys² after normalizing
    # the old minimum threshold to one. Use a deliberately wider interval.
    rmin=I('1.1')*I('32.18553')
    eta_min=F(999,1000)
    assert (1-2/rmin**2).a>(I(999)/1000)**2
    x=F(1,2)-1/(4*eta_min)
    assert x==F(499,1998)
    tail=2*sum((F(comb(505,j))*x**j*(1-x)**(505-j)
                for j in range(253,506)),F(0))
    # eta^-505 >=1 and the beta CDF is increasing. This is a lower
    # bound on the resulting UPPER CERTIFICATE, not on the true moment.
    logcost_eta=(iv.ln(I(tail.numerator)/tail.denominator)+iv.pi/a-iv.ln(margin)
                 +b*iv.ln(a)+iv.ln(sigma*tau*tau)-logvol)/iv.ln(10)
    assert logcost_eta.a>116
    print('Uniform lower log10 certificate for eta in [.999,1]:',logcost_eta)
    corridor_applicability(threshold)


def corridor_applicability(threshold):
    """Which existing residual corridors can supply the dual premise?"""
    I=iv.mpf
    q,n,d=3329,506,505
    c=I(11)/10
    volume=[I(1),I(2)]
    for j in range(2,910):
        volume.append(2*iv.pi*volume[j-2]/j)
    Q=iv.ln(q)
    logh=iv.ln(I('56.2142'))/2+iv.ln(volume[n])/n
    upper={406:iv.ln(I('34.807'))}
    for i in range(405,0,-1):
        period=upper[i+1]+Q/n
        hermite=(upper[i+1]+logh/n)/(I(d)/n)
        assert period.b<hermite.a or hermite.b<period.a
        upper[i]=min(period,hermite)
    possible=[]
    products=[]
    for i in range(11,406):
        N=d+i-1
        R=(iv.exp(((N-400)*Q-iv.ln(408000*volume[N]))/N)-iv.sqrt(N)/2)/q
        top=iv.exp(upper[i])
        assert top.b<(I(q)/c).a or (I(q)/c).b<top.a
        top=min(top,I(q)/c)
        product=c*top*R
        products.append((product,i))
        assert product.b<threshold.a or threshold.b<product.a
        if threshold.b<product.a:
            possible.append(i)
            print('Potential dual-floor applicability, draw',i,
                  'requires g>=',threshold/(c*R),'corridor g<',top)
    best=max(products,key=lambda entry:float(entry[0].mid))
    assert all(p.b<best[0].a for p,i in products if i!=best[1])
    print('Maximum corridor dual-floor product, draw',best[1],':',best[0])
    print('Draws not excluded by the dual-floor comparison:',possible)
    print('These are potential subcorridors, not certified selected histories.')


def sextic_certificate():
    """A two-evaluation exact certificate, valid for every real root parameter."""
    b=F(505,2)
    def coefficients(u,sigma):
        # Coefficients in tau²,tau,1 using generalized Laguerre L0..L3.
        L1=b-u
        L2=(u*u-2*(b+1)*u+b*(b+1))/2
        L3=(-u**3+3*(b+2)*u*u-3*(b+1)*(b+2)*u+b*(b+1)*(b+2))/6
        return sigma-L1,-2*sigma*L1+4*L2,2*sigma*L2-6*L3
    def average(sigma):
        return tuple((x+y)/2 for x,y in zip(coefficients(F(127),sigma),coefficients(F(185),sigma)))
    A,B,C=average(F(50))
    assert (A,B,C)==(F(-93,2),F(21075,2),F(-4998431,8))
    maximum=C-B*B/(4*A)
    assert A<0 and maximum==F(-3449743,124)<0
    slope=tuple(x-y for x,y in zip(average(F(51)),average(F(50))))
    assert slope==(F(1),F(-193),F(40375,4))
    assert slope[2]-slope[1]**2/4==F(1563,2)>0
    moments=(F(1),F(193,2),F(40375,4),F(9035931,8))
    H0=(moments[0],moments[1],moments[2])
    H50=tuple(moments[j+1]-50*moments[j] for j in range(3))
    assert H0[0]>0 and H0[0]*H0[2]-H0[1]**2==F(1563,2)>0
    assert H50==(F(93,2),F(21075,4),F(4998431,8))
    assert H50[0]*H50[2]-H50[1]**2==F(10349229,8)>0
    print('Sextic two-point average maximum at sigma50:',maximum)
    print('Its sigma derivative is (tau−193/2)^2+1563/2, strictly positive.')
    print('Hence every real repeated-root parameter fails if sigma<=50.')
    print('Positive moment matrices certify exclusion of all Fourier polynomials of degree<=3.')


def main():
    iv.dps=65
    I=iv.mpf
    b=I(505)/2
    for s in (5,10,15,25):
        discr=(b/iv.pi)**2-4*s*s
        low=2/(b/iv.pi+iv.sqrt(discr))
        high=(b/iv.pi+iv.sqrt(discr))/(2*s*s)
        matching=2*iv.pi/b
        assert low.b<matching.a and matching.b<high.a
        print('s=',s,'excluded width interval endpoints:',low,high)
    rmin=I('1.1')*I('32.18553')
    # Existing corridor: 2*pi*sqrt(r²−1)*R0 <157.28.
    dual_product=I('157.28')/(2*iv.pi)*rmin/iv.sqrt(rmin**2-1)
    assert dual_product.b<I('25.1').a
    rho2lower=1-2/rmin**2
    # a_match=2*pi*rho²/b. Bound 1+c(a_match) from above.
    sign_upper=1-2*rho2lower+4*iv.pi**2*I('25.1')**2/b**2
    assert sign_upper.b<I('-.60').a
    print('Corridor upper bound for r*R0:',dual_product)
    print('Upper bound on g polynomial at r=1 at matching width:',sign_upper)
    assert (b/(2*rho2lower)).b<127
    assert (2*iv.pi**2*I('25.1')**2/b).b<50
    assert 127<185<505  # u<2b is equivalent to radius<2rho at matching width
    sextic_certificate()
    feasible_broad_width()
    print('Matching width is inadmissible; other widths/higher degrees are not ruled out.')
    print('No finite-mark collision or selected-history bound follows.')


if __name__=='__main__':
    main()
