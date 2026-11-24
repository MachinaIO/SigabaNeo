"""Averaged-rounding count audit and deterministic density-floor screen.

For an independent lattice basis of r vectors of norm<=1, unbiased
coordinate rounding has E||Y||^2<=||x||^2+r/4. Its probability of landing
at a fixed lattice point is a product of unit-integral tent functions in
basis coordinates, hence has integral det(K0). Integrating Markov's bound
on ||x||<=sqrt(R^2-r/4), and then summing over cosets of K0 in K, gives

 # (K intersect B_R) >= 2/(r+2) * V_r * (R^2-r/4)^((r+2)/2)/(R^2 det K).

The finite rational checks below audit rounding and tent normalization;
they do not replace the general integration argument. The numeric stage
uses the proposed count expression and existing Hermite floors. It is a
deterministic mean-density screen, not a probability or history estimate.
"""
from fractions import Fraction as F
from itertools import product
from mpmath import iv
from wall1_hermite_budget import log_floors

iv.dps=40


def norm2(v):
    return sum((x*x for x in v),F(0))


def rounding_checks():
    bases=(((F(1),F(0)),(F(3,5),F(4,5))),
           ((F(1,2),F(0)),(F(1,4),F(1,2))))
    checks=markov_checks=0
    for basis in bases:
        assert all(norm2(b)<=1 for b in basis)
        determinant=abs(basis[0][0]*basis[1][1]-basis[0][1]*basis[1][0])
        # Integral of 1-|t| over [-1,1], computed as two linear pieces.
        tent_integral=F(1,2)+F(1,2)
        assert determinant*tent_integral**2==determinant>0
        for shift in ((F(0),F(0)),(F(1,7),F(-2,7))):
            for coeff in product((F(-1,3),F(0),F(1,4),F(1,2)),repeat=2):
                x=tuple(shift[j]+sum(coeff[i]*basis[i][j] for i in range(2)) for j in range(2))
                lower=tuple(c.__floor__() for c in coeff)
                fractional=tuple(c-lo for c,lo in zip(coeff,lower))
                outcomes=[]
                for bits in product((0,1),repeat=2):
                    probability=F(1)
                    for bit,t in zip(bits,fractional):
                        probability*=t if bit else 1-t
                    y=tuple(shift[j]+sum((lower[i]+bits[i])*basis[i][j] for i in range(2))
                            for j in range(2))
                    outcomes.append((probability,y))
                assert sum(p for p,_ in outcomes)==1
                assert tuple(sum(p*y[j] for p,y in outcomes) for j in range(2))==x
                expectation=sum(p*norm2(y) for p,y in outcomes)
                variance=sum(norm2(b)*t*(1-t) for b,t in zip(basis,fractional))
                assert expectation==norm2(x)+variance<=norm2(x)+F(2,4)
                for radius2 in (F(1),F(2),F(4)):
                    actual=sum(p for p,y in outcomes if norm2(y)<=radius2)
                    assert actual>=max(F(0),1-(norm2(x)+F(2,4))/radius2)
                    markov_checks+=1
                checks+=1
    return checks,markov_checks


def interval_minimum(a,b):
    return iv.mpf([min(a.a,b.a),min(a.b,b.b)])


def main():
    print('Exact rounding and Markov checks:',rounding_checks())
    cutoff=F(513,4)  # 2+505/4 =128.25
    # Expand 507*x*(x-2)-2*x*(x-a)-506*(x-a)*(x-2).
    quadratic=(F(507-2-506),-1014+2*cutoff+506*(cutoff+2),-1012*cutoff)
    assert quadratic==(-1,508*cutoff-2,-1012*cutoff)
    assert sum(coefficient*cutoff**power for coefficient,power in zip(quadratic,(2,1,0)))==507*cutoff*(cutoff-2)>0
    # Concavity, positivity at a, and negative value at zero imply two
    # positive roots, exactly one above a. The expression increases and
    # then decreases on x>a. Its minimum on any closed interval is at an
    # endpoint, even though it is NOT globally monotone in g.
    assert quadratic[0]<0 and quadratic[1]>0 and quadratic[2]<0
    assert quadratic[1]**2+4*quadratic[2]>0
    print('Certified derivative numerator: -x^2+65149*x-129789.')
    floors=log_floors()
    logv506=253*iv.ln(iv.pi)-iv.loggamma(254)
    logv505=iv.mpf(505)/2*iv.ln(iv.pi)-iv.loggamma(iv.mpf(507)/2)
    gmax=iv.exp((400*iv.ln(3329)-logv506)/506)
    a=iv.mpf(513)/4
    factor=iv.mpf(121)/100
    def density(g):
        x=factor*g*g
        assert x.a>a.b
        return iv.exp(iv.ln(iv.mpf(2)/507)+logv505-logv506
                      +iv.mpf(507)/2*iv.ln(x-a)-iv.ln(x-2)-506*iv.ln(g))-iv.mpf(1)/3328
    upper_endpoint=density(gmax)
    results=[]
    floor_values=[]
    for freeze,floor in enumerate(floors):
        gfloor=iv.exp((floor-logv506)/506)
        value=density(gfloor)
        floor_values.append(value)
        results.append(interval_minimum(value,upper_endpoint))
    minimum_index=min(range(len(results)),key=lambda i:results[i].a)
    minimum=results[minimum_index]
    assert all(minimum.b<value.a for i,value in enumerate(results) if i!=minimum_index)
    assert minimum.a>750000
    print('gmax endpoint Favg:',upper_endpoint)
    print('Strict global minimum endpoint interval over freezes0..406:',minimum,
          'attained at freeze',minimum_index)
    for threshold in (1,58,1000000):
        passed=[]
        for freeze,value in enumerate(results):
            if value.a>threshold:
                passed.append(freeze)
            else:
                assert value.b<threshold
        print('Threshold',threshold,'passed freezes:',len(passed),
              'largest:',max(passed) if passed else None)
    for freeze in (0,14,100,200,246,255,300,400,405,406):
        print('freeze',freeze,'floor endpoint Favg:',floor_values[freeze],
              'uniform interval minimum:',results[freeze])
    mu=750000
    budget=F(19515491,10**19) # 1.9515491e-12
    proposed=F(390*2000,mu**3)
    assert proposed==F(208,112500000000000)
    assert proposed<budget
    independent_coefficient=F(mu+25*mu**2+15*mu**3,mu**3)
    assert independent_coefficient<F(150001,10000)<2000
    print('Conditional sixth-moment target total:',proposed,'< remaining comparison budget',budget)
    print('Independent-Bernoulli comparison coefficient <15.0001; no actual moment bound claimed.')
    print('Endpoint minima certify the actual-g interval; global monotonicity was not assumed.')
    print('No probability or selected-history incidence estimate is asserted.')


if __name__=='__main__':
    main()
