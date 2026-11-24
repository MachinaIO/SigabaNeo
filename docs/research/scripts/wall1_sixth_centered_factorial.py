"""Exact sixth centered moment expansion in Charlier polynomials.

Integer polynomial arithmetic only. The proposed selected factorial-moment
caps are sufficient assumptions, not established production estimates.
"""
from fractions import Fraction as F
from math import comb


def add(a,b):
    out=[0]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    while len(out)>1 and out[-1]==0:out.pop()
    return out


def multiply(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out


def evaluate(poly,mu):
    result=0
    for coefficient in reversed(poly):result=result*mu+coefficient
    return result


def falling(x,k):
    out=1
    for j in range(k):out*=x-j
    return out


def charlier(j,x,mu):
    return sum(comb(j,l)*(-mu)**(j-l)*falling(x,l) for l in range(j+1))


def weight_polynomials():
    stirling=[[0]*7 for _ in range(7)]
    stirling[0][0]=1
    for l in range(1,7):
        for k in range(1,l+1):
            stirling[l][k]=stirling[l-1][k-1]+k*stirling[l-1][k]
    weights=[]
    for j in range(7):
        poly=[0]*7
        for l in range(j,7):
            for k in range(j,l+1):
                power=6-l+k-j
                poly[power]+=comb(6,l)*(-1)**(6-l)*stirling[l][k]*comb(k,j)
        while len(poly)>1 and poly[-1]==0:poly.pop()
        assert all(c>=0 for c in poly)
        weights.append(poly)
    return weights


def main():
    weights=weight_polynomials()
    for j,w in enumerate(weights):
        print('w_'+str(j)+' coefficients in ascending powers of mu:',tuple(w))
    points=transfers=mean_zero=0
    for mu in (F(1,3),F(1),F(2),F(7,2),F(10)):
        for x in range(26):
            assert (x-mu)**6==sum(evaluate(w,mu)*charlier(j,x,mu) for j,w in enumerate(weights))
            points+=1
        # General subprobability selected weights: do not discard C1.
        for cutoff in (0,3,8,15):
            law=[F(1+(x*x+3*x)%5,100) if x<=cutoff else F(0) for x in range(16)]
            centered=sum(p*(x-mu)**6 for x,p in enumerate(law))
            moments=[sum(p*charlier(j,x,mu) for x,p in enumerate(law)) for j in range(7)]
            assert centered==sum(evaluate(w,mu)*c for w,c in zip(weights,moments))
            transfers+=1
        # A selected law of arbitrary mass whose conditional mean is mu.
        lower=mu.__floor__();fraction=mu-lower
        for mass in (F(1,7),F(2,3),F(1)):
            support=((lower,mass*(1-fraction)),(lower+1,mass*fraction))
            moments=[sum(p*charlier(j,x,mu) for x,p in support) for j in range(7)]
            assert moments[0]==mass and moments[1]==0
            assert sum(p*(x-mu)**6 for x,p in support)==sum(evaluate(w,mu)*c for w,c in zip(weights,moments))
            mean_zero+=1
    # Each polynomial is an upper cap for C_j/a, not an absolute-value cap.
    caps=([1],[0],[0,4],[0,1],[0,1,48],[0,1,40],[0,1,70,960])
    combined=[0]
    for w,cap in zip(weights,caps):combined=add(combined,multiply(w,cap))
    assert combined==[0,296,4660,1875]
    mu=750000
    bound=evaluate(combined,mu)
    assert bound<1876*mu**3<2000*mu**3
    relaxed=list(caps)
    relaxed[3]=[0,0,1] # C3/a<=mu^2 suffices, rather than <=mu.
    relaxed_combined=[0]
    for w,cap in zip(weights,relaxed):relaxed_combined=add(relaxed_combined,multiply(w,cap))
    assert relaxed_combined==[0,206,4640,1985]
    assert evaluate(relaxed_combined,mu)<1986*mu**3<2000*mu**3
    # On Z=0, (Z-mu)^6=mu^6; the 390-step conditional charge from the
    # looser 2000*a*mu^3 cap is therefore 390*2000/mu^3.
    reference=F(390*2000,mu**3)
    target=F(19515491,10**19)
    assert target==F('1.9515491e-12')
    assert reference<target
    print('Pointwise identities:',points,'arbitrary selected transfers:',transfers,
          'conditional-mean/C1=0 checks:',mean_zero)
    print('Combined cap coefficients:',tuple(combined))
    print('At mu750000: cap <1876*a*mu^3 <2000*a*mu^3 for a>0 (equality0 if a=0).')
    print('Relaxed C3<=a*mu^2 combined coefficients:',tuple(relaxed_combined))
    print('390-step conditional bound:',reference,'display:',float(reference),'target:',target)
    print('All exact polynomial and sufficient-cap arithmetic checks passed.')
    print('The selected Charlier caps remain assumptions; no production moment estimate is proved.')


if __name__=='__main__':
    main()
