"""Exact mixed-weight convolution identity and interval envelope checks."""
from itertools import product
from fractions import Fraction as F
from mpmath import iv
from wall1_anchored_dual_completion import hyperplane_sum_bound


def checks():
    checked=0
    for q in (3,5):
        old=[F(1,1+min(x,q-x)**2) for x in range(q)]
        free=[F(1,1+2*min(x,q-x)**2) for x in range(q)]
        for f in (0,1):
            cols=((2,-1)+(0,)*f,(-1,2)+(0,)*f)
            factors=[old,old]+[free]*f
            conv=[F(1)]+[F(0)]*(q-1)
            for factor in factors+[old,old]:
                conv=[sum((conv[y]*factor[(x-y)%q] for y in range(q)),F(0)) for x in range(q)]
            hyper=[F(0)]*q
            for x in product(range(q),repeat=2+f):
                for b0,b1 in product(range(q),repeat=2):
                    term=old[b0]*old[b1]
                    for j,factor in enumerate(factors):
                        term*=factor[(x[j]+cols[0][j]*b0+cols[1][j]*b1)%q]
                    hyper[sum(x)%q]+=term
            assert hyper==conv
            checked+=1
    print('Passed exact mixed-weight hyperplane convolution checks:',checked)
    iv.dps=60;count=0
    for q in (3,5):
        for alpha,beta in ((iv.mpf('.5'),iv.mpf('.25')),(iv.mpf(1),iv.mpf(1))):
            for f in (0,1,3):
                def phi(a,x):
                    low=sum((iv.exp(-a*(z+iv.mpf(x)/q)**2) for z in range(-12,13)),iv.mpf(0))
                    tail=2*iv.exp(-a*iv.mpf('12.5')**2)/(1-iv.exp(-26*a))
                    return iv.mpf([low.a,(low+tail).b])
                raw=sum((phi(q*q*alpha,x)**4*phi(q*q*beta,x)**f
                         for x in range(-(q//2),q//2+1)),iv.mpf(0))/q
                direct=(q*iv.sqrt(alpha/iv.pi))**4*(q*iv.sqrt(beta/iv.pi))**f*raw
                bound=hyperplane_sum_bound(q,alpha,beta,2,f)
                assert direct.b<=bound.b
                count+=1
    print('Passed mixed Gaussian interval envelope checks:',count)


if __name__=='__main__':checks()
