"""Concrete rectangular marked-lattice shell obstruction, certified via Berry--Esseen."""
from fractions import Fraction as F
from mpmath import iv

def main():
    iv.dps=65;I=iv.mpf;q=3329;m=400;n=505;g=I(550)
    def fi(x):return I(x.numerator)/x.denominator
    xs=[F(j*j,q*q) for j in range(-(q//2),q//2+1)]
    mu=sum(xs)/q;var=sum((x-mu)**2 for x in xs)/q
    third=sum(abs(x-mu)**3 for x in xs)/q
    beta3=fi(third)/fi(var)**I('1.5');error=I('0.4748')*beta3/iv.sqrt(m)
    def normal_tail(z):
        # Alternating integral of exp(-x²/2); all relevant 0<z<2.
        assert I(0)<z<I(2)
        term=z;total=term
        for j in range(1,160):
            term=-term*z*z*I(2*j-1)/(2*j*(2*j+1));total+=term
        next_term=abs(term*z*z*I(319)/(320*321))
        return I('.5')-(total+I([-1,1])*next_term)/iv.sqrt(2*iv.pi)
    V=iv.pi**253/iv.factorial(253)
    R=iv.sqrt((I('1.10')*g)**2-1)
    z=I('1.3');ell=R/iv.sqrt(m*fi(mu)+z*iv.sqrt(m*fi(var)))
    c=iv.exp((iv.log(V)+506*iv.log(g)-m*iv.log(ell))/(n-m))
    S=min(I(q),iv.sqrt(I('56.2142'))*V**(I(1)/506)*g,key=lambda x:x.b)
    B=iv.sqrt((I('1.10')*g*S**(-I(1)/506))**2-1)
    zb=(B*B/(ell*ell)-m*fi(mu))/iv.sqrt(m*fi(var))
    old_upper=normal_tail(z)+error;new_lower=normal_tail(zb)-error
    assert old_upper<I('.18') and new_lower>I('.18')
    shell_lower=new_lower-old_upper;assert shell_lower>I('.05')
    print('q,m,rank,g',q,m,n,g)
    for name,v in [('R',R),('cap S',S),('B',B),('marked side ell',ell),('unmarked side c',c),('standardized third moment',beta3),('Berry Esseen error',error),('new standardized threshold',zb),('p(R) upper',old_upper),('p(B) lower',new_lower),('shell mass lower',shell_lower),('power drift RHS / old power lower',(new_lower/old_upper)**24*new_lower)]:print(name,v)
    assert ell>1 and c>1
    print('Passed corridor-scale, determinant-construction, and shell-crossing inequalities.')
if __name__=='__main__':main()
