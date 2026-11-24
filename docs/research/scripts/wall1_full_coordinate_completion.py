"""Exact joint-incidence normalization and full-coordinate majorant fixtures."""
from fractions import Fraction as F
from itertools import product


def centered(x,q):
    x%=q
    return x if x<=q//2 else x-q


def checks():
    checked=0
    for q,k in ((5,1),(7,1),(7,2)):
        coefficients=list(range(4+k));h=len(coefficients)
        for weight in (F(1,2),F(3,4)):
            for radius_sq in (4,9):
                kernel=F(0);anchor_kernel=F(0)
                for u,v in product(range(q),repeat=2):
                    values=[centered(u+c*(v-u),q) for c in coefficients]
                    kernel+=weight**sum(x*x for x in values)
                    anchor_kernel+=weight**sum(x*x for x in values[:4])
                full=weight**(-h*radius_sq)*kernel**2/q**2
                input_only=weight**(-h*radius_sq)*kernel*anchor_kernel/q**2
                exact_hits=0;eligible_gaussian=F(0)
                for u,v in product(range(q),repeat=2):
                    if u==v:continue
                    xs=[centered(u+c*(v-u),q) for c in coefficients]
                    for slope,shift in product(range(q),repeat=2):
                        ys=[centered(slope*x+shift,q) for x in xs]
                        energy=[x*x+y*y for x,y in zip(xs,ys)]
                        exact_hits+=all(e<=radius_sq for e in energy)
                        eligible_gaussian+=weight**(sum(energy)-h*radius_sq)/q**2
                assert F(exact_hits,q**2)<=eligible_gaussian<=full<=input_only
                checked+=1
    print('Passed exact full-coordinate incidence/normalization fixtures:',checked)


if __name__=='__main__':checks()
