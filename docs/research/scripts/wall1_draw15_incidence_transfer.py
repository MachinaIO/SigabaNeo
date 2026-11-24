"""Draw15 complete two-relation cover and signed-witness error diagnostic.

Uses upper candidate means, not the lower normalization of the draw14 kernel.
No useful actual-law bound is asserted unless the final error is small enough.
"""
import contextlib
import io
from pathlib import Path
import runpy
from math import factorial
from wall1_general_two_relations import draw14_bounds
from wall1_factorial_cumulants import cumulant_errors
from wall1_affine_circuit_components import exponential


def geometry_state():
    root=Path(__file__).parent
    with contextlib.redirect_stdout(io.StringIO()):
        g=runpy.run_path(str(root/'wall1_affine_void_moments.py'))
    I,iv=g['I'],g['iv']
    q,m,N,inputs=3329,400,519,119
    radius=iv.sqrt(I('1.21')*iv.exp(2*(385*iv.ln(q)-iv.ln(g['volume'][506]))/506)-2)
    mu=2*g['volume'][N]*(radius**2+I(N)/4)**(I(N)/2)/q**m
    rho=2*g['volume'][m]*(radius**2+I(m)/4)**(I(m)/2)/q**m
    assert mu.b<I('9.287185').a and rho.b<I('1.192e-300').a
    epsilon={}
    for j in range(3,25):
        beta=I((j-1)*N)/(2*j*radius**2)
        count=(g['affine_triple_count_upper'](beta,radius,N) if j==3 else
               q**(j-2)*iv.exp(j*beta*radius**2)*g['relation_theta_upper'](j,beta)**N)
        epsilon[j]=count/q**(m*(j-1))
    return dict(I=I,iv=iv,q=q,m=m,N=N,inputs=inputs,mu=mu,radius=radius,
                rho_max=rho,geometry=g,epsilon=epsilon)


def main():
    s=geometry_state()
    I,iv=s['I'],s['iv']
    print('Draw15 geometry N519, inputs119, exponent385; upper mean:',s['mu'],flush=True)
    s,full,strata=draw14_bounds(geometry_state=s)
    print('Complete two-relation cover evaluated through size24.',flush=True)
    for h in range(3,22):
        terms=[(key,v) for key,v in strata.items() if key[0]==h]
        leader=max(terms,key=lambda item:item[1].b)[0] if terms else 'circuit'
        print('size',h,'full log10',iv.log10(full[h]),'largest stratum',leader,flush=True)
    with contextlib.redirect_stdout(io.StringIO()):
        witness=runpy.run_path(str(Path(__file__).with_name('wall1_draw15_lower_witness.py')))
    order=21
    errors=cumulant_errors(s['mu'],s['rho_max'],s['q'],full,order)
    # Never introduce float weights in the signed transfer.
    from fractions import Fraction as F
    weights=[sum(witness['a'][j]*F(factorial(j),factorial(j-k))*10**(j-k)
                 for j in range(k,order+1)) for k in range(order+1)]
    series=[I(0),I(0)]+[(full.get(j,I(0))+errors[j])/factorial(j) for j in range(2,order+1)]
    correction=exponential(series,start=1)
    charge=sum((abs(I(w.numerator)/w.denominator)*correction[j] for j,w in enumerate(weights)),I(0))
    baseline=witness['val'](F(10))
    lower=I(baseline.numerator)/baseline.denominator-charge
    assert charge.b<I('8.744e-30').a
    assert lower.a>I('0.0000247527').b
    uniform_weights=[sum((abs(I(witness['a'][j].numerator)/witness['a'][j].denominator)
                         *factorial(j)/factorial(j-k)*s['mu']**(j-k)
                         for j in range(k,order+1)),I(0)) for k in range(order+1)]
    uniform_charge=sum((uniform_weights[j]*correction[j] for j in range(2,order+1)),I(0))
    print('Uniform-mean signed-witness error upper:',uniform_charge,flush=True)
    assert uniform_charge.b<I('1e-25').a
    assert I('0.0000647').a-uniform_charge.b>I('0.00006469').b
    print('Certified actual raw-void probability >0.00006469.',flush=True)
    print('Complete signed-witness error upper:',charge,flush=True)
    print('Raw-void lower certificate before max with zero:',lower,flush=True)
    print('Positive certificate:',bool(lower.a>0),flush=True)
    print('This concerns raw candidates only, not projected void or BKZ failure.',flush=True)


if __name__=='__main__':
    main()
