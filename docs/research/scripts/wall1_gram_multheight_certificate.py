"""Uniform local certificate given a full marked Gram majorizer and winner cap."""
from mpmath import iv
from wall1_rectangular_multheight import finite_scalar_moment_upper


def main():
    numerator,divisor,_=finite_scalar_moment_upper()
    iv.dps=80;I=iv.mpf
    m=400;half=16;J=33;g0=I(549)
    scalar_log=m*(iv.log(I(numerator))-iv.log(I(divisor)))
    sum_j2=half*(half+1)*(2*half+1)//3
    ell=I(102)
    # Nonzero q*t_i lies in M with norm<=ell; a trivial mark group has void0.
    cap=ell
    B2=(I('1.10')*g0)**2*cap**(-I(2)/506)-1
    log_bound=I(24)/10*(sum_j2-J*B2)/ell**2
    log_bound+=scalar_log-24*iv.log(I('.280'))
    epsilon=iv.exp(log_bound)
    assert epsilon.b<I('1e-18').a
    total=390*epsilon
    assert total.b<I('3.9e-16').a
    print('Local capped potential upper:',epsilon)
    print('390-transition charge upper:',total)
    seed=I('1.9704509e-12');budget=I('3.922e-12')
    remaining=budget-seed-I('3.9e-16')
    assert remaining.a>I('1.951159e-12').b
    print('Formal remaining allowance (unreachable gate):',remaining)
    print('Requires g>=549 and full marked Gram<=(102/3329)^2 I; winner cap follows.')
    print('This family is impossible for actual cubic-projection states; see obstruction certificate.')

if __name__=='__main__':main()
