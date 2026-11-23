"""Rogers' regular-simplex fraction in dimension 24, with rational error bounds.

In edge coordinates v_i of a side-two simplex, <v_i,v_j>=2(1+δ_ij).
Writing the barycentric coefficients as r*u_i with sum(u_i)=1 gives radial
volume r^23 dr and uniform u on the opposite face. The unit sector cuts the
radial interval at (2*(1+S))^(-1/2), S=sum(u_i^2). Thus the 25 disjoint
sectors cover the fraction 25/2^12 E[(1+S)^(-12)] of the simplex.

The uniform Dirichlet monomial integral is 23! prod(alpha_i!)/(23+|alpha|)!.
Convolving the integer sequence (2j)!/j! gives the moments E[S^k].
Taylor at 1/12 through odd degree K-1 gives a lower bound. The remainder
is positive and at most binom(11+K,11)*(S-1/12)^K since S>=0.
"""
from fractions import Fraction as Q
from math import comb, factorial
from mpmath import iv


def moments(order):
    terms = [factorial(2*j)//factorial(j) for j in range(order+1)]
    coeffs = [1]+[0]*order
    for _ in range(24):
        coeffs = [sum(coeffs[k-j]*terms[j] for j in range(k+1)) for k in range(order+1)]
    return [Q(factorial(k)*coeffs[k]*factorial(23),factorial(23+2*k)) for k in range(order+1)]


def sector_enclosure(order):
    assert order > 0 and order % 2 == 0
    a = Q(1,12)
    mu = moments(order)
    centered = [sum(comb(j,i)*mu[i]*(-a)**(j-i) for i in range(j+1)) for j in range(order+1)]
    lower = sum((-1)**k*comb(11+k,11)*centered[k]/(1+a)**(12+k) for k in range(order))
    return lower, lower+comb(11+order,11)*centered[-1]


if __name__ == "__main__":
    iv.dps = 45
    lo, hi = sector_enclosure(40)
    enclosure = iv.mpf([(iv.mpf(lo.numerator)/lo.denominator).a,
                        (iv.mpf(hi.numerator)/hi.denominator).b])
    density = 25*enclosure/4096
    gamma = 4*(density*factorial(12))**(iv.mpf(1)/12)/iv.pi
    print("simplex volume density",density)
    print("Rogers Hermite coefficient",gamma)
    assert iv.mpf("4.08111636542017") < gamma < iv.mpf("4.08111636542026")
