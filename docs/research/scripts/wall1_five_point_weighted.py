"""Weighted full-modular Gaussian count for the five-point short code."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from mpmath import iv


def ball_bound(radius_sq, dimension, q):
    scale = iv.mpf(dimension)/radius_sq
    a, b, c = scale/20, 11*scale/40, 9*scale/20
    A, B = a+2*c, b/2+2*c
    layer = c*a/(a+2*c)
    assert layer < c*b/(b+4*c)
    def theta(x):
        geometric = lambda y: 1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    kernel = theta(A)*theta(2*b)*theta(B)*theta(q*q*layer)**2
    return iv.exp((a+2*b+2*c)*radius_sq)*kernel**dimension


def finite_checks():
    a,b,c = F(1,20),F(11,40),F(9,20)
    A,B = a+2*c,b/2+2*c
    lam = c*a/A
    checked = 0
    q = 7
    for x,z,d,u,v in product(range(-2,3),repeat=5):
        original = a*x*x+b*((z+d)**2+z*z)+c*((x+d-q*u)**2+(x-d-q*v)**2)
        residual = q*q*(c*(u*u+v*v)-c*c*(u+v)**2/A-c*c*(u-v)**2/B)
        completed = (2*b*(z+F(d,2))**2+A*(x-c*q*(u+v)/A)**2
                     +B*(d-c*q*(u-v)/B)**2+residual)
        assert original == completed
        assert residual >= q*q*lam*(u*u+v*v)
        checked += 1
    iv.dps = 60
    balls = 0
    for radius in (1,2):
        points = [p for p in product(range(-radius,radius+1),repeat=2)
                  if sum(x*x for x in p) <= radius*radius]
        for q in (3,5,7,17):
            residues = Counter(tuple(x%q for x in p) for p in points)
            count = 0
            for x,y,z in product(points,repeat=3):
                left = tuple((a+b-c)%q for a,b,c in zip(x,y,z))
                right = tuple((a-b+c)%q for a,b,c in zip(x,y,z))
                count += residues[left]*residues[right]
            assert count <= ball_bound(iv.mpf(radius*radius),2,q).a
            balls += 1
    print(f'Passed {checked} exact square completions and {balls} full-modular ball counts.')


if __name__ == '__main__':
    finite_checks()
