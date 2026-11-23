"""Three-row code bound retaining a primitive orthogonal four/four plane."""
from fractions import Fraction as F
from itertools import product
from math import comb


def finite_checks():
    a, b = (1, 1, -1, -1, 0, 0), (1, -1, 0, 0, 1, -1)
    assert sum(x*y for x,y in zip(a,b)) == 0
    checked = 0
    for v in product(range(-2, 3), repeat=6):
        x, y = sum(c*d for c,d in zip(a,v)), sum(c*d for c,d in zip(b,v))
        numerator = 4*sum(c*c for c in v)-x*x-y*y
        assert numerator >= 0 and numerator % 4 != 1
        if numerator:
            assert F(numerator, 4) >= F(1, 2)
        else:
            # Exclusive coordinates recover integer plane coefficients.
            u, w = -v[2], v[4]
            assert v == tuple(u*c+w*d for c,d in zip(a,b))
        checked += 1
    assert 16*28**4 < 3329**2
    print(f'Passed {checked} exact orthogonal projection and saturation checks.')
    checked = 0
    for v in product(range(-2, 3), repeat=7):
        x, y = v[0]+sum(v[1:4]), v[0]+sum(v[4:7])
        residue = F(sum(c*c for c in v))-F(4*x*x-2*x*y+4*y*y, 15)
        differences = sum((v[i]-v[j])**2 for group in (range(1,4), range(4,7))
                          for i in group for j in group if i < j)
        explicit = F(differences, 3)+F((3*v[0]-sum(v[1:]))**2, 15)
        assert residue == explicit
        if residue:
            assert residue >= F(3, 5)
        else:
            assert v[1] == v[2] == v[3] and v[4] == v[5] == v[6]
            assert v[0] == v[1]+v[4]
        checked += 1
    assert 15*29**4 < 3329**2
    print(f'Passed {checked} exact shared-point projection and saturation checks.')


def code_ball_bound(s, *, shared=False, new_positions=2, no_new_norm_four=False,
                    shared_one_point_determinant=None, shared_two_point_determinant=None):
    """Requires a nonzero old part supported in an independent anchor basis.

    no_new_norm_four additionally excludes every balanced norm-four line
    outside the old plane. It must only be used after covering those codes.
    """
    I, iv, n, q, m, R = [s[k] for k in ('I', 'iv', 'N', 'q', 'm', 'radius')]
    assert new_positions >= 1
    old_size, cutoff, determinant = (7, 29, 15) if shared else (6, 28, 16)
    size, rank = old_size+new_positions, old_size+new_positions-3
    residual = I(3)/5 if shared else I(1)/2
    height = I(new_positions)+residual
    if no_new_norm_four:
        # Triangulate the shared plane's fundamental rhombus; its triangle
        # circumradius squared is 8/5. The orthogonal square gives 2.
        covering = I(8)/5 if shared else I(2)
        assert q**2 > size*6
        height = max(height,I(6)-covering)
    if shared_one_point_determinant is not None:
        assert shared and new_positions==1 and not no_new_norm_four
        assert shared_one_point_determinant in (36,44,56,60)
        # The old plane and a unit-new-coordinate short row form a
        # primitive basis of the complete rank-three integer plane.
        height=I(shared_one_point_determinant)/15
    if shared_two_point_determinant is not None:
        from wall1_shared_two_point_codes import COUNTS
        assert shared and new_positions==2 and not no_new_norm_four
        assert shared_two_point_determinant in COUNTS
        height=I(shared_two_point_determinant)/15
    assert determinant*cutoff**4 < q**2 and determinant*cutoff**2 < q**2
    beta = I(rank*n)/(2*size*R**2)
    a = iv.pi**2/beta
    alpha = a/q**2
    def theta(x):
        geometric = lambda y: 1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    short = (theta(4*alpha)*theta(I(15)*alpha/4)*theta(height*alpha) if shared
             else theta(4*alpha)**2*theta(height*alpha))
    tail = iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**3
    delta = 2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic = sum((comb(size,j)*delta**j for j in range(1,size+1)), I(0))
    gaussian = (iv.pi/beta)**(I(size)/2)*((short+tail)/q**3+periodic)
    return iv.exp(size*beta*R**2)*gaussian**n/q**(rank*m)


if __name__ == '__main__':
    finite_checks()
