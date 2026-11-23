"""Rank-three relation-code bound retaining the fixed triangular plane."""
import contextlib
from fractions import Fraction as F
from itertools import product
from math import comb
import io
from wall1_factorial_cumulants import difference_weights
from wall1_linear_remainder import transfer


def projected_height_checks():
    checked = positive = 0
    a, b = (1, 1, -1, -1, 0, 0), (0, 0, 1, 1, -1, -1)
    assert sum(x*x for x in a)*sum(x*x for x in b)-sum(x*y for x, y in zip(a, b))**2 == 12
    for v in product(range(-2, 3), repeat=6):
        total = sum(v)
        differences = sum((v[2*i]-v[2*i+1])**2 for i in range(3))
        residue = F(differences, 2)+F(total**2, 6)
        x, y = sum(c*d for c, d in zip(v, a)), sum(c*d for c, d in zip(v, b))
        gram_residue = F(sum(c*c for c in v))-F(x*x+x*y+y*y, 3)
        assert residue == gram_residue
        assert differences % 2 == total % 2
        if residue:
            assert residue >= F(2, 3)
            for u, w in product((-2, -1, 1, 2), repeat=2):
                assert residue+u*u+w*w >= F(8, 3)
            positive += 1
        else:
            # The triangular plane is saturated: pair constants sum to zero.
            assert v[0] == v[1] and v[2] == v[3] and v[4] == v[5]
            assert v[0]+v[2]+v[4] == 0
        checked += 1
    assert 12*30**4 < 3329**2
    assert 12*30**2 < 3329**2
    print(f'Passed {checked} exact projection identities, including {positive} positive-height cases.')


def code_ball_bound(s, new_positions=2, *, no_new_norm_four=False, one_point_determinant=None,
                    no_new_norm_six=False, short_six_determinant=None,
                    no_new_norm_eight=False, short_eight_determinant=None,
                    weighted_four_extension=False, two_point_four_determinant=None):
    """Crossing old coefficients lie in a fixed independent anchor basis."""
    I, iv, n, q, m, radius = [s[k] for k in ('I', 'iv', 'N', 'q', 'm', 'radius')]
    assert 12*30**4 < q**2 and 2*30 < q
    assert new_positions >= 1
    size, rank = 6+new_positions, 3+new_positions
    height = I(new_positions)+I(2)/3
    if two_point_four_determinant is not None:
        from wall1_triangle_two_four import UPPER_COUNTS
        assert new_positions==2 and two_point_four_determinant in UPPER_COUNTS
        assert not (no_new_norm_four or no_new_norm_six or no_new_norm_eight)
        height=I(two_point_four_determinant)/12
    if no_new_norm_four:
        assert q**2>6*size
        # Equilateral fundamental triangles have circumradius squared 4/3.
        height=I(max(3*new_positions+2,14))/3
    if no_new_norm_six:
        assert no_new_norm_four and q**2>8*size
        height=I(max(3*new_positions+2,20))/3
    if no_new_norm_eight:
        assert no_new_norm_six and no_new_norm_four and q**2>10*size
        height=I(max(3*new_positions+2,26))/3
    if short_eight_determinant is not None:
        from wall1_triangle_eight_extensions import UPPER_COUNTS
        assert not no_new_norm_four and not no_new_norm_six and not no_new_norm_eight
        assert short_six_determinant is None
        assert short_eight_determinant in UPPER_COUNTS[new_positions]
        height=I(short_eight_determinant)/12
    if short_six_determinant is not None:
        from wall1_triangle_six_extensions import UPPER_COUNTS
        assert not no_new_norm_four and not no_new_norm_six
        assert short_six_determinant in UPPER_COUNTS[new_positions]
        height=I(short_six_determinant)/12
    if one_point_determinant is not None:
        assert new_positions==1 and not no_new_norm_four
        assert one_point_determinant in (32,48)
        height=I(one_point_determinant)/12
    beta = I(rank*n)/(2*size*radius**2)
    a = iv.pi**2/beta
    alpha = a/q**2
    def theta(x):
        geometric = lambda y: 1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    short = theta(4*alpha)*theta(3*alpha)*theta(height*alpha)
    tail = iv.exp(-450*alpha)*theta(alpha/2)**3
    delta = 2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    prefactor=I(1)
    if weighted_four_extension:
        assert new_positions==3
        assert not (no_new_norm_four or no_new_norm_six or no_new_norm_eight)
        assert short_six_determinant is None and short_eight_determinant is None
        # Attached old coordinate weight5/8, other old weights1, new weights9/8.
        # Sum weights=9, so the existing exponential Markov factor is unchanged.
        short=theta(I(23)/5*alpha)*theta(I(72)/23*alpha)*theta(I(32)/9*alpha)
        scaled=alpha*I(8)/9
        tail=iv.exp(-450*scaled)*theta(scaled/2)**3
        scaled_a=a*I(8)/9
        delta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
        prefactor=iv.sqrt(I(4096)/3645)
    periodic = sum((comb(size, j)*delta**j for j in range(1, size+1)), I(0))
    gaussian = prefactor*(iv.pi/beta)**(I(size)/2)*((short+tail)/q**3+periodic)
    result=iv.exp(size*beta*radius**2)*gaussian**n/q**(rank*m)
    if two_point_four_determinant==32:
        from wall1_short_relation_shapes import equal_pair_sum_ball_bound, equal_pair_sum_alias_bound
        four_pairs=(equal_pair_sum_ball_bound(radius**2,n,4)
                    +equal_pair_sum_alias_bound(radius**2,n,4,q))/q**(5*m)
        result=min((result,four_pairs),key=lambda v:v.b)
    return result


def weighted_code_bound(s,t,coefficient,joint=None,*,exclude_three_new_four=False,
                        exclude_two_point_d32=False):
    """Cover all coefficient choices, retaining exceptional norm-four codes."""
    unrestricted=code_ball_bound(s,t)
    if joint is None:
        joint=unrestricted
    old=coefficient*joint
    if t in (3,4,5):
        from wall1_triangle_six_extensions import UPPER_COUNTS
        # At t=4 a norm-four row would be supported only on the new
        # coordinates, contradicting the nonzero old projection of a crossing.
        four_rare=(3*comb(6,4-t)*min((unrestricted,
            code_ball_bound(s,t,weighted_four_extension=True)),key=lambda v:v.b)
            if t==3 else s['I'](0))
        if t==3 and exclude_three_new_four:
            four_rare=s['I'](0)
        six_rare=sum((count*code_ball_bound(s,t,short_six_determinant=d)
                      for d,count in UPPER_COUNTS[t].items()),s['I'](0))
        split=(four_rare+six_rare+coefficient*code_ball_bound(s,t,
                               no_new_norm_four=True,no_new_norm_six=True))
        from wall1_triangle_eight_extensions import UPPER_COUNTS as EIGHT_COUNTS
        eight_rare=sum((count*code_ball_bound(s,t,short_eight_determinant=d)
                       for d,count in EIGHT_COUNTS[t].items()),s['I'](0))
        eight_split=(four_rare+six_rare+eight_rare+coefficient*code_ball_bound(s,t,
            no_new_norm_four=True,no_new_norm_six=True,no_new_norm_eight=True))
        split=min((split,eight_split),key=lambda v:v.b)
        if t<=4:
            previous=four_rare+coefficient*code_ball_bound(s,t,no_new_norm_four=True)
            old=min((old,previous),key=lambda v:v.b)
        return min((old,split),key=lambda v:v.b)
    if t>4:
        return old
    rare=3*comb(6,4-t)
    exceptional=rare*unrestricted
    if t==2:
        from wall1_triangle_two_four import UPPER_COUNTS
        exact=sum((count*code_ball_bound(s,2,two_point_four_determinant=d)
                   for d,count in UPPER_COUNTS.items() if not (exclude_two_point_d32 and d==32)),s['I'](0))
        exceptional=min((exceptional,exact),key=lambda v:v.b)
    if t==1:
        from wall1_triangle_dependent_codes import UPPER_COUNTS
        exceptional=sum((count*code_ball_bound(s,1,one_point_determinant=d)
                         for d,count in UPPER_COUNTS.items()),s['I'](0))
    split=exceptional+coefficient*code_ball_bound(s,t,no_new_norm_four=True)
    return min((old,split),key=lambda v:v.b)


def actual_parameters():
    from wall1_parallel_contraction import actual_parameters as prior
    with contextlib.redirect_stdout(io.StringIO()):
        s, baseline, linear = prior()
    I, iv, q, mu = [s[k] for k in ('I', 'iv', 'q', 'mu')]
    # A six-point anchor plus a crossing with two new points spans rank five.
    from wall1_parallel_contraction import single_class_pair_completion_count
    pair_completion=single_class_pair_completion_count(6,4,q)
    completion=min(I(q**24),I(pair_completion.numerator)/pair_completion.denominator,key=lambda v:v.b)
    activity = (comb(14, 6)*75*comb(8, 2)
                *weighted_code_bound(s,2,sum(comb(4, a)*q**a for a in (2, 3, 4)))*completion)
    from wall1_four_pair_extension import rank_five_envelope
    residual=(comb(14,6)*75*comb(8,2)*completion
        *weighted_code_bound(s,2,sum(comb(4,a)*q**a for a in (2,3,4)),exclude_two_point_d32=True))
    activity=min((activity,residual+rank_five_envelope(s,14)),key=lambda v:v.b)
    charge = linear*activity
    assert charge < I('1.151e-28')
    baseline[14] += activity
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0)) for poly in difference_weights(12)]
    known = s['normalizer']*transfer(weights, baseline)
    assert known < I('5.396e-13')
    print('Rank-five triangular weighted charge:', charge)
    print('Known transfer through ALL size-fourteen classes:', known)
    print('OPEN: size-15..24 residual classes and later selected histories; no complete draw-14 bound.')
    return s, baseline, linear


if __name__ == '__main__':
    projected_height_checks()
    actual_parameters()
