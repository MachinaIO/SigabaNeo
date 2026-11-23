"""Certified initial-history void bounds; see wall1_affine_void_moments.md.

No BKZ simulations. Numerical certificates use interval arithmetic; the finite
regression enumerates all nonempty subsets of three finite fixtures and all affine maps.
"""
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
from math import comb, factorial, gcd, isqrt
from mpmath import iv

ORDER = 8
STIRLING = [[0]*(ORDER+1) for _ in range(ORDER+1)]
ASSOCIATED = [[0]*(ORDER+1) for _ in range(ORDER+1)]
STIRLING[0][0] = ASSOCIATED[0][0] = 1
for i in range(1, ORDER+1):
    for j in range(1, i+1):
        STIRLING[i][j] = j*STIRLING[i-1][j]+STIRLING[i-1][j-1]
        ASSOCIATED[i][j] = sum(
            comb(i-1, k-1)*ASSOCIATED[i-k][j-1] for k in range(2, i+1))
assert ASSOCIATED[6][1:4] == [1, 25, 15]
assert ASSOCIATED[8][1:5] == [1, 119, 490, 105]


def normalized_moment_bound(mu, gamma, dependent, zero, prime):
    """Even central moment bound, valid for exact rationals or outward intervals."""
    main = sum(ASSOCIATED[ORDER][b]*mu**(b-ORDER) for b in range(1, ORDER//2+1))
    error = zero
    for ell in range(2, ORDER+1):
        for k in range(2, ell+1):
            term = dependent[k]*mu**(k-ell)
            for rank in range(2, k):
                for j in range(3, rank+2):
                    multiplicity = (comb(k, j)*comb(k-j, rank-j+1)
                                    * prime**((rank-1)*(k-rank-1)))
                    term += multiplicity*gamma[j]*mu**(rank-ell)
            error += comb(ORDER, ell)*STIRLING[ell][k]*term
    return main+error


def rank_mod(rows, prime):
    rows = [list(row) for row in rows]
    if not rows:
        return 0
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col] % prime), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col] % prime, -1, prime)
        rows[rank] = [v*inv % prime for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank:
                coefficient = rows[i][col] % prime
                rows[i] = [(a-coefficient*b) % prime for a, b in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


# Exhaustive subset checks, including a six-point circuit with input affine rank five.
def check_fixture(points, prime):
    count_points = len(points)
    records = {}
    for size in range(2, min(ORDER, count_points)+1):
        for indices in combinations(range(count_points), size):
            mask = sum(1 << i for i in indices)
            rows = [(*points[i], 1) for i in indices]
            input_rows = [(*points[i][1:], 1) for i in indices]
            rank = rank_mod(rows, prime)
            circuit = (size >= 3 and rank == size-1 and all(
                rank_mod(rows[:i]+rows[i+1:], prime) == size-1 for i in range(size)))
            records[mask] = (size, rank, rank_mod(input_rows, prime), circuit)
    design_masks = []
    for coeffs in product(range(prime), repeat=len(points[0])):
        design_masks.append(sum(1 << i for i, point in enumerate(points)
                                if (point[0]-sum(a*y for a, y in zip(coeffs[:-1], point[1:]))
                                    -coeffs[-1]) % prime == 0))
    for mask in range(1, 1 << count_points):
        count = mask.bit_count()
        mu = F(count, prime)
        circuits = {j: 0 for j in range(3, ORDER+1)}
        dependent = {k: 0 for k in range(2, ORDER+1)}
        ranks = {(k, r): 0 for k in range(3, ORDER+1) for r in range(2, k)}
        for submask, (k, rank, input_rank, circuit) in records.items():
            if submask & mask != submask:
                continue
            if circuit:
                circuits[k] += factorial(k)
            if input_rank < k:
                dependent[k] += factorial(k)
            if 2 <= rank < k:
                ranks[k, rank] += factorial(k)
        for (k, rank), value in ranks.items():
            upper = sum(comb(k, j)*comb(k-j, rank-j+1)*circuits[j]
                        *count**(rank-j+1)*prime**((rank-1)*(k-rank-1))
                        for j in range(3, rank+2))
            assert value <= upper
        gamma = {j: F(circuits[j], count**(j-1)) for j in circuits}
        dependence = {k: F(dependent[k], count**k) for k in dependent}
        bound = normalized_moment_bound(mu, gamma, dependence, F(0), prime)
        histogram = Counter((mask & design).bit_count() for design in design_masks)
        exact = sum(number*(F(hit)-mu)**ORDER for hit, number in histogram.items())
        exact /= len(design_masks)*mu**ORDER
        assert exact <= bound, (mask, exact, bound)
    return (1 << count_points)-1, len(design_masks), records

fixtures = [
    [(x, y) for x in range(3) for y in range(3)],
    [(0, 0, 0), (0, 1, 0), (0, 0, 1), (1, 0, 0),
     (1, 1, 0), (1, 0, 1), (2, 1, 1)],
    [(0, 0, 0, 0, 0), (1, 1, 0, 0, 0), (0, 0, 1, 0, 0),
     (0, 0, 0, 1, 0), (0, 0, 0, 0, 1), (1, 1, 1, 1, 2),
     (1, 0, 0, 0, 0), (2, 0, 1, 0, 1)],
]
tested = 0
for fixture in fixtures:
    count, laws, records = check_fixture(fixture, 3)
    tested += count
    print(f'Passed {count} subsets in dimension {len(fixture[0])}, all {laws} affine graph laws.')
assert tested == 893
assert any(k == 6 and rank == input_rank == 5 and circuit
           for k, rank, input_rank, circuit in records.values())

# Analytic Gaussian upper bounds and integer-ball lower bounds for the actual parameters.
iv.dps = 80
I = iv.mpf
q = 3329
m, n = 400, 506
volume = [I(1), I(2)]
for d in range(2, 522):
    volume.append(2*iv.pi*volume[d-2]/d)


def theta_upper(t):
    return 1+2*iv.exp(-t)/(1-iv.exp(-3*t))


def relation_theta_upper(size, beta):
    T = iv.sqrt(iv.pi/beta)
    result = theta_upper(beta*q*q/size)
    for j in range(1, size):
        result *= 1+T*iv.sqrt(I(j)/(j+1))
    return result


# Enumerate a primitive integer normal for every three-point affine relation.
# Normalize its last residue to 1, so the key runs over t != 0,-1.
normal_limit = isqrt(2*q)+1
normal_by_relation = {}
for u in range(-normal_limit, normal_limit+1):
    for v in range(-normal_limit, normal_limit+1):
        w = -u-v
        norm_sq = u*u+v*v+w*w
        if norm_sq > 2*q or not all(a % q for a in (u, v, w)):
            continue
        key = u*pow(w, -1, q) % q
        candidate = (norm_sq, u, v, w)
        if key not in normal_by_relation or candidate < normal_by_relation[key]:
            normal_by_relation[key] = candidate
assert set(normal_by_relation) == set(range(1, q-1))
for key, (norm_sq, u, v, w) in normal_by_relation.items():
    assert u+v+w == 0 and gcd(gcd(abs(u), abs(v)), abs(w)) == 1
    assert (u-key*w) % q == 0 and (v+(1+key)*w) % q == 0
normal_counts = Counter(record[0] for record in normal_by_relation.values())
assert min(normal_counts) == 6 and max(normal_counts) == 6422
print('Verified primitive normals for all 3327 three-point affine relations.')


def affine_triple_count_upper(beta, radius, dimension):
    """Sum the exact finite relation list instead of dropping coefficient-sum zero."""
    T = iv.sqrt(iv.pi/beta)
    total = I(0)
    for norm_sq, multiplicity in sorted(normal_counts.items()):
        t = beta*q*q/norm_sq
        assert t > iv.pi or t < iv.pi
        theta = (theta_upper(t) if t > iv.pi else
                 iv.sqrt(iv.pi/t)*theta_upper(iv.pi**2/t))
        section = (1+T/iv.sqrt(I(3)))*(1+T*iv.sqrt(I(3)/norm_sq))*theta
        total += multiplicity*section**dimension
    return iv.exp(3*beta*radius**2)*total


def candidate_lower(N, radius):
    a = iv.sqrt(radius**2-I(N-2)/4)
    out = radius+iv.sqrt(I(N))/2
    unrestricted = volume[N]*a**N-iv.pi/iv.sqrt(I(2))*volume[N-1]*a**(N-1)
    # Disjoint cubes for noncentered integer points lie in these coordinate caps.
    assert out > 1664
    discarded = 2*N*volume[N-1]*out**N*(1-(I(1664)/out)**2)**(I(N-1)/2)
    result = unrestricted-discarded
    assert result > 0
    return result


upper_bounds = {7: '1.598e-34', 8: '1.656e-30', 9: '1.957e-26',
                10: '2.641e-22', 11: '4.066e-18', 12: '7.149e-14'}
total = I(0)
for draw, upper in upper_bounds.items():
    N = 504+draw
    inputs = N-m
    radius = iv.sqrt(I('1.21')*iv.exp(2*(I(400-draw)*iv.ln(q)-iv.ln(volume[n]))/n)-2)
    count = candidate_lower(N, radius)
    mu = count/q**m
    gamma = {}
    for j in range(3, ORDER+1):
        beta = I((j-1)*N)/(2*j*radius**2)
        circuit_bound = (affine_triple_count_upper(beta, radius, N) if j == 3 else
                         q**(j-2)*iv.exp(j*beta*radius**2)*relation_theta_upper(j, beta)**N)
        gamma[j] = circuit_bound/count**(j-1)
    beta = I(N)/(2*radius**2)
    T = iv.sqrt(iv.pi/beta)
    dependence = {}
    for k in range(2, ORDER+1):
        relations = (q**(k-1)-1)//(q-1)
        bound = (relations*iv.exp(k*beta*radius**2)*(1+T)**(k*m+(k-2)*inputs)
                 *relation_theta_upper(2, beta)**inputs)
        dependence[k] = bound/count**k
    exit_bound = normalized_moment_bound(mu, gamma, dependence, I(0), q)/I('.280')
    assert exit_bound < I(upper)
    total += exit_bound
    print(f'draw {draw}: certified P(b_i > 0.280) < {upper}')
assert total < I('7.150e-14')
assert total+I('6.354e-12') < I('6.426e-12')
assert total+I('6.354e-12')+I('1.174e-12') < I('7.6e-12')
print('Certified joint initial exit < 7.150e-14; remaining draw-13--404 allowance 6.354e-12.')

# Verify the stated limitation of this majorant at the next draw.
next_draw = 13
next_dimension = 504+next_draw
next_radius = iv.sqrt(I('1.21')*iv.exp(
    2*(I(400-next_draw)*iv.ln(q)-iv.ln(volume[n]))/n)-2)
next_mu = candidate_lower(next_dimension, next_radius)/q**m
assert 105/(I('.280')*next_mu**4) > I('1.4e-9')
print('At draw 13 the leading term of this majorant alone exceeds 1.4e-9.')

# A stronger barrier for the fixed raw-ball domination, independent of the moment method.
barrier_draw = 16
barrier_dimension = 504+barrier_draw
barrier_radius_sq = I('1.21')*iv.exp(
    2*(I(400-barrier_draw)*iv.ln(q)-iv.ln(volume[n]))/n)-2
raw_covered_upper = (2*volume[barrier_dimension]
                     *(barrier_radius_sq+I(barrier_dimension)/4)**(I(barrier_dimension)/2)
                     /q**m)
assert raw_covered_upper < I('.707088')
assert 1-raw_covered_upper > I('.292912')
print('At the fixed draw-16 raw radius, every matrix has raw void fraction > 0.292912.')
