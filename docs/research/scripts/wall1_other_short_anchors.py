"""Third-circuit extensions for orthogonal and seven-point short anchors."""
import contextlib
import io
from itertools import combinations
from math import comb
from wall1_general_two_relations import draw14_bounds
from wall1_rank_five_code import actual_parameters as known_fourteen
from wall1_triangular_third_relation import new_group_bound
from wall1_short_relation_shapes import (
    balanced_rows,
    orthogonal_pair_ball_bound, orthogonal_pair_alias_bound,
    shared_four_ball_bound, shared_four_gaussian_bound)
from wall1_factorial_cumulants import difference_weights
from wall1_linear_remainder import remainder_weights


def finite_checks():
    for size, overlap, expected in ((6, 2, 180), (7, 1, 630)):
        count = 0
        for left, right in combinations(list(combinations(range(size), 4)), 2):
            if len(set(left) & set(right)) != overlap or len(set(left) | set(right)) != size:
                continue
            for u in balanced_rows(left, size):
                for v in balanced_rows(right, size):
                    if size == 6 and sum(a*b for a,b in zip(u,v)) != 0:
                        continue
                    count += 1
        assert count == expected, (size, count)
        print('Exact short-anchor witness count:', size, count, flush=True)


def other_envelopes(s, *, exclude_triangular=False):
    """If restricted, the caller must add a full triangular-anchor cover."""
    from wall1_orthogonal_third_code import code_ball_bound
    from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count
    I, q, m, n, R, mu = [s[k] for k in ('I', 'q', 'm', 'N', 'radius', 'mu')]
    orth = (orthogonal_pair_ball_bound(R**2, n)
            +orthogonal_pair_alias_bound(R**2, n, q))/q**(4*m)
    shared = (shared_four_ball_bound(R**2, n)
              +shared_four_gaussian_bound(R**2, n, q, aliases_only=True))/q**(5*m)
    groups = {t: new_group_bound(R**2, n, t, q)/q**(m*(t-1)) for t in range(2, 20)}
    orth_triple = code_ball_bound(s)
    shared_triple = code_ball_bound(s, shared=True)
    same_rank = {size:code_ball_bound(s,shared=(size==7),new_positions=1) for size in (6,7)}
    larger_codes = {(size,t): code_ball_bound(s,shared=(size==7),new_positions=t)
                    for size in (6,7) for t in range(3,25-size)}
    ordinary_codes = {(size,t): code_ball_bound(s,shared=(size==7),new_positions=t)
                      for size in (6,7) for t in range(1,5)}
    no_four_codes = {(size,t): code_ball_bound(s,shared=(size==7),new_positions=t,
                                             no_new_norm_four=True)
                    for size in (6,7) for t in range(1,5)}
    shared_dependent_rare=sum((count*code_ball_bound(s,shared=True,new_positions=1,
                                 shared_one_point_determinant=gram)
                              for gram,count in ((36,24),(44,28),(56,24),(60,5))),I(0))
    from wall1_shared_two_point_codes import COUNTS
    shared_two_rare=sum((count*code_ball_bound(s,shared=True,new_positions=2,
                              shared_two_point_determinant=gram)
                        for gram,count in COUNTS.items()
                        if not (exclude_triangular and gram==44)),I(0))
    from wall1_shared_four_new_six import ball_bound as shared_four_bound, COUNTS as SIX_COUNTS
    shared_four_rare=sum((count*shared_four_bound(s,I(gram)/15)
                         for gram,count in SIX_COUNTS.items()),I(0))
    shared_four_remainder=shared_four_bound(s,I(32)/5)
    def weighted_joint(size,t,coefficients,joint):
        old=coefficients*joint
        if t>4:
            return old
        # A new norm-four line uses all t new coordinates. Each such line
        # determines at most one third code and normalized fundamental row.
        rare=3*comb(size,4-t)
        rare_bound=shared_dependent_rare if (size,t)==(7,1) else rare*ordinary_codes[size,t]
        if (size,t)==(7,2):
            rare_bound=shared_two_rare
        split=rare_bound+coefficients*no_four_codes[size,t]
        if (size,t)==(7,4):
            split=min((split,shared_four_rare+coefficients*shared_four_remainder),key=lambda v:v.b)
        return min((old,split),key=lambda v:v.b)
    result = {}
    s['other_anchor_terms'] = {}
    for h in range(15, 25):
        for r in range(4, h-1):
            total = I(0)
            for size, rank, patterns, anchor in ((6, 4, 180, orth), (7, 5, 630, shared)):
                if r < rank or r == h-2:
                    continue
                choices = comb(h, size)*patterns
                if r == rank:
                    old = choices*anchor*q**((r-1)*(h-size))
                    # Fix the least outside label, so no extra position factor.
                    coefficient=sum(comb(rank,a)*q**(a-1) for a in range(3,rank+1))
                    dependent = (choices*weighted_joint(size,1,coefficient,same_rank[size])
                                 *q**((r-1)*(h-size-1)))
                    chosen = min((old,dependent),key=lambda v:v.b)
                    total += chosen
                    s['other_anchor_terms'][h,r,size,'same-rank'] = chosen
                    continue
                small = I(0)
                large = I(0)
                for t in range(2, min(r-rank+1, h-size)+1):
                    extra = r-rank-t+1
                    coefficients = sum(comb(rank, a)*q**(t+a-2)
                                       for a in range(max(1, 4-t), rank+1))
                    joint = anchor*groups[t]
                    if size == 6 and t == 2:
                        joint = min((joint, orth_triple), key=lambda v: v.b)
                    if size == 7 and t == 2:
                        joint = min((joint, shared_triple), key=lambda v: v.b)
                    if t >= 3:
                        joint = min((joint, larger_codes[size,t]), key=lambda v: v.b)
                    # Contracting the fixed anchor and crossing preserves
                    # absence of coloops. Quotient rank extra gives at least
                    # extra+1 bases for every witnessed support.
                    charge = (choices*comb(h-size, t)*comb(h-size-t, extra)
                              *weighted_joint(size,t,coefficients,joint)*mu**extra
                              *q**((r-1)*(h-r-3))/(extra+1))
                    if t == 2:
                        small += charge
                    else:
                        large += charge
                parallel = (choices*anchor*mu**(r-rank)
                            *parallel_completion_count(h-size,r-rank,rank,q))
                triple = orth_triple if size == 6 else shared_triple
                marked = (choices*comb(h-size,2)
                          *weighted_joint(size,2,sum(comb(rank,a)*q**a for a in range(2,rank+1)),triple)
                          *mu**(r-rank-1)
                          *marked_parallel_completion_count(h-size-2,r-rank-1,rank,q))
                chosen_small = min((small, parallel, marked), key=lambda v: v.b)
                total += large+chosen_small
                s['other_anchor_terms'][h,r,size,'large-crossing'] = large
                s['other_anchor_terms'][h,r,size,'small-crossing'] = chosen_small
            result[h, r] = total
    return result


def actual_parameters():
    from wall1_larger_triangular_components import triangular_envelopes
    with contextlib.redirect_stdout(io.StringIO()):
        s, baseline, _ = known_fourteen()
        _, _, full = draw14_bounds()
        _, _, no_double = draw14_bounds(exclude_double_short_anchors=True)
    I, mu, iv = s['I'], s['mu'], s['iv']
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0)) for poly in difference_weights(12)]
    linear = remainder_weights(weights, baseline, 15)
    triangle, other = triangular_envelopes(s), other_envelopes(s,exclude_triangular=True)
    largest = sorted(((v.b,key,v) for key,v in s['other_anchor_terms'].items()
                      if key[0] == 15 and v.a > 0),reverse=True)
    for _,key,v in largest[:8]:
        print('other-anchor term',key,'weighted log10',iv.log10(s['normalizer']*linear[15]*v),flush=True)
    for h in range(15, 25):
        total = I(0)
        for (size, r, c), value in full.items():
            if size != h or r < 3:
                continue
            if c == 4 and r >= 4:
                candidate = no_double[h, r, c]+triangle[h, r]+other[h, r]
                value = min((value, candidate), key=lambda v: v.b)
            total += value
        print(h, 'full residual log10', iv.log10(s['normalizer']*linear[h]*total), flush=True)
    print('OPEN: full residual and selected history still require proof.')


if __name__ == '__main__':
    finite_checks()
    actual_parameters()
