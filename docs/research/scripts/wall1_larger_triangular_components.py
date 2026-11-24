"""Third-relation envelopes at sizes 15--24 and a short-anchor diagnostic."""
import contextlib
from math import comb
import io
from wall1_general_two_relations import draw14_bounds
from wall1_rank_five_code import code_ball_bound, weighted_code_bound
from wall1_triangular_third_relation import new_group_bound
from wall1_short_relation_shapes import equal_pair_sum_ball_bound, equal_pair_sum_alias_bound
from wall1_factorial_cumulants import difference_weights
from wall1_linear_remainder import remainder_weights


def triangular_envelopes(s,*,exclude_d44=False):
    from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count
    I, q, m, n, radius, mu = [s[k] for k in ('I', 'q', 'm', 'N', 'radius', 'mu')]
    anchor = (equal_pair_sum_ball_bound(radius**2, n, 3)
              +equal_pair_sum_alias_bound(radius**2, n, 3, q))/q**(4*m)
    triple = code_ball_bound(s)
    same_rank = code_ball_bound(s,1)
    larger_codes = {t: code_ball_bound(s,t) for t in range(3,19)}
    groups = {t: new_group_bound(radius**2, n, t, q)/q**(m*(t-1)) for t in range(3, 20)}
    result = {}
    s['triangular_extension_terms'] = {}
    for h in range(14, 25):
        result[h, 4] = comb(h, 6)*75*anchor*q**(3*(h-6))
        same_rank_cover = (comb(h,6)*75*weighted_code_bound(s,1,
                           sum(comb(4,a)*q**(a-1) for a in range(3,5)),same_rank)*q**(3*(h-7)))
        result[h,4] = min((result[h,4],same_rank_cover),key=lambda v:v.b)
        # A proper rank-four six-point anchor already has nullity two. If the
        # whole connected support also had nullity two, all outside points
        # would be coloops, contradicting connectedness.
        result[h, h-2] = I(0)
        for r in range(5, h-2):
            total = I(0)
            small = I(0)
            for t in range(2, min(r-3, h-6)+1):
                extra = r-t-3
                joint = triple if t == 2 else anchor*groups[t]
                if t >= 3:
                    joint = min((joint, larger_codes[t]), key=lambda v: v.b)
                coefficients = sum(comb(4, a)*q**(t+a-2) for a in range(max(1, 4-t), 5))
                choices = comb(h, 6)*75*comb(h-6, t)*comb(h-6-t, extra)
                charge = (choices*weighted_code_bound(s,t,coefficients,joint,
                          exclude_three_new_four=exclude_d44)*mu**extra
                          *q**((r-1)*(h-r-3))/(extra+1))
                s['triangular_extension_terms'][h,r,t]=charge
                if t == 2:
                    small += charge
                else:
                    total += charge
            parallel = (comb(h,6)*75*anchor*mu**(r-4)
                        *parallel_completion_count(h-6, r-4, 4, q))
            marked = (comb(h,6)*75*comb(h-6,2)
                      *weighted_code_bound(s,2,sum(comb(4,a)*q**a for a in range(2,5)),triple)*mu**(r-5)
                      *marked_parallel_completion_count(h-8,r-5,4,q))
            if r==5:
                from wall1_parallel_contraction import single_class_pair_completion_count
                completion=single_class_pair_completion_count(h-8,4,q)
                counted_once=(comb(h,6)*75*comb(h-6,2)
                    *weighted_code_bound(s,2,sum(comb(4,a)*q**a for a in range(2,5)),triple)
                    *I(completion.numerator)/completion.denominator)
                marked=min((marked,counted_once),key=lambda v:v.b)
            result[h, r] = total+min((small, parallel, marked), key=lambda v: v.b)
            if r==5:
                from wall1_four_pair_extension import rank_five_envelope
                residual_completion=min((I(q**(4*(h-8))),I(completion.numerator)/completion.denominator),key=lambda v:v.b)
                residual=(comb(h,6)*75*comb(h-6,2)*residual_completion
                    *weighted_code_bound(s,2,sum(comb(4,a)*q**a for a in range(2,5)),triple,
                                         exclude_two_point_d32=True))
                result[h,r]=min((result[h,r],residual+rank_five_envelope(s,h)),key=lambda v:v.b)
    return result


def actual_parameters():
    with contextlib.redirect_stdout(io.StringIO()):
        from wall1_rank_five_code import actual_parameters as known_fourteen
        s, baseline, _ = known_fourteen()
        _, full, strata = draw14_bounds()
        _, _, free = draw14_bounds(exclude_triangular_anchors=True)
        _, _, no_double = draw14_bounds(exclude_double_short_anchors=True)
        _, _, no_twenty = draw14_bounds(exclude_double_short_anchors=True,exclude_four_six_twenty=True)
        _, _, no_twenty_three = draw14_bounds(exclude_double_short_anchors=True,
            exclude_four_six_twenty=True,exclude_four_six_twenty_three=True)
        _, _, no_girth_three_twenty = draw14_bounds(exclude_three_circuit_twenty=True)
        _, _, no_five_twenty = draw14_bounds(exclude_three_circuit_twenty=True,
                                            exclude_five_twenty=True)
        _, _, no_nine_twenty_seven = draw14_bounds(exclude_nine_twenty_seven=True)
        _, _, no_six_ten_thirty_two = draw14_bounds(exclude_nine_twenty_seven=True,
            exclude_six_ten_thirty_two=True)
        _, _, no_five_fifteen = draw14_bounds(exclude_three_circuit_twenty=True,
            exclude_five_twenty=True,exclude_five_fifteen=True)
        _, _, no_six_twenty_three = draw14_bounds(exclude_three_circuit_twenty=True,
            exclude_five_twenty=True,exclude_five_fifteen=True,exclude_six_twenty_three=True)
        _, _, no_twenty_four = draw14_bounds(exclude_double_short_anchors=True,
            exclude_four_six_twenty=True,exclude_four_six_twenty_three=True,
            exclude_four_six_twenty_four=True)
        _, _, no_seven_six = draw14_bounds(exclude_double_short_anchors=True,
            exclude_four_six_twenty=True,exclude_four_six_twenty_three=True,
            exclude_four_six_twenty_four=True,exclude_seven_four_six=True)
        _, _, no_ten_eight = draw14_bounds(exclude_double_short_anchors=True,
            exclude_four_six_twenty=True,exclude_four_six_twenty_three=True,
            exclude_four_six_twenty_four=True,exclude_seven_four_six=True,
            exclude_ten_twenty_eight=True)
        _, _, no_eleven_thirty_one = draw14_bounds(exclude_double_short_anchors=True,
            exclude_four_six_twenty=True,exclude_four_six_twenty_three=True,
            exclude_four_six_twenty_four=True,exclude_seven_four_six=True,
            exclude_ten_twenty_eight=True,exclude_eleven_thirty_one=True)
        _, _, no_six_d24 = draw14_bounds(exclude_double_short_anchors=True,
            exclude_four_six_twenty=True,exclude_four_six_twenty_three=True,
            exclude_four_six_twenty_four=True,exclude_seven_four_six=True,
            exclude_ten_twenty_eight=True,exclude_eleven_thirty_one=True,
            exclude_six_d24=True)
    I, iv, mu = s['I'], s['iv'], s['mu']
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0)) for poly in difference_weights(12)]
    linear = remainder_weights(weights, baseline, 15)
    triangular = triangular_envelopes(s)
    unrestricted_extension_terms=s['triangular_extension_terms']
    from wall1_d44_extension import envelopes as d44_envelopes
    without_d44=triangular_envelopes(s,exclude_d44=True)
    s['triangular_without_d44_extension_terms']=s['triangular_extension_terms']
    s['triangular_extension_terms']=unrestricted_extension_terms
    d44=d44_envelopes(s)
    s['d44_cover_parts']={key:(triangular[key],without_d44[key],d44[key])
                          for key in triangular if key in d44}
    for key,(old,remainder,anchor) in s['d44_cover_parts'].items():
        triangular[key]=min((old,remainder+anchor),key=lambda v:v.b)
    from wall1_other_short_anchors import other_envelopes
    # D44 shared-two-point codes contain a triangular anchor, whose complete
    # cover is already included in every expression using `other` below.
    other = other_envelopes(s,exclude_triangular=True)
    from wall1_twenty_plane import envelopes as twenty_envelopes
    twenty = twenty_envelopes(s,exclude_two_short=True)
    from wall1_twenty_three_plane import envelopes as twenty_three_envelopes
    twenty_three = twenty_three_envelopes(s)
    from wall1_girth_three_twenty import envelopes as girth_three_twenty_envelopes
    girth_three_twenty=girth_three_twenty_envelopes(s)
    five_twenty=girth_three_twenty_envelopes(s,anchor_size=5)
    five_fifteen=girth_three_twenty_envelopes(s,anchor_size=5,determinant=15)
    six_twenty_three=girth_three_twenty_envelopes(s,anchor_size=6,determinant=23)
    from wall1_nine_twenty_seven import envelopes as nine_twenty_seven_envelopes
    nine_twenty_seven=nine_twenty_seven_envelopes(s)
    from wall1_six_ten_anchor import rank_eight_envelopes
    six_ten_thirty_two=rank_eight_envelopes(s)
    from wall1_six_ten_rank_nine import envelopes as six_ten_rank_nine_envelopes
    six_ten_rank_nine=six_ten_rank_nine_envelopes(s)
    from wall1_six_ten_rank_ten import envelopes as six_ten_rank_ten_envelopes
    six_ten_rank_ten,_=six_ten_rank_ten_envelopes(s)
    from wall1_six_ten_higher_rank import envelopes as six_ten_higher_rank_envelopes
    six_ten_higher_rank,_=six_ten_higher_rank_envelopes(s)
    from wall1_six_ten_all_rank import envelopes as six_ten_all_rank_envelopes
    six_ten_all_rank,_=six_ten_all_rank_envelopes(s)
    from wall1_twenty_four_plane import envelopes as twenty_four_envelopes
    twenty_four=twenty_four_envelopes(s)
    from wall1_seven_twenty_three import envelopes as seven_six_envelopes
    seven_six=seven_six_envelopes(s)
    ten_eight=seven_six_envelopes(s,anchor_size=10)
    eleven_thirty_one=seven_six_envelopes(s,anchor_size=11)
    from wall1_six_d24_anchor import envelopes as six_d24_envelopes
    six_d24=six_d24_envelopes(s)
    refined = {}
    refined_strata = {}
    for h in range(15, 25):
        remaining = I(0)
        no_double_remaining = I(0)
        triangle_charge = I(0)
        for (size, r, c), old in strata.items():
            if size != h or r < 3:
                continue
            value = old
            if c==6 and r>=7:
                value=min((value,no_nine_twenty_seven[h,r,c]+nine_twenty_seven[h,r]),key=lambda v:v.b)
                if r==8:
                    value=min((value,no_six_ten_thirty_two[h,r,c]+nine_twenty_seven[h,r]
                               +six_ten_thirty_two[h]),key=lambda v:v.b)
                if r==9:
                    value=min((value,no_six_ten_thirty_two[h,r,c]+nine_twenty_seven[h,r]
                               +six_ten_rank_nine[h]),key=lambda v:v.b)
                if r==10:
                    value=min((value,no_six_ten_thirty_two[h,r,c]+nine_twenty_seven[h,r]
                               +six_ten_rank_ten[h]),key=lambda v:v.b)
                if r in (11,12):
                    value=min((value,no_six_ten_thirty_two[h,r,c]+nine_twenty_seven[h,r]
                               +six_ten_higher_rank[h,r]),key=lambda v:v.b)
                if r>=13 and (h,r) in six_ten_all_rank:
                    value=min((value,no_six_ten_thirty_two[h,r,c]+nine_twenty_seven[h,r]
                               +six_ten_all_rank[h,r]),key=lambda v:v.b)
            if c==3 and r>=4:
                value=min((value,no_girth_three_twenty[h,r,c]+girth_three_twenty[h,r]),key=lambda v:v.b)
                value=min((value,no_five_twenty[h,r,c]+girth_three_twenty[h,r]+five_twenty[h,r]),
                          key=lambda v:v.b)
                value=min((value,no_five_fifteen[h,r,c]+girth_three_twenty[h,r]
                           +five_twenty[h,r]+five_fifteen[h,r]),key=lambda v:v.b)
                value=min((value,no_six_twenty_three[h,r,c]+girth_three_twenty[h,r]
                           +five_twenty[h,r]+five_fifteen[h,r]+six_twenty_three[h,r]),key=lambda v:v.b)
            if c == 4 and r >= 4:
                candidate = free[h, r, c]+triangular[h, r]
                if candidate.b < old.b:
                    value = candidate
                all_short = no_double[h, r, c]+triangular[h, r]+other[h, r]
                if all_short.b < value.b:
                    value = all_short
                extended = no_twenty[h,r,c]+triangular[h,r]+other[h,r]+twenty[h,r]
                if extended.b < value.b:
                    value = extended
                extended_three=(no_twenty_three[h,r,c]+triangular[h,r]+other[h,r]
                                +twenty[h,r]+twenty_three[h,r])
                if extended_three.b < value.b:
                    value=extended_three
                extended_four=(no_twenty_four[h,r,c]+triangular[h,r]+other[h,r]
                               +twenty[h,r]+twenty_three[h,r]+twenty_four[h,r])
                if extended_four.b<value.b:
                    value=extended_four
                extended_seven=(no_seven_six[h,r,c]+triangular[h,r]+other[h,r]
                                +twenty[h,r]+twenty_three[h,r]+twenty_four[h,r]+seven_six[h,r])
                if extended_seven.b<value.b:
                    value=extended_seven
                extended_ten=(no_ten_eight[h,r,c]+triangular[h,r]+other[h,r]
                              +twenty[h,r]+twenty_three[h,r]+twenty_four[h,r]
                              +seven_six[h,r]+ten_eight[h,r])
                if extended_ten.b<value.b:
                    value=extended_ten
                extended_eleven=(no_eleven_thirty_one[h,r,c]+triangular[h,r]+other[h,r]
                    +twenty[h,r]+twenty_three[h,r]+twenty_four[h,r]
                    +seven_six[h,r]+ten_eight[h,r]+eleven_thirty_one[h,r])
                value=min((value,extended_eleven),key=lambda v:v.b)
                extended_six_d24=(no_six_d24[h,r,c]+triangular[h,r]+other[h,r]
                    +twenty[h,r]+twenty_three[h,r]+twenty_four[h,r]
                    +seven_six[h,r]+ten_eight[h,r]+eleven_thirty_one[h,r]+six_d24[h,r])
                value=min((value,extended_six_d24),key=lambda v:v.b)
                if h==17 and r in (6,8,9):
                    covers={
                        'original':{'unrestricted':old},
                        'triangle':{'remaining':free[h,r,c],'triangle':triangular[h,r]},
                        'two-four':{'remaining':no_double[h,r,c],'triangle':triangular[h,r],
                                    'other-two-four':other[h,r]},
                    }
                    added={'triangle':triangular[h,r],'other-two-four':other[h,r]}
                    for name,residual,label,charge in (
                        ('D20-eight',no_twenty,'D20-eight',twenty[h,r]),
                        ('D23-nine',no_twenty_three,'D23-nine',twenty_three[h,r]),
                        ('D24-eight',no_twenty_four,'D24-eight',twenty_four[h,r]),
                        ('D23-seven',no_seven_six,'D23-seven',seven_six[h,r]),
                        ('D28-ten',no_ten_eight,'D28-ten',ten_eight[h,r]),
                        ('D31-eleven',no_eleven_thirty_one,'D31-eleven',eleven_thirty_one[h,r]),
                        ('D24-six',no_six_d24,'D24-six',six_d24[h,r])):
                        added[label]=charge
                        covers[name]={'remaining':residual[h,r,c],**added}
                    totals={name:sum(parts.values(),I(0)) for name,parts in covers.items()}
                    winner=min(totals,key=lambda name:totals[name].b)
                    # The diagnostic must reconstruct the actual selected envelope.
                    assert totals[winner].a<=value.b and value.a<=totals[winner].b
                    coefficient=s['normalizer']*linear[h]
                    print('selected-cover',h,r,c,winner,flush=True)
                    for name,total in totals.items():
                        print('cover-total',name,'weighted log10',iv.log10(coefficient*total),flush=True)
                    for name,part in covers[winner].items():
                        print('selected-cover-part',name,'weighted log10',
                              iv.log10(coefficient*part),flush=True)
                triangle_charge += min((old, triangular[h, r]), key=lambda v: v.b)
            remaining += value
            refined_strata[h,r,c] = value
            no_double_remaining += no_double[h, r, c]
        refined[h] = min((full[h], s['base'][h]+remaining), key=lambda v: v.b)
        coefficient = s['normalizer']*linear[h]
        if h == 15:
            assert coefficient*triangle_charge < I('1.88e-13')
            assert coefficient*remaining < I('4.51e7')
        print('size', h, 'full residual log10', iv.log10(coefficient*remaining),
              'triangular part log10', iv.log10(coefficient*triangle_charge),
              'no-double-short diagnostic log10', iv.log10(coefficient*no_double_remaining), flush=True)
    largest = sorted(((v.b, r, c, v) for (h, r, c), v in no_double.items()
                      if h == 15 and r >= 3), reverse=True)
    for _, r, c, v in largest[:5]:
        print('size-15 no-double-short rank/girth', r, c, 'weighted log10',
              iv.log10(s['normalizer']*linear[15]*v), flush=True)
    for diagnostic_size in (16,17):
        largest = sorted(((v.b,r,c,v) for (h,r,c),v in refined_strata.items()
                           if h==diagnostic_size),reverse=True)
        for _,r,c,v in largest[:5]:
            print('refined size/rank/girth',diagnostic_size,r,c,'weighted log10',
                  iv.log10(s['normalizer']*linear[diagnostic_size]*v),flush=True)
    assert s['normalizer']*remainder_weights(weights, baseline, 14)[14]*triangular[14, 5] < I('1.151e-28')
    print('OPEN: sizes17..24 and later histories do not meet the remaining residual budget.')
    return s, refined


if __name__ == '__main__':
    actual_parameters()
