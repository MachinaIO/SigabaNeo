"""Diagnose the actually selected rank-eight girth-four anchor addback."""
import contextlib,io
from wall1_general_two_relations import draw14_bounds
from wall1_other_short_anchors import other_envelopes

def main():
    with contextlib.redirect_stdout(io.StringIO()):
        s,_,_=draw14_bounds(exclude_double_short_anchors=True,exclude_four_six_twenty=True,
            exclude_four_six_twenty_three=True,exclude_four_six_twenty_four=True,
            exclude_seven_four_six=True,exclude_ten_twenty_eight=True,
            exclude_eleven_thirty_one=True)
        bounds=other_envelopes(s)
    iv=s['iv']
    total=bounds[17,8]
    print('rank8 actual other-two-four addback relative contributions')
    for key,value in s['other_anchor_terms'].items():
        if key[:2]==(17,8):print(key,iv.log10(value/total))
    candidate=s['size17_stratum_candidates'][8,4]
    print('raw remainder selected', {k:str(iv.log10(v)) for k,v in candidate.items()})
    terms={k:v for k,v in s['size17_two_relation_terms'].items() if k[:2]==(8,4)}
    for key,value in sorted(terms.items(),key=lambda kv:kv[1].b,reverse=True)[:6]:
        print('rawterm share',key,iv.log10(value/candidate['two']))
    from math import comb
    from wall1_orthogonal_third_code import code_ball_bound
    from wall1_short_relation_shapes import shared_four_ball_bound,shared_four_gaussian_bound
    from wall1_triangular_third_relation import new_group_bound
    I,q,m,n,R,mu=[s[k] for k in ('I','q','m','N','radius','mu')]
    anchor=(shared_four_ball_bound(R**2,n)+shared_four_gaussian_bound(R**2,n,q,aliases_only=True))/q**(5*m)
    for t in (3,4):
        extra=8-5-t+1
        ordinary=code_ball_bound(s,shared=True,new_positions=t)
        nofour=code_ball_bound(s,shared=True,new_positions=t,no_new_norm_four=True)
        group=new_group_bound(R**2,n,t,q)/q**(m*(t-1))
        joint=min((anchor*group,ordinary),key=lambda v:v.b)
        C=sum(comb(5,a)*q**(t+a-2) for a in range(max(1,4-t),6))
        rare=3*comb(7,4-t)*ordinary
        rest=C*nofour
        selected=min((C*joint,rare+rest),key=lambda v:v.b)
        charge=comb(17,7)*630*comb(10,t)*comb(10-t,extra)*selected*mu**extra*q**(7*(17-8-3))/(extra+1)
        if t==4:
            from wall1_shared_four_new_six import refined_bound
            improved,rare6,remainder6=refined_bound(s,C,selected)
            print('shared-t4-six improvement',iv.log10(improved/selected),'rare6/rest',iv.log10(rare6/remainder6))
            # Production already includes the new t4 split. Reconstruct the
            # previous complete envelope by replacing precisely that charge.
            previous_total=total+charge-charge*improved/selected
            print('complete rank8 other-anchor new/old',iv.log10(total/previous_total))
            assert iv.log10(improved/selected).b < -30
            assert iv.log10(total/previous_total).b < -2.79
        print('shared crossing',t,'relative to total',iv.log10(charge/total),'rare/rest',iv.log10(rare/rest),'split/old',iv.log10((rare+rest)/(C*joint)))
    return s

if __name__=='__main__':main()
