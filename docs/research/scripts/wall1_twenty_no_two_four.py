"""Conditional D20 one-point cover without six/seven-position two-four anchors."""
import contextlib
import io
from collections import Counter
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant
from wall1_twenty_plane import code_bound
from wall1_twenty_dependent_codes import UPPER_COUNTS


def certify():
    a=(1,1,-1,-1,0,0,0,0,0)
    bs=((1,1,0,0,1,-1,-1,-1,0),(1,0,-1,0,1,1,-1,-1,0))
    counts=[]
    for b in bs:
        retained=Counter();removed=Counter()
        for v in norm_rows(9,4):
            if not v[8]:continue
            columns=list(zip(a,b,v))
            minors={ix:determinant(*(columns[i] for i in ix)) for ix in combinations(range(9),3)}
            assert any(abs(x)==1 for x in minors.values())
            assert max(map(abs,minors.values()))<7
            if not all(any(minors[ix] for ix in combinations(comp,3))
                       for comp in combinations(range(9),6)):
                continue
            x=sum(z*w for z,w in zip(a,v)); y=sum(z*w for z,w in zip(b,v))
            d=80-6*x*x+4*x*y-4*y*y
            overlap=sum(bool(z and w) for z,w in zip(a,v))
            if overlap:
                assert overlap in (1,2)
                assert (overlap==1 and abs(x)==1) or (overlap==2 and abs(x) in (0,2))
                assert any(abs(a[i]*v[j]-a[j]*v[i])==1 for i,j in combinations(range(9),2))
                removed[d]+=1
            elif d==44:
                assert abs(y)==3
                w=tuple(z-(1 if y>0 else -1)*t for z,t in zip(b,v))
                assert sum(w)==0 and sum(z*z for z in w)==4
                assert abs(sum(z*t for z,t in zip(a,w)))==2
                assert sum(bool(z or t) for z,t in zip(a,w))==6
                assert any(abs(a[i]*w[j]-a[j]*w[i])==1 for i,j in combinations(range(9),2))
                removed[d]+=1
            else:
                assert d==76
                retained[d]+=1
        counts.append(retained[76])
        print('retained',dict(retained),'removed',dict(sorted(removed.items())))
    assert counts==[9,8]
    print('Certified uniform conditional bound:9 determinant76 codes; full rank3 unit minors.')


def main():
    certify()
    from wall1_rank_five_code import actual_parameters
    from wall1_factorial_cumulants import difference_weights
    from wall1_linear_remainder import remainder_weights
    with contextlib.redirect_stdout(io.StringIO()):s,baseline,_=actual_parameters()
    I,iv,q,mu=s['I'],s['iv'],s['q'],s['mu']
    weights=[sum((I(abs(v.numerator))/v.denominator*mu**d for d,v in enumerate(p)),I(0)) for p in difference_weights(12)]
    factor=s['normalizer']*remainder_weights(weights,baseline,15)[17]
    coeff=sum(comb(6,a)*q**(a-1) for a in range(3,7))
    old=comb(17,8)*3360*code_bound(s)*q**45
    parts={d:c*code_bound(s,1,one_point_determinant=d) for d,c in UPPER_COUNTS.items()}
    regular=coeff*code_bound(s,1,no_new_norm_four=True)
    unrestricted=coeff*code_bound(s,1)
    rare=sum(parts.values(),I(0))
    revised=9*code_bound(s,1,one_point_determinant=76)
    prefactor=comb(17,8)*3360*q**40
    for d,v in parts.items():print('one-point rare D',d,'weighted log10',iv.log10(factor*prefactor*v))
    for name,v in [('same-rank-old',old),('onepoint-regular',prefactor*regular),
                   ('onepoint-selected',prefactor*min((unrestricted,rare+regular),key=lambda x:x.b)),
                   ('conditional-onepoint-rare',prefactor*revised),
                   ('conditional-selected',min((old,prefactor*min((unrestricted,revised+regular),key=lambda x:x.b)),key=lambda x:x.b))]:
        print(name,iv.log10(factor*v))


if __name__=='__main__':main()
