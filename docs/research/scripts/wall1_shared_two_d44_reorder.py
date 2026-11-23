"""Exact D44 basis permutation and a full-tail numerical refinement.

Only the short theta product changes; the existing cutoff-29 tail and every
periodic term are retained. No anchor family is removed.
"""
import contextlib
import io
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant
from wall1_shared_two_point_codes import COUNTS
from wall1_orthogonal_third_code import code_ball_bound


def certify():
    a=(1,1,-1,-1,0,0,0,0,0)
    b=(1,0,0,0,1,-1,-1,0,0)
    checked=0
    for c in norm_rows(9,4):
        if not all(c[7:]):continue
        rows=(a,b,c)
        gram=[[sum(x*y for x,y in zip(u,v)) for v in rows] for u in rows]
        d=determinant(*gram)
        if d!=44:continue
        pair=next((i,j) for i,j in combinations(range(3),2) if abs(gram[i][j])==2)
        u,v=(rows[i] for i in pair)
        assert sum(bool(x and y) for x,y in zip(u,v))==2
        assert sum(bool(x or y) for x,y in zip(u,v))==6
        third=tuple(x-(1 if gram[pair[0]][pair[1]]>0 else -1)*y for x,y in zip(u,v))
        assert sum(third)==0 and sum(x*x for x in third)==4
        assert any(abs(u[i]*v[j]-u[j]*v[i])==1 for i,j in combinations(range(9),2))
        cols=list(zip(*rows))
        assert any(abs(determinant(*(cols[i] for i in ix)))==1
                   for ix in combinations(range(9),3))
        # After selecting the dot +/-2 pair, leading Gram minors are 4,12,44.
        checked+=1
    assert checked==20
    print('Certified20 D44 rows: unit minor; GS squared lengths4,3,11/3.')


def reordered_bound(s):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    size,rank=9,6
    beta=I(rank*n)/(2*size*R**2)
    a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(4*alpha)*theta(3*alpha)*theta(I(11)/3*alpha)
    tail=iv.exp(-I(29**2)*alpha/2)*theta(alpha/2)**3
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(size,j)*delta**j for j in range(1,size+1)),I(0))
    gaussian=(iv.pi/beta)**(I(size)/2)*((short+tail)/q**3+periodic)
    return iv.exp(size*beta*R**2)*gaussian**n/q**(rank*m)


def main():
    certify()
    from wall1_rank_five_code import actual_parameters
    with contextlib.redirect_stdout(io.StringIO()):s,_,_=actual_parameters()
    I,iv=s['I'],s['iv']
    parts={d:count*code_ball_bound(s,shared=True,new_positions=2,
            shared_two_point_determinant=d) for d,count in COUNTS.items()}
    old=sum(parts.values(),I(0));new44=20*reordered_bound(s)
    selected44=min((parts[44],new44),key=lambda v:v.b)
    new=selected44+sum((v for d,v in parts.items() if d!=44),I(0))
    for d,v in parts.items():print('D',d,'old-log10',iv.log10(v))
    print('D44 reordered full-tail log10',iv.log10(new44))
    print('rare total old log10',iv.log10(old))
    print('rare total refined log10',iv.log10(new))
    print('rare ratio log10',iv.log10(new/old))
    without=sum((v for d,v in parts.items() if d!=44),I(0))
    print('conditional no-triangle rare log10',iv.log10(without))
    print('conditional no-triangle rare ratio log10',iv.log10(without/old))


if __name__=='__main__':main()
