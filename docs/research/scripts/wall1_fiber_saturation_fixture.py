"""Exact nonsaturation of J={0} nearest-input witnesses, with genuine ties.

Toy radius only; no production radius or reachable-history assertion.
K basis: e1=(1/10,0), e2=(7/250,12/125); M=5K; fresh mark u=0.
Nearest and winner ties use lexicographic integer basis coordinates.
"""
from fractions import Fraction as F
from itertools import product

Q=5
B2=F(1,20)


def norm2(x,y):
    return (F(x*x+y*y)+F(14,25)*x*y)/100


def physical(x,y):
    return F(x,10)+F(7*y,250),F(12*y,125)


def projected2(y):
    return F(144,15625)*y*y


def main():
    # Gram eigenvalue min=(1-7/25)/100=9/1250.
    eigenlower=F(9,1250)
    centered_cap=F(256,2500)
    assert centered_cap/eigenlower==F(128,9)<16
    # Every residue has a centered |x|,|y|<=2 representative with norm
    # at most centered_cap. Every nearest representative therefore lies
    # in [-3,3]^2. The following enumeration is exhaustive.
    nearest={}
    physical_nearest={}
    for x,y in product(range(-3,4),repeat=2):
        mark=(x%Q,y%Q)
        key=(norm2(x,y),x,y)
        if mark not in nearest or key<nearest[mark]:
            nearest[mark]=key
        pkey=(norm2(x,y),*physical(x,y),x,y)
        if mark not in physical_nearest or pkey<physical_nearest[mark]:
            physical_nearest[mark]=pkey
    assert len(nearest)==25
    assert all(norm2(x,y)<=centered_cap for _,x,y in nearest.values())
    assert all((entry[1],entry[2])==physical_nearest[v][-2:]
               for v,entry in nearest.items())

    # W_0=(5K,0)+Z(0,1). A candidate of norm^2<=1/4 must have j=0,
    # and x^2+y^2<=625/18<36. Thus [-5,5]^2 at height zero is complete.
    assert F(1,4)/eigenlower==F(625,18)<36
    winners=[(norm2(x,y),x,y,0)
             for x,y in product(range(-5,6),repeat=2)
             if (x or y) and x%Q==0 and y%Q==0]
    winner=min(winners)
    assert winner==(F(1,4),-5,0,0)
    assert norm2(5,0)==norm2(0,5)==F(1,4)

    assert nearest[3,3]==(F(241,2500),-2,3)
    assert norm2(-2,3)==norm2(3,-2)  # genuine nearest tie
    assert nearest[0,3]==(F(1,25),0,-2)
    assert projected2(3)==F(1296,15625)>B2
    assert projected2(-2)==F(576,15625)<B2

    hit={v for v,(_,x,y) in nearest.items() if projected2(y)<=B2}
    assert hit==set(nearest)-{(3,3)}
    kernel={(x,0) for x in range(Q)}
    saturated={((x+k)%Q,y) for x,y in hit for k,_ in kernel}
    assert saturated==set(nearest)
    # After horizontal projection, QW has spacing 5*(12/125) in the
    # remaining original direction, and integer spacing in height.
    # Thus f kills precisely the first coordinate; the quotient has 5 marks.
    true_distances={v:projected2((v[1]+2)%Q-2) for v in nearest}
    assert max(true_distances.values())==F(576,15625)<B2
    print('Actual shortest winner:',winner)
    print('All25 nearest marks certified in [-3,3]^2; coefficient/physical lex agree.')
    print('Unsaturated witness hits:',len(hit),'missing:',sorted(set(nearest)-hit))
    print('Kernel size:',len(kernel),'saturated hits:',len(saturated))
    print('Witness void bound = 1/25; saturated bound = actual outgoing void = 0.')
    print('Exact fixture checks passed; ties and arbitrary toy radius are essential scope.')


if __name__=='__main__':
    main()
