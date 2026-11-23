"""Integer projection and short-row shapes for a three-circuit with large extension."""
from fractions import Fraction as F
from itertools import product
from wall1_rare_second_line import norm_rows


def finite_checks():
    a=(2,-1,-1)
    for v in product(range(-4,5),repeat=3):
        dot=sum(x*y for x,y in zip(a,v))
        D=F(sum(x*x for x in v))-F(dot*dot,6)
        explicit=F((v[1]-v[2])**2,2)+F(sum(v)**2,3)
        assert D==explicit and (D==0 or D>=F(1,3))
    assert len(list(norm_rows(3,6,minimum_support=3)))==3
    assert not list(norm_rows(3,8,minimum_support=3))
    for norm in (6,8):
        rows=list(norm_rows(norm,norm,minimum_support=3))
        for row in rows:
            support=sum(bool(x) for x in row)
            if norm==6:assert support in (3,6)
            else:assert support in (5,8)
    print('Passed729 projection identities, three norm-six directions, and all norm-six/eight shapes.')


if __name__=='__main__':
    finite_checks()
