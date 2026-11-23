"""Norm-ten rows covering nine new positions with a four-circuit."""
from wall1_rare_second_line import norm_rows


def checks():
    unit=[v for v in norm_rows(10,10) if all(abs(x)==1 for x in v)]
    assert len(unit)==126
    outside=[]
    for old in range(4):
        for v in unit:
            row=[0]*4+list(v[1:])
            row[old]=v[0]
            outside.append(tuple(row))
    assert len(set(outside))==504
    first_four=list(norm_rows(4,4,minimum_support=4))
    first_ten=list(norm_rows(4,10,minimum_support=4))
    assert len(first_four)==3 and len(first_ten)==12
    for a in first_four:
        for b in outside:
            assert abs(sum(x*y for x,y in zip(a,b)))==1
            assert 4*10-sum(x*y for x,y in zip(a,b))**2==39
    for a in first_ten:
        for b in outside:
            assert abs(sum(x*y for x,y in zip(a,b)))<=2
    print('Passed1512 four/ten Gram checks and6048 old-ten/outside-ten inner-product checks.')


if __name__=='__main__':checks()
