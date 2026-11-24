"""Exact first moment on a genuine old-minimum gate; no production claim."""
from fractions import Fraction as F
from itertools import product


def short_vectors(d):
    # c=3/2: norm^2<c^2 iff integral norm^2 is 1 or 2.
    return tuple(z for z in product((-1,0,1),repeat=d)
                 if 0<sum(x*x for x in z)<=2)


def main():
    q=3
    vectors=tuple(product(range(q),repeat=2))
    candidates=tuple(tuple(sign if j==i else 0 for j in range(3))
                     for i in range(3) for sign in (-1,1))
    old_short=short_vectors(3)
    next_short=short_vectors(4)
    selected=nonzero_pairs=hit_sum=tail=0
    for a in vectors:
        def label(z):
            return tuple((z[i]-a[i]*z[2])%q for i in range(2))
        eligible=not any(not any(label(z)) for z in old_short)
        assert eligible==all(a)
        if not eligible:
            continue
        selected+=1
        labels=tuple(label(z) for z in candidates)
        assert all(any(v) for v in labels)
        assert len(set(labels))==6
        for u in vectors:
            has_short=any(all((z[i]-a[i]*z[2]-u[i]*z[3])%q==0 for i in range(2))
                          for z in next_short)
            z=sum(v==u for v in labels)
            if any(u):
                nonzero_pairs+=1
                hit_sum+=z
                assert (not has_short)==(z==0)
            else:
                assert has_short
            tail+=not has_short
    a_mass=F(selected,9)
    m0=F(nonzero_pairs,81)
    m1=F(hit_sum,81)
    assert F(1)+1<F(3,2)**2 # R^2+height^2<c^2
    assert m0==a_mass*F(8,9)==F(32,81)
    assert m1==a_mass*F(6,9)==F(24,81)
    assert m1==m0*6*F(1,8)
    assert F(tail,81)==F(8,81)
    print('Complete old and next short-vector lists:',len(old_short),len(next_short))
    print('Eligible old maps:',selected,'out of 9; all 81 old/fresh pairs covered by gate and enumeration.')
    print('M0,M1:',m0,m1,'first reference error:',m1-m0*6*F(1,8))
    print('Exact joint next tail for this small fixture:',F(tail,81))
    print('Geometric nonzero-label and exact first-moment checks passed; production history remains open.')


if __name__=='__main__':
    main()
