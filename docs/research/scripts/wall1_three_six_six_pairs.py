"""Exact H6 two-six coefficient charts with C=012 and S=old prefix+345."""
from collections import Counter, defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows


def support(v, q):
    return tuple(i for i,x in enumerate(v) if x % q)


def main():
    rows = list(norm_rows(6,6,minimum_support=3))
    fours = list(norm_rows(6,4,minimum_support=1))
    assert len(rows)==70 and len(fours)==45
    for q in (7,17,3329):
        codes, excluded = defaultdict(set), defaultdict(set)
        checked=0
        for a,b in combinations(rows,2):
            if not all(x or y for x,y in zip(a,b)):
                continue
            p=next(i for i in (3,4,5) if a[i] or b[i])
            first=tuple(b[p]*a[i]-a[p]*b[i] for i in range(6))
            if support(first,q)!=(0,1,2):
                continue
            f=tuple(x*pow(first[0]%q,-1,q)%q for x in first)
            dot=sum(x*y for x,y in zip(a,b)); d=36-dot*dot
            for overlap in (1,2):
                second=tuple(b[overlap]*a[i]-a[overlap]*b[i] for i in range(6))
                if support(second,q)!=tuple(range(overlap))+(3,4,5):
                    continue
                v=tuple((second[i]-second[0]*f[i])*
                        pow(second[3]%q,-1,q)%q for i in range(6))
                key=(f,v)
                if abs(dot)==4:
                    diff=tuple(x-(1 if dot>0 else -1)*y for x,y in zip(a,b))
                    assert sum(x*x for x in diff)==4
                    excluded[overlap,d].add(key)
                    continue
                assert d in (32,36)
                assert sorted((len(support(a,q)),len(support(b,q))))==[3,6]
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1
                           for i,j in combinations(range(6),2))
                classes=Counter((1,y*pow(x%q,-1,q)%q) if x else (0,1)
                                for x,y in zip(a,b))
                assert max(classes.values())==3
                for w in fours:
                    u=w[0]%q; z=w[3]%q
                    assert any((w[i]-u*f[i]-z*v[i])%q for i in range(6))
                codes[overlap,d].add(key)
                checked+=1
        actual={k:len(v) for k,v in sorted(codes.items())}
        bad={k:len(v) for k,v in sorted(excluded.items())}
        assert actual=={(1,36):1,(2,32):18,(2,36):1},actual
        assert bad=={(1,20):3,(2,20):3},bad
        assert checked==20
        for ov in (1,2):
            retained=set().union(*(v for (a,d),v in codes.items() if a==ov))
            rejected=set().union(*(v for (a,d),v in excluded.items() if a==ov))
            assert not retained.intersection(rejected)
        print(f'q={q}: retained={actual}; excluded={bad}; '
              'unit minors, girth3 and all balanced norm4 exclusions verified')


if __name__=='__main__':
    main()
