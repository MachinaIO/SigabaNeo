"""Exact norm-four/norm-six witness counts on seven positions."""
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows
from collections import defaultdict


def exact_counts():
    C = (0,1,2,3)
    for q in (7,17,3329):
        counts = {1:0,2:0,3:0}
        for first in balanced_rows(C,7):
            for second in norm_rows(7,6):
                if not all(x or y for x,y in zip(first,second)):
                    continue
                dot = sum(x*y for x,y in zip(first,second))
                assert abs(dot) in (1,3)
                if abs(dot) == 3:
                    sign = 1 if dot>0 else -1
                    assert sum((b-sign*a)**2 for a,b in zip(first,second)) == 4
                    continue
                words = [second]+[tuple((a+t*b)%q for a,b in zip(first,second))
                                  for t in (0,1,q-1)]
                supports = [tuple(i for i,x in enumerate(word) if x%q) for word in words]
                assert min(map(len,supports)) == 4
                assert [support for support in supports if len(support)==4] == [C]
                for overlap in (1,2,3):
                    target = tuple(range(overlap))+(4,5,6)
                    if target in supports:
                        counts[overlap] += 1
        assert counts == {1:0,2:14,3:42}
        print(f'q={q}: prescribed-overlap witness counts {counts}.')


def eight_point_counts():
    for q in (7,17,3329):
        for norm, expected in ((6,{1:0,2:30,3:42}), (8,{1:60,2:13,3:60})):
            codes = {a:set() for a in (1,2,3)}
            determinants = defaultdict(set)
            for first in balanced_rows((0,1,2,3),8):
                for second in norm_rows(8,norm):
                    if not all(second[4:]):
                        continue
                    inverse = pow(second[4]%q,-1,q)
                    # Canonical representative modulo C: old coordinate zero
                    # vanishes and the first new coordinate equals one.
                    normalized = tuple((x*inverse-second[0]*inverse*y)%q
                                       for x,y in zip(second,first))
                    key = (first,normalized)
                    dot = sum(a*b for a,b in zip(first,second))
                    determinant = 4*norm-dot*dot
                    critical = {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}
                    for scalar in critical:
                        support = tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
                        for a in codes:
                            if support == tuple(range(a)):
                                codes[a].add(key)
                                determinants[a,determinant].add(key)
            actual = {a:len(values) for a,values in codes.items()}
            assert actual == expected
            refined = {key:len(values) for key,values in determinants.items()}
            target = ({(2,20):16,(2,24):14,(3,24):42} if norm == 6 else
                      {(1,28):12,(1,31):48,(2,32):13,(3,28):12,(3,31):48})
            assert refined == target
            print(f'q={q}, eight-point norm {norm}: exact code counts {actual}.')
            if q == 3329:
                print('Gram determinant strata:',sorted(refined.items()))


def nine_point_counts():
    for q in (7,17,3329):
        by_norm={}
        for norm in (6,8):
            codes=defaultdict(set)
            for first in balanced_rows((0,1,2,3),9):
                for second in norm_rows(9,norm):
                    if not all(second[4:]):
                        continue
                    inverse=pow(second[4]%q,-1,q)
                    key=(first,tuple((x-second[0]*y)*inverse%q for x,y in zip(second,first)))
                    dot=sum(x*y for x,y in zip(first,second))
                    determinant=4*norm-dot*dot
                    critical={(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}
                    for scalar in critical:
                        support=tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
                        for overlap in (1,2,3):
                            if support==tuple(range(overlap)):
                                codes[overlap,determinant].add(key)
            target=({(1,23):30,(3,23):30} if norm==6 else
                    {(1,23):30,(3,23):30,(2,31):50,(3,31):150})
            assert {k:len(v) for k,v in codes.items()}==target
            by_norm[norm]=codes
        for overlap in (1,3):
            assert by_norm[6][overlap,23]==by_norm[8][overlap,23]
        print(f'q={q}: nine-point Gram strata and duplicate determinant-23 planes verified.')


def ten_point_counts():
    for q in (7,17,3329):
        codes=defaultdict(set)
        for first in balanced_rows((0,1,2,3),10):
            for second in norm_rows(10,8):
                if not all(second[4:]):continue
                dot=sum(x*y for x,y in zip(first,second))
                determinant=32-dot*dot
                inverse=pow(second[4]%q,-1,q)
                key=(first,tuple((x-second[0]*y)*inverse%q for x,y in zip(second,first)))
                for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}:
                    support=tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
                    for overlap in (1,2,3):
                        if support==tuple(range(overlap)):
                            codes[overlap,determinant].add(key)
        assert {k:len(v) for k,v in codes.items()}=={(2,28):55,(2,32):50,(3,32):150}
        print(f'q={q}: ten-position norm-eight Gram strata verified.')


def eleven_norm_ten_checks():
    checked=0
    for first in balanced_rows((0,1,2,3),11):
        for second in norm_rows(11,10):
            if not all(second[4:]) or not any(second[:4]):continue
            assert all(abs(x)<=1 for x in second)
            assert sum(bool(x) for x in second[:4])==3
            dot=sum(x*y for x,y in zip(first,second))
            assert abs(dot) in (1,3)
            if abs(dot)==3:
                sign=1 if dot>0 else -1
                assert sum((x-sign*y)**2 for x,y in zip(second,first))==8
            else:
                assert 40-dot*dot==39
            checked+=1
    assert checked==1512
    print('Passed1512 norm-ten witnesses; no other shape meets both old and seven new positions.')


def eleven_point_counts():
    for q in (7,17,3329):
        codes=defaultdict(set)
        for first in balanced_rows((0,1,2,3),11):
            for second in norm_rows(11,8):
                if not all(second[4:]):continue
                assert sum(bool(x) for x in second[:4])==1
                dot=sum(x*y for x,y in zip(first,second))
                assert abs(dot)==1
                inverse=pow(second[4]%q,-1,q)
                key=(first,tuple((x-second[0]*y)*inverse%q for x,y in zip(second,first)))
                for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}:
                    support=tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
                    for overlap in (1,2,3):
                        if support==tuple(range(overlap)):
                            codes[overlap,31].add(key)
        assert {k:len(v) for k,v in codes.items()}=={(1,31):105,(3,31):105}
        print(f'q={q}: eleven-position determinant31 counts verified.')


if __name__ == '__main__':
    exact_counts()
    eight_point_counts()
    nine_point_counts()
    ten_point_counts()
    eleven_point_counts()
    eleven_norm_ten_checks()
