"""Exact one-point extension strata for all five balanced triangular patterns."""
from collections import Counter
from itertools import combinations
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant

UPPER_COUNTS={32:24,48:6}


def exact_counts():
    patterns=Counter()
    for a in balanced_rows((0,1,2,3),7):
        for b in balanced_rows((2,3,4,5),7):
            dot=sum(x*y for x,y in zip(a,b))
            if abs(dot)!=2:
                continue
            total=0
            valid=Counter()
            for v in norm_rows(7,4):
                if not v[-1]:
                    continue
                total+=1
                x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
                gram=48-4*x*x+2*dot*x*y-4*y*y
                columns=list(zip(a,b,v))
                minors={indices:determinant(*(columns[i] for i in indices))
                        for indices in combinations(range(7),3)}
                assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
                if all(any(minors[indices] for indices in combinations(complement,3))
                       for complement in combinations(range(7),4)):
                    valid[gram]+=1
            assert total==60
            assert valid in ({32:24},{32:18,48:6})
            patterns[tuple(sorted(valid.items()))]+=1
            assert all(count<=UPPER_COUNTS[d] for d,count in valid.items())
    assert patterns=={((32,24),):1,((32,18),(48,6)):4}
    print('Passed five triangular patterns, 300 short lines and 35 complements per line.')
    print('Uniform exceptional Gram counts:',UPPER_COUNTS)


if __name__=='__main__':
    exact_counts()
