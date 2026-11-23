"""Exact multiplicity identities for the rank-one quotient marked-pair cover."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from wall1_parallel_contraction import single_class_pair_completion_count,marked_parallel_completion_count


def checks():
    subsets=0
    for size in range(2,11):
        for k in range(2,size+1):
            for members in combinations(range(size),k):
                mass=sum((F(1,comb(k,2)) for _ in combinations(members,2)),F(0))
                assert mass==1
                subsets+=1
    identities=0
    for q in (3,7,3329):
        for d in (4,5):
            for n in range(19):
                value=single_class_pair_completion_count(n,d,q)
                direct=sum(comb(n+2,k)*q**(d*(k-2)+(d-1)*(n+2-k)) for k in range(2,n+3))
                assert comb(n+2,2)*value==direct
                previous=marked_parallel_completion_count(n,0,d,q)
                assert F(previous,comb(n+2,2))<=value<=previous
                identities+=1
    print(f'Passed{subsets} subset multiplicity checks and{identities} exact weighted count identities.')


if __name__=='__main__':checks()
