"""Exact selection bias after a fixed quotient stratum.

q=3, m=8, d=1; A ranges over all 3^8 columns. L_A consists of
(x,j) with x=A*j modulo 3. Fixed old winner is w=(-3e1,0), norm^2=9.
Every candidate that can beat/tie w has |j|<=3. At nonzero height,
coordinatewise centered residues uniquely minimize the horizontal norm.
A noncentered coordinate with nonzero residue raises its square by at
least 3, but cannot alter the selected/not-selected answer below: for a
column containing a zero residue, the centered height-one vector already
beats w; for an all-nonzero column, centered norm is 8 at heights +/-1,
and any noncentered lift has norm^2>=12. At multiples of 3, any nonzero
horizontal lift adds at least 9. Thus the finite test is complete.

The fixed real/rational subspace E=span(e1) always has F=0, S=span(e1)
under sigma_A(x,j)=x-A*j, while Gamma_A=L_A intersect E=3Z e1.
Quotient residual T is the last seven entries of A. This common fixed
stratum has uniform T before selection, but not after selecting w.
This is a finite model, not a production selected-history estimate.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product

Q=3
M=8


def centered(value):
    return (value+1)%Q-1


def winner_test(column):
    horizontal=(9,(-3,)+(0,)*(M-1),0)
    best=horizontal
    for j in range(-3,4):
        if j==0:
            continue
        x=tuple(centered(j*a) for a in column)
        candidate=(sum(v*v for v in x)+j*j,x,j)
        best=min(best,candidate)
    return best==horizontal,best


def main():
    columns=list(product(range(Q),repeat=M))
    baseline=Counter()
    selected=Counter()
    selected_count=0
    tie_count=0
    for a in columns:
        chosen,best=winner_test(a)
        assert chosen==all(a)
        # sigma_A(e1,0)=e1, independently of A; E has zero kernel.
        sigma_e1=tuple(int(i==0)-a[i]*0 for i in range(M))
        assert sigma_e1==(1,)+(0,)*(M-1)
        # Along E, membership is x1=0 mod3, giving exactly 3Z e1.
        assert all(((integer%Q)==0)==(integer in (-6,-3,0,3,6))
                   for integer in range(-6,7))
        residual=a[1:]
        baseline[residual]+=1
        if chosen:
            selected[residual]+=1
            selected_count+=1
            # Height +/-1 competitors tie norm9 but have first coordinate
            # >=-1, so lexicographic priority keeps the horizontal winner.
            assert best==(9,(-3,)+(0,)*(M-1),0)
            tie_count+=1
    assert len(columns)==3**8 and len(baseline)==3**7
    assert all(count==3 for count in baseline.values())
    assert selected_count==2**8
    assert all(selected[t]==(2 if all(t) else 0) for t in baseline)
    mass=F(selected_count,len(columns))
    assert mass==F(2,3)**8
    tv=sum((abs(F(selected[t],selected_count)-F(count,len(columns)))
            for t,count in baseline.items()),F(0))/2
    assert tv==1-F(2,3)**7
    density=max(F(selected[t],selected_count)/F(count,len(columns))
                for t,count in baseline.items())
    assert density==F(3,2)**7
    # Exact likelihood weighting: alpha(T)=Pr(selected|T).
    alpha={t:F(selected[t],baseline[t]) for t in baseline}
    assert all(value==(F(2,3) if all(t) else 0) for t,value in alpha.items())
    tests=(lambda t:int(t[0]==0),lambda t:sum(t),lambda t:int(all(t)))
    for test in tests:
        conditional=sum((F(selected[t],selected_count)*test(t) for t in baseline),F(0))
        weighted=sum((F(baseline[t],len(columns))*alpha[t]*test(t)
                      for t in baseline),F(0))/mass
        assert conditional==weighted
    old_zero=sum((F(count,len(columns)) for t,count in baseline.items() if t[0]==0),F(0))
    new_zero=sum((F(selected[t],selected_count) for t in baseline if t[0]==0),F(0))
    assert old_zero==F(1,3) and new_zero==0
    # In the retained lattice use (b,0), (d,-1), with disjoint supports
    # of sizes 3 and 4. Squared norms are 3 and 5; labels are b,d+T.
    # Enumerate nonzero-label collisions rather than assuming their sign.
    a=(1,1,1,0,0,0,0)
    d=(0,0,0,1,1,1,1)
    minus_a=tuple(-x%3 for x in a)
    stats={}
    for t in baseline:
        second=tuple((x+y)%3 for x,y in zip(d,t))
        labels=[v for v in (a,second) if any(v)]
        n=len(labels)
        j=sum(v==w for v in labels for w in labels)
        scalar=sum(w==tuple(k*x%3 for x in v)
                   for v in labels for w in labels for k in (1,2))
        assert n==2-int(not any(second))
        assert j==n+2*int(second==a)
        assert scalar==n+2*int(second in (a,minus_a))
        certificate=F(2*n*n,(3**7-1)*scalar)  # q3 sign quotient: r=0.
        covered={tuple(k*x%3 for x in v) for v in labels for k in (1,2)}
        assert certificate==F(len(covered),3**7-1)
        stats[t]=(F(n),F(j),F(scalar),certificate)
    old_means=[sum((F(baseline[t],len(columns))*stats[t][i] for t in baseline),F(0))
               for i in range(4)]
    new_means=[sum((F(selected[t],selected_count)*stats[t][i] for t in baseline),F(0))
               for i in range(4)]
    assert old_means[1:3]==[2+F(1,2187),2+F(3,2187)]
    assert new_means[1:3]==[F(129,64),F(65,32)]
    assert new_means[1]>old_means[1] and new_means[2]>old_means[2]
    assert new_means[3]<old_means[3]  # Witness coverage only, not actual failure.
    assert sum(x*x for x in a)==3 and sum(x*x for x in d)+1==5
    # On selected histories M_T has minimum squared 8: centered heights
    # +/-1 give 8; +/-2 give 11; horizontal and larger heights give >=9.
    # The witnesses at R^2=5 support k=1 and a nontrivial c^2=7<8.
    assert 5+1<7<8
    for i in (1,2):
        covariance=sum((F(baseline[t],len(columns))*alpha[t]*stats[t][i]
                        for t in baseline),F(0))-mass*old_means[i]
        assert covariance==mass*(new_means[i]-old_means[i])>0
    # Weighted Cauchy--Schwarz retains the actual selection likelihood.
    # Every r>=0 below is a valid relaxation of the q3 spectral value r=0.
    selected_moment_bounds=[]
    for r in (F(0),F(1,4),F(1)):
        weighted_n=sum((F(baseline[t],len(columns))*alpha[t]*stats[t][0]
                        for t in baseline),F(0))
        weighted_d=F(0)
        weighted_certificate=F(0)
        for t in baseline:
            n,j,scalar,_=stats[t]
            denominator=r*2*j+(1-r)*scalar
            weight=F(baseline[t],len(columns))*alpha[t]
            weighted_d+=weight*denominator
            weighted_certificate+=weight*2*n*n/((3**7-1)*denominator)
        lower=2*weighted_n**2/((3**7-1)*weighted_d)
        assert 0<=lower<=weighted_certificate<=mass
        assert lower/mass<=new_means[3]
        selected_moment_bounds.append(lower/mass)
    assert selected_moment_bounds[0]==F(128,71045)
    print('Raw columns:',len(columns),'residual values:',len(baseline))
    print('Selected columns:',selected_count,'all with genuine shortest norm ties:',tie_count)
    print('Baseline residual multiplicity:3; selected multiplicity:2 on nonzero grid,0 elsewhere.')
    print('Selected mass:',mass,'total variation:',tv,'maximum density ratio:',density)
    print('Test 1{T0=0}: baseline',old_zero,'selected',new_zero)
    print('Three exact likelihood-weighted tests passed.')
    print('Two-candidate old means (N,J,Csc,coverage):',old_means)
    print('Two-candidate selected means:',new_means)
    print('Both collision covariances are positive; witness coverage decreases.')
    print('Selected conditional coverage lower bounds from mixed moments:',selected_moment_bounds)
    print('All fixed-stratum, shortest selection, residual histogram, and likelihood checks passed.')


if __name__=='__main__':
    main()
