"""Exact fixed-quotient disintegration in a small raw graph model.

q=3, x,y in F3^2, sigma_A(x,y)=x-Ay. For each fixed subspace E,
condition on F=ker(sigma_A|E) and S=image(sigma_A|E). The residual
T=RA, for fixed ker R=S, is tested against precisely the forced equations
Ty=Rx for (x,y) in E. No selected-history law is inferred from this test.
"""
from collections import Counter,defaultdict
from itertools import combinations,product
from fractions import Fraction as F

Q=3


def canonical(rows,width):
    a=[list(row) for row in rows if any(row)]
    rank=0
    for col in range(width):
        pivot=next((i for i in range(rank,len(a)) if a[i][col]%Q),None)
        if pivot is None:
            continue
        a[rank],a[pivot]=a[pivot],a[rank]
        inverse=pow(a[rank][col],-1,Q)
        a[rank]=[v*inverse%Q for v in a[rank]]
        for i in range(len(a)):
            if i!=rank:
                scale=a[i][col]
                a[i]=[(v-scale*w)%Q for v,w in zip(a[i],a[rank])]
        rank+=1
        if rank==len(a):
            break
    return tuple(tuple(row) for row in a[:rank])


def subspaces(width):
    """Unique RREF bases: free entries only right of each row's pivot."""
    output=[]
    for rank in range(width+1):
        for pivots in combinations(range(width),rank):
            free=[(i,j) for i,pivot in enumerate(pivots)
                  for j in range(pivot+1,width) if j not in pivots]
            for values in product(range(Q),repeat=len(free)):
                rows=[[int(j==pivot) for j in range(width)] for pivot in pivots]
                for (i,j),value in zip(free,values):
                    rows[i][j]=value
                output.append(tuple(map(tuple,rows)))
    assert len(set(output))==len(output)
    return output


def span(basis,width):
    return [tuple(sum(c*row[j] for c,row in zip(coefficients,basis))%Q
                  for j in range(width))
            for coefficients in product(range(Q),repeat=len(basis))]


def sigma(a,z):
    return tuple((z[i]-sum(a[2*i+j]*z[2+j] for j in range(2)))%Q for i in range(2))


def quotient(s):
    if not s:
        return ((1,0),(0,1))
    if len(s)==2:
        return ()
    u,v=s[0]
    row=((v%Q,(-u)%Q),)
    return canonical(row,2)


def residual(r,a):
    return tuple(sum(row[i]*a[2*i+j] for i in range(2))%Q
                 for row in r for j in range(2))


def compatible(t,r,e):
    return all(sum(t[2*i+j]*z[2+j] for j in range(2))%Q
               ==sum(row[j]*z[j] for j in range(2))%Q
               for z in e for i,row in enumerate(r))


def main():
    spaces=subspaces(4)
    assert len(spaces)==212
    matrices=list(product(range(Q),repeat=4))
    strata=0
    quotient_dims=Counter()
    supports=0
    largest_lift=0
    kernel_strata=0
    output_spaces=subspaces(2)
    assert len(output_spaces)==6
    for e in spaces:
        vectors=span(e,4)
        groups=defaultdict(Counter)
        for a in matrices:
            f=canonical([z for z in vectors if not any(sigma(a,z))],4)
            s=canonical([sigma(a,z) for z in e],2)
            r=quotient(s)
            assert all(all(sum(row[i]*v[i] for i in range(2))%Q==0
                           for row in r) for v in span(s,2))
            groups[f,s][residual(r,a)]+=1
        input_rank=len(canonical([z[2:] for z in e],2))
        old_output=canonical([z[:2] for z in vectors if not any(z[2:])],2)
        a_dimension=len(e)-input_rank
        assert len(old_output)==a_dimension
        by_kernel=defaultdict(dict)
        for (f,s),counts in groups.items():
            r=quotient(s)
            expected={t for t in product(range(Q),repeat=2*len(r)) if compatible(t,r,e)}
            assert expected and set(counts)==expected
            assert len(set(counts.values()))==1
            assert len(f)+len(s)==len(e)
            # Positive strata have graphic F: its input projection is injective.
            assert len(canonical([z[2:] for z in f],2))==len(f)
            exponent=(2-len(s))*input_rank+len(s)*len(f)
            predicted=F(1,Q**exponent)
            for ell in range(1,input_rank-len(f)+1):
                predicted*=1-F(1,Q**ell)
            observed=F(sum(counts.values()),len(matrices))
            assert observed==predicted
            by_kernel[f][s]=observed
            strata+=1
            quotient_dims[len(r)]+=1
            supports+=len(expected)
            largest_lift=max(largest_lift,max(counts.values()))
        for f,by_image in by_kernel.items():
            required_dimension=len(e)-len(f)
            admissible={s for s in output_spaces if len(s)==required_dimension
                        and all(v in span(s,2) for v in span(old_output,2))}
            assert set(by_image)==admissible
            assert len(set(by_image.values()))==1
            old_formula=F(1,Q**(2*len(f)))
            for j in range(input_rank-len(f)):
                exponent=a_dimension+j-2
                power=F(Q**exponent) if exponent>=0 else F(1,Q**(-exponent))
                old_formula*=1-power
            assert sum(by_image.values(),F(0))==old_formula
            kernel_strata+=1
    # A difference can be nonzero before quotient and vanish modulo S.
    e=((1,0,0,0),)
    s=((1,0),)
    r=quotient(s)
    a=(0,0,0,0)
    difference=(1,0,0,0)
    raw=sigma(a,difference)
    assert raw==(1,0) and any(raw)
    assert residual(r,a)==(0,0)
    assert all(sum(row[i]*raw[i] for i in range(2))%Q==0 for row in r)
    print('All F3^4 subspaces:',len(spaces),'raw matrices per subspace:',len(matrices))
    print('Nonempty (E,F,S) strata:',strata,'by quotient dimension:',dict(sorted(quotient_dims.items())))
    print('Distinct admissible residual-map supports summed across strata:',supports)
    print('Largest equal lift multiplicity:',largest_lift)
    print('Exact stratum mass formula checks:',strata)
    print('Fixed (E,F) image support/equal-mass and old kernel formula checks:',kernel_strata)
    print('Strict raw-vs-quotient collision example: (1,0) != 0 but R(1,0)=0.')
    print('All support equality, conditional uniformity, and rank checks passed.')


if __name__=='__main__':
    main()
