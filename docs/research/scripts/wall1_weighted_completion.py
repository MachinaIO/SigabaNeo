"""Exact weighted affine-span completion and rank-collision checks.

Finite fixtures only; no assertion about the width-506 numerical budget.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product, permutations
from math import comb, factorial


def line_key(x, y, q):
    dx, dy = (y[0]-x[0]) % q, (y[1]-x[1]) % q
    normal = (dy, -dx % q)
    first = next(v for v in normal if v)
    normal = tuple(v*pow(first,-1,q) % q for v in normal)
    return normal+(sum(a*b for a,b in zip(normal,x)) % q,)


def check(q, radius_sq):
    half=q//2
    points=list(product(range(-half,half+1),repeat=2))
    ball=[x for x in points if sum(a*a for a in x)<=radius_sq]
    normals=[(1,i) for i in range(q)]+[(0,1)]
    lines=[v+(t,) for v in normals for t in range(q)]
    occupancy={v:sum((v[0]*x[0]+v[1]*x[1]-v[2])%q==0 for x in ball) for v in lines}
    basis=list(permutations(ball,2))
    masses=Counter(line_key(x,y,q) for x,y in basis)
    assert all(masses[v]==occupancy[v]*(occupancy[v]-1) for v in lines)
    ell=len(lines); z=len(basis); N=len(ball); Q=q*q; p=F(1,q)
    mean=p*N
    variance=p*(1-p)*N*(Q-N)/(Q-1)
    assert sum((F(c)-mean)**2 for c in occupancy.values())/ell==variance
    collision=0
    for x,y in basis:
        for u,v in basis:
            dx,dy=y[0]-x[0],y[1]-x[1]
            same=all((dx*(t[1]-x[1])-dy*(t[0]-x[0]))%q==0 for t in (u,v))
            assert same==(line_key(x,y,q)==line_key(u,v,q))
            collision+=same
    chi=F(ell*collision,z*z)-1
    assert chi==sum((F(ell*masses[v],z)-1)**2 for v in lines)/ell
    selected=F(sum(masses[v]*occupancy[v] for v in lines),z)
    assert selected>=mean and (selected-mean)**2<=variance*chi
    # Sharpness for a legal (nonnegative) tilt, with no fresh-span hypothesis.
    t=F(1,2*q)
    densities={v:1+t*(occupancy[v]-mean) for v in lines}
    assert all(v>=0 for v in densities.values())
    assert sum(densities.values())==ell
    tilted=sum(densities[v]*occupancy[v] for v in lines)/ell
    tilted_chi=sum((v-1)**2 for v in densities.values())/ell
    assert tilted==mean+t*variance
    assert (tilted-mean)**2==variance*tilted_chi
    if (q,radius_sq)==(5,2):
        assert selected==F(8,3) and mean==F(9,5) and chi==F(17,18)
        # Prove CS upper bound < 11/4 + 1/100 = 69/25, with rationals.
        assert variance*chi < (F(69,25)-mean)**2
        assert max(occupancy.values())==3
    print(f'q={q}, R^2={radius_sq}, N={N}, lines={ell}, bases={z}, '
          f'occupancy_hist={dict(sorted(Counter(occupancy.values()).items()))}')
    print(f'  uniform_mean={mean}, weighted_mean={selected}, variance={variance}, '
          f'chi2={chi}, basis_span_collisions={collision}; sharp tilt checked')
    return z*z


def projective(v, q):
    v=tuple(x % q for x in v)
    if not any(v):
        return None
    inv=pow(next(x for x in v if x),-1,q)
    return tuple(x*inv % q for x in v)


def fixed_anchor_check(q, ambient, anchor_dim, extension_rank, radius_sq):
    # Anchor is the coordinate anchor_dim-plane through zero. Its quotient
    # coordinates are the remaining D coordinates; no random-anchor premise.
    D=ambient-anchor_dim; k=extension_rank
    assert (D,k) in ((2,0),(2,1),(3,2))
    residues=list(product(range(q),repeat=D))
    directions=sorted({projective(v,q) for v in residues if any(v)})
    if k==0:
        spaces=[frozenset({(0,)*D})]
    elif k==1:
        spaces=[frozenset(tuple(t*x % q for x in v) for t in range(q)) for v in directions]
    else:
        spaces=[frozenset(v for v in residues if sum(x*y for x,y in zip(v,n))%q==0)
                for n in directions]
    assert len(set(spaces))==len(spaces)
    half=q//2
    ball=[v for v in product(range(-half,half+1),repeat=ambient)
          if sum(x*x for x in v)<=radius_sq]
    fiber=Counter(tuple(x % q for x in v[anchor_dim:]) for v in ball)
    b0=fiber[(0,)*D]
    T={v:sum(fiber[tuple(t*x % q for x in v)] for t in range(1,q)) for v in directions}
    p=F(q**k-1,q**D-1)
    p2=F(0) if k<2 else p*F(q**k-q,q**D-q)
    total=sum(T.values()); energy=sum(x*x for x in T.values())
    mean=b0+p*total
    variance=p*(1-p)*energy+(p2-p*p)*(total*total-energy)
    occupancy={W:sum(fiber[v] for v in W) for W in spaces}
    assert sum(occupancy.values())/F(len(spaces))==mean
    assert sum((c-mean)**2 for c in occupancy.values())/len(spaces)==variance
    for u in directions:
        assert F(sum(u in W for W in spaces),len(spaces))==p
        for v in directions:
            if u!=v:
                assert F(sum(u in W and v in W for W in spaces),len(spaces))==p2
    masses=Counter()
    for vectors in permutations(ball,k):
        quotient=[tuple(x % q for x in v[anchor_dim:]) for v in vectors]
        generated=frozenset(tuple(sum(t*x[i] for t,x in zip(coeff,quotient))%q for i in range(D))
                            for coeff in product(range(q),repeat=k))
        if len(generated)==q**k:
            masses[generated]+=1
    z=sum(masses.values()); L=len(spaces)
    collision=sum(w*w for w in masses.values())
    chi=F(L*collision,z*z)-1
    selected=sum(masses[W]*occupancy[W] for W in spaces)/F(z)
    assert (selected-mean)**2<=variance*chi
    # Direct unnormalized weighted-moment inequality.
    assert (z*(selected-mean))**2<=variance*(L*collision-z*z)
    def falling(c,j):
        out=1
        for i in range(j):out*=c-i
        return out
    for degree in (1,2,5,6,10):
        for function in (lambda c:c**degree,lambda c:falling(c,degree)):
            reference=sum(function(c) for c in occupancy.values())/F(L)
            second=sum(function(c)**2 for c in occupancy.values())/F(L)
            weighted=sum(masses[W]*function(occupancy[W]) for W in spaces)/F(z)
            assert (weighted-reference)**2 <= (second-reference**2)*chi
    if (q,ambient,anchor_dim,k,radius_sq)==(5,2,0,1,2):
        # Rank enumerators in this D=2,k=1 fixture: quotient rank is 0,
        # 1 if all nonzero vectors have one direction, and 2 otherwise.
        probabilities={0:F(1),1:p,2:F(0)}
        factorial_moments={0:F(1)}
        for degree in range(1,5):
            for distinct in (False,True):
                tuples=permutations(ball,degree) if distinct else product(ball,repeat=degree)
                counts=Counter()
                for row in tuples:
                    dirs={projective(v,q) for v in row if any(v)}
                    rank=min(2,len(dirs))
                    counts[rank]+=1
                moment=sum(number*probabilities[rank] for rank,number in counts.items())
                actual=sum((falling(c,degree) if distinct else c**degree)
                           for c in occupancy.values())/F(L)
                assert moment==actual
                if distinct:factorial_moments[degree]=moment
        for degree in (1,2):
            second=sum(comb(degree,i)**2*factorial(i)*factorial_moments[2*degree-i]
                       for i in range(degree+1))
            assert second==sum(falling(c,degree)**2 for c in occupancy.values())/F(L)
    if (q,ambient,anchor_dim,k,radius_sq)==(5,2,0,1,2):
        assert (mean,variance,chi,selected)==(F(7,3),F(8,9),F(1,2),F(3))
        assert (selected-mean)**2==variance*chi
    print(f'fixed anchor: q={q}, n={ambient}, a={anchor_dim}, k={k}, R^2={radius_sq}; '
          f'mean={mean}, variance={variance}, chi2={chi}, weighted_mean={selected}, bases={z}')
    return len(directions)**2


def zero_extension_checks():
    # A full fixed affine anchor leaves one possible plane, even with many
    # weighted/decorated basis descriptions and different forbidden identities.
    checks=0
    for c in range(1,9):
        weights=(F(1),F(2),F(3,2))
        Z=sum(weights); collision=Z*Z; L=1
        chi=F(L*collision,Z*Z)-1
        assert chi==0
        for j in (1,2,5,6,10):
            reference=F(c**j)
            second=F(c**(2*j))
            weighted=sum(w*c**j for w in weights)/Z
            assert weighted==reference and second-reference**2==0
            # Quotient k=0: rank-zero tuples are precisely those entirely
            # in the fixed anchor. There are C(S)^j of them.
            assert reference==c**j
            checks+=1
        for m in range(c+1):
            from itertools import combinations
            for forbidden in combinations(range(c),m):
                assert len(set(range(c))-set(forbidden))==c-m
                for j in (1,2,5):
                    remaining=1
                    for i in range(j):remaining*=c-m-i
                    assert remaining==len(list(permutations(set(range(c))-set(forbidden),j)))
                    checks+=1
    print(f'PASS: {checks} zero-extension and fixed-cardinality forbidden-set checks.')


if __name__=='__main__':
    zero_extension_checks()
    tests=sum(check(q,r) for q,r in ((3,1),(5,2),(7,4)))
    anchor_tests=sum(fixed_anchor_check(*case) for case in
                     ((5,2,0,0,2),(5,3,1,0,2),(5,2,0,1,2),(3,3,1,1,2),(5,3,1,1,2),
                      (3,3,0,2,2),(5,3,0,2,2)))
    print(f'PASS: {tests} ordered basis-pair rank-collision tests; '
          f'{anchor_tests} fixed-anchor direction-pair cases; exact moments and sharpness.')
