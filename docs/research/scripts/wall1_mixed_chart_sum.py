"""Shared coefficient charts: exact counts, factorization obstruction, row repeats."""
from fractions import Fraction as F
from itertools import product,permutations
from math import log10


def falling(n,k):
    out=1
    for i in range(k):out*=max(0,n-i)
    return out


def checks():
    q=5;center=lambda u:(u+2)%q-2
    # Affine coefficients (1-u,u) are shared by both repeated coordinates.
    f=[F(2)**(-center(u)**2) for u in range(q)]
    actual=sum(x*x for x in f)
    incorrectly_decoupled=sum(f)**2/q
    assert actual==F(193,128) and incorrectly_decoupled==F(289,320)
    assert actual>incorrectly_decoupled
    assert actual<=sum(f)**2  # Unnormalized relaxation is valid but looser.
    print('shared two-coordinate chart sum',actual,'invalid normalized factorization',incorrectly_decoupled)
    # Equality with the same shared-chart higher powers and exact chart count.
    for n in (1,2,3,6):
        exact=sum(x**n for x in f)
        assert exact>=sum(f)**n/q**(n-1)
        assert exact<=sum(f)**n
    cases=0
    for d in (1,2,3):
        coeffs=list(product(range(q),repeat=d))
        charts=[(1-sum(u))%q for u in coeffs]
        assert all((c+sum(u))%q==1 for c,u in zip(charts,coeffs))
        # Independent affine basis ensures distinct coefficients mean distinct inputs.
        used=coeffs[:d+1]
        remaining=[u for u in coeffs if u not in used]
        for k in (1,2):
            assert sum(1 for _ in permutations(remaining,k))==falling(q**d-len(used),k)
            cases+=1
    # A connected four-point anchor in a plane with three copies of each coordinate.
    d=2;copies=3;R2=6
    embed=lambda u:(u[0],)*copies+(u[1],)*copies
    anchor=[(0,0),(1,0),(0,1),(1,1)]
    C=[u for u in product(range(q),repeat=d)
       if sum(center(v)**2 for v in embed(u))<=R2]
    assert set(anchor)<=set(C) and len(C)==9
    assert sum(1 for _ in permutations([u for u in C if u not in anchor],2))==20
    # Exact weighted pivot count agrees and beats the arbitrary affine cap q^d.
    weighted=sum(1 for u in product(range(q),repeat=d)
                 if sum(copies*center(v)**2 for v in u)<=R2)
    assert weighted==9<q**d
    # gamma=(log2)/3: e^(gamma R²)*prod theta_q(3 gamma)=4*(17/8)^2.
    gaussian=4*sum(f)**2
    assert F(weighted)<=gaussian==F(289,16)<q**d
    print(cases,'exact coefficient distinctness counts passed.')
    print('repeated-coordinate full-rank fixture: C=9<25, pinned two completions20, Gaussian cap',gaussian)
    q=3329;d=10;k=6;H=13
    Q=q**(d*k);distinct=falling(q**d-H,k)
    assert distinct<=Q
    deficit=F(1)-F(distinct,Q)
    assert deficit<=F(k*H+k*(k-1)//2,q**d)
    print('production unrestricted coefficient charts q^60; log10',60*log10(q))
    print('distinct/pinned relative deletion <=',float(F(93,q**10)))

if __name__=='__main__':checks()
