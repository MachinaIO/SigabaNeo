"""Uniform ball-constrained affine-slice completion bound; no random-span assumption."""
from itertools import product
from fractions import Fraction as F

def completion_bound(s,dimension):
    I,iv,q,R=[s[k] for k in ('I','iv','q','radius')]
    assert 0<=dimension<len(s['geometry']['volume'])
    if dimension==0:return I(1)
    volume=s['geometry']['volume'][dimension]
    ball=volume*(R+iv.sqrt(I(dimension))/2)**dimension
    return min((I(q**dimension),ball),key=lambda x:x.b)

def checks():
    tested=0
    for q in (3,5):
        half=q//2
        points=list(product(range(-half,half+1),repeat=3))
        directions=set()
        for a in product(range(q),repeat=3):
            if not any(a):continue
            p=next(x for x in a if x)
            directions.add(tuple(x*pow(p,-1,q)%q for x in a))
        for normal in directions:
            missing=next(i for i,x in enumerate(normal) if x)
            pivots=tuple(i for i in range(3) if i!=missing)
            for target in range(q):
                for radius_sq in (0,1,2,4,7,12):
                    section=[v for v in points if sum(x*x for x in v)<=radius_sq
                             and sum(x*y for x,y in zip(v,normal))%q==target]
                    images={tuple(v[i] for i in pivots) for v in section}
                    assert len(images)==len(section)
                    possible=sum(sum(x*x for x in v)<=radius_sq
                                 for v in product(range(-half,half+1),repeat=2))
                    assert len(section)<=possible<=q*q
                    tested+=1
    print('Passed',tested,'exact affine-plane ball/pivot injection checks.')

def diagnostic():
    import contextlib,io,runpy
    from pathlib import Path
    with contextlib.redirect_stdout(io.StringIO()):
        s=runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    for d in range(8,24):
        print('dimension',d,'completion/q^d log10',s['iv'].log10(completion_bound(s,d)/s['q']**d))

if __name__=='__main__':
    checks()
    diagnostic()
