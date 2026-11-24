"""Actual planar winners, finite witnesses, and shared-column replica checks.

All comparisons are exact. Toy radii do not model the BKZ moving-radius law.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd


def centered(v,q):
    return (v+q//2)%q-q//2


def shortest(q,u,scale):
    # The vector (scale*q,0) certifies norm <= scale*q; scale<=1.
    choices=[(scale*scale*x*x+j*j,scale*x,j) for x in range(-q,q+1)
             for j in range(-q,q+1)
             if (x or j) and (x-u*j)%q==0]
    s2,x,j=min(choices)
    assert gcd(int((x/scale-u*j)/q),j)==1
    return s2,x,j


def main():
    branches=0;replica_checks=0;strict_example=None;kernel_cases=0
    saturation_checks=0;strict_saturations=0
    for q,scale in product((3,5,7),(F(1),F(1,4))):
        for heights in ((0,),(-1,0,1),(-2,-1,0,1,2)):
            for radius in ('quarter','one','moving'):
                counts=[]
                for u in range(q):
                    s2,wx,wj=shortest(q,u,scale)
                    b2={'quarter':F(1,4),'one':F(1),'moving':F(4,1+s2)}[radius]
                    actual={v for v in range(q)
                            if scale**2*centered(wj*v,q)**2/s2>b2}
                    witnesses=set()
                    for v in range(q):
                        projections=[]
                        for j in heights:
                            y=scale*centered(v+j*u,q)
                            # (y,j) represents the same marked projected coset.
                            assert (y/scale-v-j*u)%q==0
                            p2=F(y*y+j*j)-F((y*wx+j*wj)**2,s2)
                            assert p2>=0
                            assert p2==F((wj*y-wx*j)**2,s2)
                            projections.append(p2)
                        if all(p2>b2 for p2 in projections): witnesses.add(v)
                    assert actual<=witnesses
                    # Projection kernel is multiplication by winner height.
                    image={wj*v%q for v in range(q)}
                    kernel=q//len(image)
                    assert all(sum(wj*v%q==a for v in range(q))==kernel for a in image)
                    # Credit every input label whose image has a hit witness.
                    hit_images={wj*v%q for v in range(q) if v not in witnesses}
                    saturated_misses={v for v in range(q) if wj*v%q not in hit_images}
                    assert actual<=saturated_misses<=witnesses
                    strict_saturations+=len(saturated_misses)<len(witnesses)
                    saturation_checks+=1
                    # Ambient content equals the order of the projection kernel.
                    content=gcd(abs(int(wx/scale)),abs(wj))
                    assert content==kernel and content in (1,q)
                    if content==q and wj:
                        assert wx==0 and abs(wj)==q and s2==q*q
                    image_misses={a for a in image if scale**2*centered(a,q)**2/s2>b2}
                    assert F(len(actual),q)==F(len(image_misses),len(image))
                    kernel_cases+=kernel>1
                    counts.append(len(witnesses));branches+=1
                for k in (1,2,3,24):
                    moment=sum(F(m,q)**k for m in counts)/q
                    replica_count=sum(m**k for m in counts)
                    assert moment==F(replica_count,q**(k+1))
                    independent=(F(sum(counts),q*q))**k
                    assert moment>=independent
                    if k==24 and len(heights)==3 and moment>independent and strict_example is None:
                        strict_example=(q,scale,heights,radius,counts,moment,independent)
                    # Explicit tuples verify the counting shortcut at small k.
                    if k<=3:
                        total=sum(sum(all(v<m for v in vs) for vs in product(range(q),repeat=k)) for m in counts)
                        assert total==replica_count
                    replica_checks+=1
    assert strict_example is not None and kernel_cases>0
    q,scale,hs,rad,counts,shared,independent=strict_example
    print('Actual shortest-winner branches:',branches)
    print('Exact replica moment checks:',replica_checks)
    print('Nontrivial quotient-kernel cases:',kernel_cases)
    print('Fiber-saturation checks / strict improvements:',saturation_checks,strict_saturations)
    print('Independent-column error fixture q/heights/radius/counts:',q,scale,hs,rad,counts)
    print('Shared-U 24th moment:',shared)
    print('Independent-U substitution:',independent)
    print('Exact ratio:',shared/independent)

if __name__=='__main__': main()
