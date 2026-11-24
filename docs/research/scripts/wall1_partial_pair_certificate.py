"""Certified moment intervals before all old-minimum exclusions are processed."""
from fractions import Fraction as F
from itertools import product
from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_mixed_exclusion_gates import exclude
from wall1_selected_pair_collision import nonzero_mark_moments
from wall1_integer_pair_bound import integer_void_upper


def main():
    q=5
    model=FixedQuotientGraphSpace(q,2,1,0,(),())
    candidates=tuple(z for z in product((-1,0,1),repeat=3)
                     if 0<sum(x*x for x in z)<=2)
    short=tuple(z for z in product((-1,0,1),repeat=3) if any(z))
    # Identical zero-equation events are deduplicated, but full and quotient
    # tags are kept distinct even in this zero-image fixture.
    quotient_lines=sorted({row_basis((z,),q) for z in short})
    # First full event overlaps a later quotient event. This tests the
    # remainder union bound when events are not disjoint.
    events=[('full',(1,1,1))]+[('quotient',line[0]) for line in quotient_lines]+[('full',(2,1,1))]
    center=F(len(candidates),q*q-1)
    direct=[]
    for prefix in range(len(events)+1):
        sums=[F(0)]*4
        void=F(0)
        for a in product(range(q),repeat=2):
            def label(z):
                return tuple((z[i]-a[i]*z[2])%q for i in range(2))
            if any(not any(label(v)) for _,v in events[:prefix]):
                continue
            for u in product(range(q),repeat=2):
                if not any(u):
                    continue
                z=sum(label(x)==u for x in candidates)
                for j,value in enumerate((1,z,z*(z-1),(F(z)-center)**2)):
                    sums[j]+=value
                void+=int(z==0)
        direct.append((tuple(v/q**4 for v in sums),void/q**4))
    target,truth_void=direct[-1]
    states={((),()):1}
    lower_envelope=[F(0)]*4
    previous=None
    best_void=F(1)
    improved=None
    for prefix in range(len(events)+1):
        upper=nonzero_mark_moments(model,states,candidates,center)
        assert upper==direct[prefix][0]
        residual=[F(0)]*4
        for tag,v in events[prefix:]:
            weighted=nonzero_mark_moments(model,states,candidates,center,
                         (v,) if tag=='full' else (), (v,) if tag=='quotient' else ())
            residual=[r+w for r,w in zip(residual,weighted)]
        lower=[max(F(0),u-r) for u,r in zip(upper,residual)]
        if prefix==0:
            assert lower[0]<target[0]
        lower_envelope=[max(a,b) for a,b in zip(lower_envelope,lower)]
        assert all(lo<=x<=hi for lo,x,hi in zip(lower_envelope,target,upper))
        if previous is not None:
            assert all(u<=p for u,p in zip(upper,previous))
        previous=upper
        second_upper=upper[2]+upper[1]
        cs=upper[0]-lower_envelope[1]**2/second_upper if second_upper else upper[0]
        integer_bound,_=integer_void_upper(upper[0],lower_envelope[1],upper[2])
        best_void=min(best_void,cs,integer_bound,upper[3]/center**2,upper[0])
        assert truth_void<=best_void
        if best_void<upper[0] and improved is None:
            improved=prefix
        if prefix in (0,len(events)):
            print('prefix',prefix,'upper',upper,'lower',lower_envelope,'void upper',best_void)
        if prefix<len(events):
            states=exclude(states,*events[prefix],model)
    assert tuple(lower_envelope)==target
    assert best_void<target[0]
    assert best_void==truth_void
    # At incomplete gates, using M1=M0*center is generally false.
    assert direct[0][0][1]!=direct[0][0][0]*center
    print('Prefixes certified:',len(direct),'first strict void improvement:',improved)
    print('Actual fixture joint void:',truth_void,'certified bound:',best_void)
    print('PASS; production remainder and selected-history bounds remain open.')


if __name__=='__main__':
    main()
