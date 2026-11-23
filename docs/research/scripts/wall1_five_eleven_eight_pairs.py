"""H11 girth5: complete 7000-witness cover of two independent norm-eight rows."""
from collections import Counter
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows

PAIR_BOUND=7000


def checks():
    inside=[v+(0,)*6 for v in norm_rows(5,8,minimum_support=5)]
    outside=[v for v in norm_rows(11,8,minimum_support=5) if all(v[5:])]
    assert len(inside)==20 and len(outside)==350
    assert all(sum(bool(x) for x in b[:5])==2 and all(abs(x)<=1 for x in b) for b in outside)
    determinants=Counter()
    for a in inside:
        assert sorted(abs(x) for x in a[:5])==[1,1,1,1,2]
        for b in outside:
            dot=sum(x*y for x,y in zip(a,b))
            assert abs(dot)<=3
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(11),2))
            determinants[64-dot*dot]+=1
    assert sum(determinants.values())==PAIR_BOUND
    assert dict(determinants)=={55:1500,60:2100,63:1300,64:2100}
    # Two outside norm-eight rows with proportional new restrictions have
    # a nonzero combination supported on <=4 old coordinates. Girth5 excludes it.
    excluded=0
    for a,b in combinations(outside,2):
        ratio=a[5]*b[5]
        if any(x!=ratio*y for x,y in zip(a[5:],b[5:])):continue
        difference=tuple(x-ratio*y for x,y in zip(a,b))
        assert 0<sum(bool(x) for x in difference)<=4
        excluded+=1
    print('inside/outside norm8 lines:',len(inside),len(outside),
          'pair witnesses:',PAIR_BOUND,'Gram strata:',dict(sorted(determinants.items())))
    print('outside/outside proportional-new pairs excluded by girth5:',excluded)
    # A pair fixes one finite-field plane and a unique normalized coefficient
    # chart. Count eligible prescribed second supports only as a diagnostic.
    for q in (7,17,3329):
        charts={a:set() for a in range(1,5)}
        for a in inside:
            f=tuple(x*pow(a[0]%q,-1,q)%q for x in a)
            for b in outside:
                inv=pow(b[5]%q,-1,q)
                v=tuple((x-b[0]*y)*inv%q for x,y in zip(b,f))
                for scalar in {(-b[i]*pow(a[i]%q,-1,q))%q for i in range(5)}:
                    support=tuple(i for i in range(5) if (b[i]+scalar*a[i])%q)
                    for overlap in charts:
                        if support==tuple(range(overlap)):charts[overlap].add((f,v))
        assert {a:len(v) for a,v in charts.items()}=={1:0,2:700,3:210,4:1960}
        print('q',q,'eligible chart counts',{a:len(v) for a,v in charts.items()})


def kernels(s,overlap):
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    beta=I(9*n)/(22*R**2);a=iv.pi**2/beta;alpha=a/q**2
    assert 14**3<q and 11*14**2<q*q
    def theta(x):
        geo=s['geometry']['theta_upper']
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(11,j)*delta**j for j in range(1,12)),I(0))
    tail=iv.exp(-98*alpha)*theta(I(5)*alpha/2)**2
    def kernel(g1,g2):
        return (iv.pi/beta)**(I(11)/2)*((theta(g1*alpha)*theta(g2*alpha)+tail)/q**2+periodic)
    Q=q**(7+overlap)
    rare=I(min(Q,PAIR_BOUND))/Q*kernel(I(8),I(55)/8)**n
    one_eight=kernel(I(8),I(8))**n
    no_eight=kernel(I(10),I(15)/2)**n
    old=min((kernel(I(8),I(6))**n,kernel(I(8),I(55)/8)**n+no_eight),key=lambda v:v.b)
    return old,rare+one_eight+no_eight,(rare,one_eight,no_eight)


def diagnostic():
    import contextlib,io
    from wall1_rank_nine_five_diagnostic import main
    with contextlib.redirect_stdout(io.StringIO()):s,raw=main()
    I,iv=s['I'],s['iv']
    candidates=s['size17_stratum_candidates'][9,5]
    assert candidates['two'].b<candidates['one'].a
    ratios={}
    for overlap in range(1,5):
        old,new,parts=kernels(s,overlap)
        selected=s['five_circuit_anchor_parts'][6,overlap]['selected']
        # Reconstruct the previous complete branch after production integration.
        # This H11/c5 branch has zero one-six/two-six terms.
        chosen=min((old,new),key=lambda v:v.b)
        production_ratio=selected/chosen
        tolerance=I('1e-60')
        assert production_ratio.a>(1-tolerance).b
        assert production_ratio.b<(1+tolerance).a
        ratios[overlap]=chosen/old
        assert iv.log10(ratios[overlap]).b<-15.65
        print('overlap',overlap,'new / reconstructed previous selected log10',iv.log10(ratios[overlap]),
              'rare/complement log10',iv.log10(parts[0]/(parts[1]+parts[2])))
    for h in (17,18):
        terms={key[1:]:v for key,v in raw.items() if key[0]==h}
        new_total=sum(terms.values(),I(0))
        old_total=sum((v/ratios[a] if t==6 else v for (t,a),v in terms.items()),I(0))
        assert iv.log10(new_total/old_total).b<-1.96
        print('size',h,'rank9c5 two-relation aggregate new/old log10',iv.log10(new_total/old_total))
    return s,ratios


if __name__=='__main__':
    checks()
    diagnostic()
