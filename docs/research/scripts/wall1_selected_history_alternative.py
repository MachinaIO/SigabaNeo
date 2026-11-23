"""Exact tests for latent collision histories and stopped drift certificates.

No simulation, asymptotic assumption, or claim of a BKZ drift estimate.
"""
from fractions import Fraction as F
from itertools import product


def collision(a, t, q):
    # Labels x-a*y of C_t={(0,0),(t,1)} in the graph-lattice quotient.
    labels=(0,(t-a)%q)
    return sum(x==y for x in labels for y in labels)


def collision_checks():
    events=0
    for q in (3,5,7,11):
        values={a:tuple(F(q*(collision(a,t,q)-2),2) for t in range(q))
                for a in range(q)}
        for t in range(q):
            assert sum((values[a][t] for a in range(q)),F(0))/q==1
            for a in range(q):
                assert collision(a,t,q)==2+2*(a==t)
                assert values[a][t]==q*(a==t)
                events+=1
        assert all(max(v)==q for v in values.values())
        # Under the observable collision filtration, a string of misses has
        # current value zero but positive next conditional expectation.
        for t in range(q-1):
            remaining=[a for a in range(q) if all(values[a][j]==0 for j in range(t+1))]
            assert len(remaining)==q-t-1
            assert all(values[a][t]==0 for a in remaining)
            next_mean=sum((values[a][t+1] for a in remaining),F(0))/len(remaining)
            assert next_mean==F(q,q-t-1)>0
        # Under the uninformative filtration, {first hit<=0}={a=0} is neither
        # empty nor the entire sample space, so first hit is not a stopping time.
        assert 0<sum(values[a][0]>0 for a in range(q))<q
        print(f'q={q}: each fixed-time mean=1; maximum={q} surely; '
              'latent first hit is not a stopping time; observed process has positive drift')
    return events


def stopped_tree_checks():
    """Exhaustive finite binary-tree illustration of the stopped drift proof.

    Potentials need not be martingales. Conditional positive drift is charged
    exactly, including histories where a bad event has not yet occurred.
    """
    paths=list(product((0,1),repeat=3))
    checked=0
    for mode in range(4):
        def phi(prefix):
            t=len(prefix)
            if mode==0:return F(sum(prefix),2)
            if mode==1:return F(sum((j+1)*b for j,b in enumerate(prefix)),4)
            if mode==2:return F((sum(prefix)%2)*(t+1),4)
            return F(sum(prefix)**2,9)
        for threshold in (F(1,2),F(3,4),F(1)):
            def potential(prefix):return phi(prefix)/threshold
            costs={}
            for t in range(3):
                for prefix in product((0,1),repeat=t):
                    increment=(potential(prefix+(0,))+potential(prefix+(1,)))/2-potential(prefix)
                    costs[prefix]=max(F(0),increment)
            hit=F(0);stopped=F(0);stopped_cost=F(0);all_cost=F(0)
            for path in paths:
                tau=next((t for t in range(4) if potential(path[:t])>=1),4)
                hit+=F(tau<=3,len(paths))
                stopped+=potential(path[:min(tau,3)])/len(paths)
                stopped_cost+=sum((costs[path[:i]] for i in range(3) if i<tau),F(0))/len(paths)
                all_cost+=sum((costs[path[:i]] for i in range(3)),F(0))/len(paths)
            assert hit<=stopped<=potential(())+stopped_cost<=potential(())+all_cost
            checked+=1
    print(f'Passed {checked} exact adapted stopped-potential tree checks.')
    return checked


def first_moment_checks():
    checked=0
    # Uniform independent labels realize the reference pair-collision law.
    for h in (2,3,4):
        for n in (1,2,3,4):
            total=F(0)
            for labels in product(range(h),repeat=n):
                j=sum(x==y for x in labels for y in labels)
                d=F(18,7)*(F(h*j,n*n)-1)
                assert d>=0
                total+=d
            expected=total/h**n
            assert expected==F(18*(h-1),7*n)
            checked+=1
    # Reference N/h=58 exactly: the linear potential is not a 1e-12 budget.
    h=3329
    value=F(18*(h-1),7*58*h)
    assert value>F(4,100)
    print(f'Passed {checked} exact pair-collision first-moment identities; '
          f'at N/h=58 and h=3329, E[D]={float(value):.12g}>0.04.')
    return checked


if __name__=='__main__':
    count=collision_checks()
    stopped_tree_checks()
    first_moment_checks()
    print(f'PASS: {count} exact graph-lattice collision identities.')
