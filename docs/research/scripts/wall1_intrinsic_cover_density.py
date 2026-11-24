"""Exact rounding checks and deterministic mean-density floor horizons.

The covering radius <=sqrt(rank)/2 is already proved in
wall1_history_free_compression.md, Lemma 2. Unbiased rounding below is an
alternate verification, not a new lemma. The density screen reuses the
existing Hermite determinant floors. It is not a failure-probability bound.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial
from mpmath import iv
from wall1_hermite_budget import log_floors

iv.dps=40


def matvec(matrix,vector):
    return tuple(sum((x*y for x,y in zip(row,vector)),F(0)) for row in matrix)


def rounding_checks():
    checks=0
    for vector in ((1,2),(1,2,3)):
        n=len(vector)
        square=sum(x*x for x in vector)
        line=tuple(tuple(F(x*y,square) for y in vector) for x in vector)
        complement=tuple(tuple(F(i==j)-line[i][j] for j in range(n)) for i in range(n))
        for projection,rank in ((line,1),(complement,n-1)):
            assert sum(projection[i][i] for i in range(n))==rank
            for a in product((F(-1,3),F(0),F(1,4),F(1,2)),repeat=n):
                x=matvec(projection,a)
                lower=tuple(v.__floor__() for v in a)
                fractional=tuple(v-lo for v,lo in zip(a,lower))
                expectation=F(0)
                probability_sum=F(0)
                minimum=None
                for bits in product((0,1),repeat=n):
                    probability=F(1)
                    for bit,t in zip(bits,fractional):
                        probability*=t if bit else 1-t
                    if not probability:
                        continue
                    integer=tuple(lo+bit for lo,bit in zip(lower,bits))
                    rounded=matvec(projection,integer)
                    error=sum((v-w)**2 for v,w in zip(x,rounded))
                    expectation+=probability*error
                    probability_sum+=probability
                    minimum=error if minimum is None else min(minimum,error)
                formula=sum((projection[i][i]*fractional[i]*(1-fractional[i])
                             for i in range(n)),F(0))
                assert probability_sum==1 and expectation==formula<=F(rank,4)
                assert minimum<=F(rank,4)
                checks+=1
    return checks


def main():
    print('Exact independent-rounding projection checks:',rounding_checks())
    floors=log_floors()
    logv506=253*iv.ln(iv.pi)-iv.loggamma(254)
    logv505=iv.mpf(505)/2*iv.ln(iv.pi)-iv.loggamma(iv.mpf(507)/2)
    gmax=iv.exp((400*iv.ln(3329)-logv506)/506)
    intrinsic=iv.sqrt(505)/2
    factor=iv.mpf(11)/10
    assert (factor*gmax).b<(506*intrinsic).a
    # d log[(R-rho)^505/g^506]/d log g has the sign of
    # 506*rho*R+1010-R^2. Since R<1.1*gmax<506*rho, it is positive.
    # The same certificate holds for every larger ambient rho below.
    print('Uniform monotonicity certified: 1.1*gmax < 506*rho_intrinsic.')
    print('gmax:',gmax,'intrinsic cover radius:',intrinsic)
    def density(g,rho):
        radius=iv.sqrt(factor**2*g*g-2)
        if radius.b<=rho.a:
            return None
        assert radius.a>rho.b, 'Unresolved radius/cover interval comparison'
        return iv.exp(logv505-logv506+505*iv.ln(radius-rho)-506*iv.ln(g))-iv.mpf(1)/3328
    intrinsic_values=[]
    ambient_values=[]
    for freeze,floor in enumerate(floors):
        g=iv.exp((floor-logv506)/506)
        intrinsic_values.append(density(g,intrinsic))
        ambient_values.append(density(g,iv.sqrt(505+freeze)/2))
    selected={14,100,200,300,400,406}
    for name,values in (('intrinsic',intrinsic_values),('ambient',ambient_values)):
        for threshold in (58,1):
            passed=[]
            for freeze,value in enumerate(values):
                if value is None:
                    continue
                if value.a>threshold:
                    passed.append(freeze)
                else:
                    assert value.b<threshold, 'Unresolved strict threshold comparison'
            last=max(passed) if passed else None
            print(name,'largest freeze with density floor >',threshold,':',last)
            if last is not None:
                assert passed==list(range(last+1))
                selected.update(f for f in (last-1,last,last+1) if 0<=f<=406)
    for freeze in sorted(selected):
        print('freeze',freeze,'intrinsic F:',intrinsic_values[freeze],
              'ambient F:',ambient_values[freeze])
    # If L*=58(h-1), p=1/(h-1), every factor in the first eleven
    # binomial-kernel terms is >=58. This is reference normalization only.
    reference=1/sum((F(58**j,factorial(j)) for j in range(12)),F(0))
    assert reference<F(1301,10**15)
    print('Uniform degree-11 reference norm <1.301e-12; selected higher errors are not bounded.')
    print('Every reported floor is uniform for g between its Hermite floor and gmax, when R>rho.')
    print('No failure-probability bound or selected-history incidence estimate is asserted.')


if __name__=='__main__':
    main()
