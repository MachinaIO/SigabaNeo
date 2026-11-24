"""Degree-21 raw-void lower witness; actual draw15 moment transfer is unproved."""
from fractions import Fraction as F
from math import comb,factorial

def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def solve(a,b):
 n=len(b);a=[list(map(F,row))+[F(y)] for row,y in zip(a,b)]
 for i in range(n):
  k=next(k for k in range(i,n) if a[k][i]);a[i],a[k]=a[k],a[i]
  v=a[i][i];a[i]=[x/v for x in a[i]]
  for k in range(n):
   if k!=i:
    v=a[k][i];a[k]=[x-v*y for x,y in zip(a[k],a[i])]
 return [row[-1] for row in a]
t=10;mu=10
M=lambda i,j:sum(F(comb(i,k)*comb(j,k)*factorial(k))*mu**(i+j-k) for k in range(min(i,j)+1))
H=lambda i,j:M(i+1,j)+(i-1)*M(i,j)
c=solve([[H(i,j) for j in range(1,t+1)] for i in range(1,t+1)],[-H(0,j) for j in range(1,t+1)])
q=[F(1)]+[F(0)]*t;fall=[F(1)]
for i in range(1,t+1):
 fall=mul(fall,[F(1-i),F(1)])
 for j,x in enumerate(fall):q[j]+=c[i-1]*x
p=mul([F(1),F(-1)],mul(q,q));n=len(p)-1
S=[[0]*(n+1) for _ in range(n+1)];S[0][0]=1
for i in range(1,n+1):
 for j in range(1,i+1):S[i][j]=S[i-1][j-1]+j*S[i-1][j]
a=[sum(p[i]*S[i][j] for i in range(j,n+1)) for j in range(n+1)]
def val(x):return sum(v*x**i for i,v in enumerate(a))
assert q[0] == 1 and len(p) == 22
def bern(lo,hi):
 co=[sum(a[j]*comb(j,i)*lo**(j-i)*(hi-lo)**i for j in range(i,n+1)) for i in range(n+1)]
 return [sum(co[i]*F(comb(k,i),comb(n,i)) for i in range(k+1)) for k in range(n+1)]
cap=F('9.287185')
minimum = min(x for k in range(40) for x in bern(cap*k/40,cap*(k+1)/40))
assert minimum > F('0.0000647')
for z in range(101):
    g = sum(v*z**i for i,v in enumerate(p))
    assert g == (1-z)*sum(v*z**i for i,v in enumerate(q))**2
    assert g <= int(z == 0)
# a_j are both the Poisson-mean polynomial coefficients and the coefficients
# of g in the falling-factorial basis. Check the exact moment transfer.
laws = [(F(1),), (F(1,2),F(1,2)), (F(0),F(0),F(1)), tuple([F(1,10)]*10)]
for law in laws:
    mean = sum(F(z)*prob for z,prob in enumerate(law))
    moments = [sum(prob*(factorial(z)//factorial(z-j) if z>=j else 0)
                   for z,prob in enumerate(law)) for j in range(n+1)]
    expected = sum(prob*sum(v*z**i for i,v in enumerate(p)) for z,prob in enumerate(law))
    assert expected == sum(v*m for v,m in zip(a,moments))
    discrepancy = sum(abs(v)*abs(m-mean**j) for j,(v,m) in enumerate(zip(a,moments)))
    assert law[0] >= val(mean)-discrepancy >= F('0.0000647')-discrepancy
    # Independent Poisson(10-mean) padding changes only the first factorial cumulant.
    cumulants = [F(0)]*(n+1)
    for j in range(1,n+1):
        cumulants[j] = moments[j]-sum(F(comb(j-1,k-1))*cumulants[k]*moments[j-k]
                                     for k in range(1,j))
    correction = [F(1)]+[F(0)]*n
    for j in range(1,n+1):
        correction[j] = sum(cumulants[k]*correction[j-k]/factorial(k-1)
                            for k in range(2,j+1))/F(j)
    weights = [sum(a[j]*F(factorial(j),factorial(j-k))*10**(j-k)
                   for j in range(k,n+1)) for k in range(n+1)]
    padded = [sum(F(comb(j,k))*moments[k]*(10-mean)**(j-k) for k in range(j+1))
              for j in range(n+1)]
    assert sum(a[j]*padded[j] for j in range(n+1)) == sum(weights[j]*correction[j] for j in range(n+1))
    actual_weights=[sum(a[j]*F(factorial(j),factorial(j-k))*mean**(j-k)
                        for j in range(k,n+1)) for k in range(n+1)]
    assert expected == sum(actual_weights[j]*correction[j] for j in range(n+1))
    uniform_weights=[sum(abs(a[j])*F(factorial(j),factorial(j-k))*cap**(j-k)
                         for j in range(k,n+1)) for k in range(n+1)]
    assert abs(expected-val(mean)) <= sum(uniform_weights[j]*abs(correction[j]) for j in range(2,n+1))
assert val(F(10)) > F('0.0000247527')
print('Exact Bernstein coefficients certify Poisson expectation >0.0000647 on [0,9.287185].')
print('Degree21 pointwise lower witness and four exact factorial-moment transfer checks passed.')
print('Actual draw15 factorial-moment discrepancy is NOT bounded by this script.')
print('Four exact Poisson-padding/cumulant transfer identities passed; fixed-mean baseline >0.0000247527.')
