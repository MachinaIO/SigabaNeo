# Void probabilities at fixed Gram–Schmidt profile

## Independent lifts across one cut

Fix a positive diagonal, write the triangular basis in orthonormal GS coordinates, and put \(R=g_0\). Count sign pairs strictly inside the open ball. Split after the first \(t\) coordinates, \(1\le t<d\), and condition on both diagonal blocks of the triangular matrix. Write \(D\) for the first block lattice and \(H\) for the lower right matrix. For any nonzero integer suffix \(v\), the lifts of \(Hv\) have horizontal coordinates in a single translate of \(D\). Set
\[
 s_v=\sqrt{(R^2-\|Hv\|^2)_+},\qquad
 p_v=\operatorname{vol}_{\mathbb R^t/D}(B_t(s_v)\bmod D)
\]
with torus volume normalized to one and the radius-zero ball empty.

**Theorem.** Choose a rationally independent list of suffixes using only the two revealed blocks. Conditionally the indicators that these suffixes admit short lifts are independent Bernoulli variables with means \(p_v\). Thus the conditional void probability is at most \(\prod_v(1-p_v)\). In particular one may maximize \(\sum_v-\log(1-p_v)\) over independent lists after the reveal. Only finitely many suffixes have positive radius.

**Proof.** The cross-block columns are independent uniform points of the GS box of \(D\), a fundamental region by successive rounding. On the product of these tori, taking the integer linear combinations specified by the suffixes pushes Haar probability to product Haar. Indeed the integer coefficient matrix has full row rank, so its real linear map is onto in each torus coordinate. Passing to the quotient preserves surjectivity, hence its image measure is Haar. Primitivity and unit minors are unnecessary. Each hit tests membership of its own torus point in the projected ball. Integrating the conditional product gives the unconditional upper bound. This is a fixed-chart argument using the unfolding of Parts 46 and 55.

Here is a deterministic version with explicit exponent. For each column \(j\ge t\) take the unit suffix and put
\[
 h_j^2=g_j^2+\tfrac14\sum_{t\le l<j}g_l^2,\qquad
 q_j=\Pr\left[\sum_{l<t}g_l^2 U_l^2<R^2-h_j^2\right],
 \quad U_l\overset{\rm iid}{\sim}\mathrm{Unif}[-1/2,1/2].
\]
The portion of the GS box inside the indicated horizontal ball supplies distinct torus points almost everywhere. Size reduction bounds the squared suffix norm by \(h_j^2\). Therefore \(p_{e_j}\ge q_j\) on every history. With \(E=\mathbb E N_R\) and \(E'=\max_t\sum_{j\ge t}-\log(1-q_j)\) we obtain
\[
 \Pr[N_R=0]\le e^{-E'}\le e^{-\min(E,E')}.
\]
This proves a capped bound with \(c=1\). Its exponent can be infinite even in one column. For example at \(t=j=1\), \(g_1\le\sqrt3 R/2\) gives certain failure up to a null set. More generally the first inequality retains the full logarithmic penalty near coverage. For finite exponents it does not establish a profile-independent positive lower bound on \(E'/E\). Maximizing over cuts uses separately valid upper bounds. Multiplying across cuts could count the same randomness twice.

## Limits of a factorial-moment or dependency-graph argument

Parts 55 and 57 give the exact full mean, with a contribution \(V_j(R^2-m^2g_j^2)^{j/2}/\prod_{l<j}g_l\) for each last coefficient \(1\le m<R/g_j\). These are expected *numbers of lifts*. Even within one suffix, ball volume divided by determinant can exceed the probability of at least one lift. Different multiples of the same suffix give multiples of one torus point. For instance coefficient vectors \((0,1),(1,1)\) are independent over the rationals but have identical suffix at the row-zero cut. Tuple independence requires rank in the unrevealed variables. The choice of sign does not fix this defect.

There is a separate logical problem with the proposed Bonferroni comparison. For any \(\delta>0\), take zero with probability \(\delta/(1+\delta)\) and otherwise a Poisson variable of mean \((1+\delta)E\). Its mean is \(E\) and its order-\(k\) factorial moment is \((1+\delta)^{k-1}E^k\) for every \(k\ge1\), yet its void probability is at least \(\delta/(1+\delta)\). This example tests the moment inference only. Alternating sums require signed error control at the scale of the void probability. Likewise a row-overlap dependency graph puts all tests using row zero into one clique. Row independence alone supplies neither monotonicity nor a small sum of joint hit probabilities. The theorem bypasses those issues for independent suffixes, of which there are at most \(d-t\) in one list.

## Rank 1023 Haar integral

The table gives individual 99% lower bounds on \(g_{1023-\beta}\) for every fully BKZ-reduced basis of a Haar unimodular lattice, in covolume-one units. These numerical improvements come entirely from normalization in the disjoint HKZ integral. The independent-lift theorem gives no certified numerical gain here.

| Width | Certified radius | GSA comparison | Linear target |
|---:|---:|---:|---:|
|406|0.005832301|0.434|0.859|
|506|0.015428983|0.960|0.959|
|647|0.039231048|2.143|1.084|
|800|0.139941828|4.015|1.206|

Use the Part 50 upper prefix envelope and Part 55 partition integral in the form given in [the product certificate](wall1_volume_product.md). With \(h\) pieces of ranks \(d_i\), the exact zeta correction to its zeta-free log normalization is \(\sum_i Z_{d_i}-Z_n\), where \(Z_d=\sum_{s=2}^d\log\zeta(s)\). Cancel one term against \(Z_n\) and bound each remaining term by \(Z_\infty\). The finite interval sum below uses the integral test beyond 64 and \(\log\zeta(s)\le 3\cdot 2^{-s}\) beyond 32. The integer envelope rounds upwards, then its cap and log integral are checked outwards with mpmath. This bounds the probability of existence of a bad basis by its expected sign-divided count. The comparison columns are the rounded benchmarks of Part 57.

```python
from fractions import Fraction as Q
from mpmath import iv as I
I.dps=40
n=1023
M=10**9
C=[0,0]
A=[I.mpf(0)]*2
for d in range(2,n+1):
    u=I.mpf(d)/2
    small=[0,0,Q(4,3),2,4,8,Q(64,3),64,256]
    if d<len(small):
        z=Q(small[d])
        H=I.ln(I.mpf(z.numerator)/z.denominator)/2
    else:
        H=u*I.ln(2/I.pi)+I.loggamma(2+u)
    C.append(int((M*H).a)+1)
    assert C[d]-1<=M*H and M*H<C[d]
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u))
def envelope(b,t):
    k=n-b
    T=[0]*(n+1)
    for i in reversed(range(n-1)):
        T[i]=T[i+1]+min((C[d]+T[i+1]-T[i+d]+d-2)//(d-1)
                        for d in range(2,min(b,n-i)+1))-(t if i==k else 0)
    return T,[I.mpf((n-i)*T[0]-n*T[i])/(n*M) for i in range(n+1)]
def partition(U,e):
    L=A[n]-(len(e)-2)*I.ln(2)
    for i,j in zip(e,e[1:]):
        d=j-i
        L+=d*(U[i]+U[j])-A[d]+I.mpf('1.5')
    return L-sum(I.ln(z-x) for x,z in zip(e,e[2:]))
cases=[(406,list(range(13,170,13))+[183,197,212,618]),
       (506,[12,518]),
       (647,[377]),
       (800,[224])]
# Z_d=sum_{j=2}^d log zeta(j). Cancel the largest block
# against Z_n and use a finite sum with an integral tail.
zbound=I.mpf(0)
for j in range(2,33):
    z=sum(I.mpf(m)**(-j) for m in range(1,65))+I.mpf(64)**(1-j)/(j-1)
    zbound+=I.ln(z)
zbound+=I.mpf(3)*2**-32
assert zbound<I.mpf('1.1')
for b,cuts in cases:
    k=n-b
    h=len(cuts)+1
    dent,scaled={
        406:(6063551553,5832301),506:(5154982794,15428983),
        647:(4632315938,39231048),800:(3786982933,139941828)
    }[b]
    ends=[0]+cuts+[n]
    assert all(1<=y-x<=b for x,y in zip(ends,ends[1:]))
    _,U=envelope(b,dent)
    L=partition(U,ends)-I.mpf('1.5')*h+(h-1)*zbound
    assert L < -I.ln(100)
    assert I.exp(U[k+1]-U[k]) > I.mpf(scaled)/M
    print(b,scaled,float(L.b))
```

The open step is to control the conditional void probability across the profiles carrying the bad Haar mass. Neither a uniform full-mean exponent nor a lower bound on the integrated penalty sufficient to offset the roughly 34,000 excess log units has been established here. All four GSA and linear targets remain uncertified.
