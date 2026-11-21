# Counting bad bases of the null graph lattice

On the full shape the quadratic comparison fails at all four requested widths. With probability greater than $1-2^{-360}$, **every** fully reduced basis has terminal length at most 600, simultaneously at these widths. Even the smallest quadratic target is 608.5. This concerns the actual projected minimum and strengthens the obstruction for the Rankin quotient. The full-shape linear comparison and the positive-prefix Babai bound at the four widths remain open here. [Rankin route](wall1_rankin_route.md) · [Part 48](wall1_null_terminal.md)

Write $r$ for the number of retained sample rows, $n=512$, $N=r+n$, $D=q^r$, $q=3329$. Width $b$ counts horizontal dimensions, so $k=N-b$ is the zero-based terminal index. With an embedding height the corresponding width is $b+1$. We use the fixed length benchmarks $\sqrt{6b}$ and $1+1.5(b-1)$ specified in the question. The latter is a sufficient-comparison benchmark evaluated at a mean, and failure to clear it does not decide the planted shortest-vector comparison. [Part 47](wall1_decoupled.md)

## Exact basis count

For an integer matrix $B=(E;F)$ in vertical block notation, simultaneous column membership is the equation $AF=-E$ over the prime field. It is soluble exactly when $\ker F\subseteq\ker E$, equivalently $\mathrm{rank}(B)=\mathrm{rank}(F)=s$ over this field. Each of the $r$ independent rows then has $q^{n-s}$ choices. If $|\det B|=D$, membership implies generation by index equality. Moreover $s=n$ is forced in the soluble case since the reduction of the generated lattice is the full graph. Equivalently the Smith factors are $r$ copies of $q$ and $n$ units, and projection of the residue space onto the secret coordinates is bijective. Thus the exact expected ordered count is
$$
 q^{-rn}\#\{B\in U\cap M_N(\mathbb Z): |\det B|=D,\ 
 \mathrm{rank}_q B=\mathrm{rank}_q F=n\}.
$$
For example the complete search can be bounded recursively by the Part 6 upper prefix volumes $X_j$. Every nonempty integer prefix has volume at least 1 by Cauchy–Binet, hence $g_i\le X_{i+1}$. Size reduction gives squared column norms at most $X_{i+1}^2+\sum_{h<i}X_{h+1}^2/4$. This proves finiteness without replacing determinant equality by a thickened real region. The determinant slice has ordinary matrix-space volume zero. A Haar calculation on the fixed-determinant space would still need a finite-modulus discrepancy estimate for this particular region. [Part 6](wall1_prefix.md)

## A lower bound for the bad-region sum via the last successive minimum

Fix an integer $K$ with $2\sqrt K<q$. Let $M$ count all integer points in the shell $K/2<\|v\|^2\le K$ in dimension $N$, and $H$ all points in the closed radius-$\sqrt K$ ball in dimension $r$. If $M>4NH$, then
$$
 \Pr\{\lambda_N(L_A)>\sqrt K\}\le p=16qN^2D/M .
$$

**Proof.** Drop the shell points with zero secret residue, of which there are at most $H$ since the secret coordinates must vanish integrally. For the remaining set $S$ form $Z=\sum_{v\in S}1_{v\in L_A}vv^T$. Sign and permutation symmetry make the full shell's unweighted matrix sum scalar, with each eigenvalue greater than $MK/(2N)$ by its trace. Removing the excluded points costs at most $HK$ in operator norm. Every retained point has membership probability $1/D$, so the least eigenvalue of $\mathbb EZ$ exceeds $MK/(4ND)$.

In the expansion of $\mathbb E\|Z-\mathbb EZ\|_F^2$, each covariance has multiplier $(v^Tw)^2\le K^2$. Independent secret residues have covariance zero. For dependent nonzero secret residues simultaneous membership requires the same scalar relation on the full vectors modulo $q$. For each $v$ at most $q-1$ choices of $w$ can contribute positive covariance, since the ball maps injectively modulo $q$. Each covariance is at most $1/D$. Hence the second moment is at most $qMK^2/D$. If $Z$ is singular the Frobenius deviation exceeds $MK/(4ND)$, by testing a unit null vector. Markov proves the claim since nonsingularity supplies a spanning set of lattice vectors of length at most $\sqrt K$.

For **any** proper prefix span, at least one spanning vector has nonzero projection, of length at most its original length. The terminal BKZ window covers the whole quotient, so its shortest-first condition implies $g_k\le\sqrt K$ simultaneously for all such reduced bases. At least one size-reduced HKZ basis exists by recursively taking a primitive shortest vector in each quotient, lifting and size reducing. It satisfies all truncated block checks. With the usual closed size-reduction bound, independent column sign choices give at least $2^N$ ordered bases in the Part 6 region whenever $\sqrt K<\rho$ and spanning holds. Consequently the requested sum is at least $2^N(1-p)$ in each passing cell below. Even counting one representative per lattice gives at least $1-p$.

| Retained rows (null rank) | Quadratic, all applicable widths | Linear 406 | Linear 506 | Linear 647 | Linear 800 |
|---|---:|---:|---:|---:|---:|
| 511 (1023) | 360 | open | open | open | open |
| 188 (700) | 2322 | 30 | 30 | 57 | outside rank |
| 149 (661) | 2553 | 191 | 296 | 413 | outside rank |
| 134 (646) | 2641 | 333 | 435 | outside rank | outside rank |

An integer $e$ certifies $p<2^{-e}$, hence a **negative** decision on whether the bad-region sum is below 0.01. Quadratic cells all use the same radius 600. The spanning bounds in the linear cells use $K=6b-1$ so strict badness holds even in the presence of ties. The Part 39 embedded dimension 647 corresponds to horizontal rank 646 after deleting sample coordinates. Its existing planted guarantee addresses a different comparison. [Frontier](../PROOF_GAP.md)

## Projector-uniform improvement at rank 700

At this rank a sphere of squared radius $K=3969$ also refutes the linear comparison at 406 and 506. The ambient sphere radius 63 exceeds both targets. To rule out a zero projection and a too-long projection in the same test, use the polynomial $t(T-t)$ with $t=v^TQv$, $T=6b$, and $Q$ any orthogonal projector of rank $b$. A positive sum forces some $0<t<T$.

In this paragraph $M$ counts the exact sphere and $H$ its sample-only points. Let $a$ and $c$ be the averages of $v_1^4$ and $v_1^2v_2^2$ on the whole sphere. Coordinate symmetry gives $Na+N(N-1)c=K^2$. By sign symmetry only even coordinate multiplicities survive in the fourth moment, giving
$$
 \operatorname{avg} t^2=c(b^2+2b)+(a-3c)\sum_i Q_{ii}^2.
$$
Here $\mathrm{tr}(Q^2)=b$ and $\sum_i Q_{ii}^2\le b$. Since the average of $t$ is $Kb/N$, the variable `margin` below bounds the full-sphere average of the polynomial from below. Removing the sample-only points reduces this lower bound by at most $HTK/M$.

For $h=2,4$ take the random tensor sum of $v^{\otimes h}$ over retained sphere points satisfying the check. The squared Frobenius deviation from its expectation has mean at most $qMK^h/D$ by the same covariance proof, since the inner-product multiplier is $(v^Tw)^h\in[0,K^h]$. Except with probability at most $2qD/(M\epsilon^2)$, both deviations have norm at most $\epsilon M K^{h/2}/D$. Contracting with $Q$ and $Q\otimes Q$ costs factors $\sqrt b$ and $b$, respectively. Thus after normalization by $D/M$ the random polynomial sum is at least the margin less $HTK/M+\epsilon b(TK+K^2)$, uniformly over all projectors, including data-dependent ones. The following exact checks give positive margins simultaneously at all three widths, with exceptional probability below $2^{-30}$. At 647 the spanning certificate is stronger.

```python
from math import isqrt
def theta(d,K):
    a=[1]
    for t in range(1,K+1):
        a.append(2*sum(((d+1)*j*j-t)*a[t-j*j]
                       for j in range(1,isqrt(t)+1))//t)
    return a
q,r,N,K=3329,188,700,3969
M=theta(N,K)[K]
H=theta(r,K)[K]
slice_count=theta(N-1,K)
from fractions import Fraction as F
a=F(2*sum(j**4*slice_count[K-j*j] for j in range(1,64)),M)
c=(K*K-N*a)/(N*(N-1))
eps=F(1,1000*N)
for b in (406,506,647):
    T=6*b
    margin=F(T*K*b,N)-c*(b*b+2*b)-max(0,a-3*c)*b
    assert margin > F(H*T*K,M)+eps*b*(T*K+K*K)
assert 2*q*q**r*2**30 < M*eps**2
```

## Numerical certificate

For small radii compute exact coefficients of $a(z)=f(z)^d$, $f(z)=1+2\sum_{j\ge1}z^{j^2}$, using $fa'=df'a$. For radius 600 use unit cubes about the integer points. The ball of radius $R-\sqrt d/2$ is covered by cubes of points of norm at most $R$, and all those cubes fit inside radius $R+\sqrt d/2$. Subtraction bounds the shell from below. Python 3 with mpmath interval arithmetic checks the table by strict comparisons.

```python
from math import isqrt
from mpmath import iv as I
I.dps=40
q=3329
def counts(d,K):
    a=[1]
    for t in range(1,K+1):
        v=2*sum(((d+1)*j*j-t)*a[t-j*j] for j in range(1,isqrt(t)+1))
        assert v%t==0
        a.append(v//t)
    return sum(a[(K//2+1):]),sum(a)
for r in (511,188,149,134):
    N=r+512
    for b in (406,506,647,800):
        if b>N: continue
        for quad in (False,True):
            K=600**2 if quad else 6*b-1
            if quad:
                B=I.sqrt(K)
                ball=lambda d,R:I.pi**(I.mpf(d)/2)*R**d/I.gamma(1+I.mpf(d)/2)
                M=ball(N,B-I.sqrt(N)/2)-ball(N,B/I.sqrt(2)+I.sqrt(N)/2)
                H=ball(r,B+I.sqrt(r)/2)
            else:
                M0,_=counts(N,K)
                _,H0=counts(r,K)
                M,H=I.mpf(M0),I.mpf(H0)
            assert M > 4*N*H
            p=16*q*N*N*q**r/M
            targets = {511:360,188:2322,149:2553,134:2641}
            linear = {(188,647):57,(149,406):191,(149,506):296,
                      (149,647):413,(134,406):333,(134,506):435}
            e = targets[r] if quad else linear.get((r,b))
            if e is not None:
                assert p * 2**e < 1
                assert 4*K < q*q
                assert (4*K < (3*b-1)**2) if quad else (K < 6*b)
```

The open cells require control of short vectors created by projection even when the ambient ball fails to span. The tuple identity fixes the weight of each complete basis but supplies no estimate of how many integral completions have the required coupled prefix and suffix profile. Dividing the ordered sum by the sign multiplicity is valid for an event bound and still leaves that count unresolved. The spanning theorem gives upper bounds on terminal lengths and yields no positive lower certificate for the earlier GS lengths at 12. No Haar or GSA value enters the table.
