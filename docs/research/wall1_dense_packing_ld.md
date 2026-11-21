# Deterministic void exclusion on the twelve Part 71 boxes

**Theorem.** Each rank-1023 witness box in Part 71 has a full-width projected block in which every triangular basis with the specified diagonal has a nonzero vector strictly shorter than the first GS length. The block start can be fixed throughout each box. Thus the fixed-profile void probability and the contribution of each box to the fully accepted integral are exactly zero. The proof uses a finite-dimensional spherical-code certificate. It does not require independence, or even randomness, of the coefficients. [Part 71](wall1_surviving_mass.md) · [Wall 1 frontier](../PROOF_GAP.md)

## Packing inequality and certificate

Write $V_b$ for unit ball volume, $R=g_i$ for the head of the projected block starting at $i$, and $L$ for that block lattice in its $b$ GS coordinates. Its determinant is $\prod_{l=i}^{i+b-1}g_l$. Define $T=V_b R^b/\det L$. If $N=0$, then $\lambda_1(L)\ge R$, and open balls of radius $R/2$ centered at $L$ form a packing of density $2^{-b}T$. For $t=\cos\theta\le1/2$, Cohn–Zhao Proposition 2.1 therefore implies
$$T\le [2(1-t)]^{b/2} A(b,\theta),$$
where $A$ is the largest code on the unit sphere in $\mathbb R^b$ with distinct inner products at most $t$. The dimension on the right is exactly $b$. [Cohn–Zhao, Proposition 2.1 and Theorem 3.1](https://arxiv.org/pdf/1212.5966)

Let $P_l$ be the degree-$l$ Gegenbauer polynomial for this sphere normalized by $P_l(1)=1$, and let $h_l$ be the dimension of degree-$l$ spherical harmonics. With spherical probability normalization, $\int P_l^2=1/h_l$. Choose rational $u>t$ with $P_0(u),\ldots,P_{k-1}(u)>0$ and $P_k(u)<0$. Put
$$q(x)=\sum_{l<k} h_l P_l(u)P_l(x),\qquad F(x)=(x-t)q(x)^2.$$
Then
$$A(b,\theta)\le
\frac{(1-t)q(1)^2}{(u-t)\sum_{l<k}h_l P_l(u)^2}.$$

Indeed, the addition theorem makes each $P_l$ a positive definite zonal kernel. Christoffel–Darboux gives $(x-u)q(x)$ as a positive constant times $P_k(x)P_{k-1}(u)-P_{k-1}(x)P_k(u)$ (the leading coefficients are positive). Both this kernel and $q$ have nonnegative Gegenbauer coefficients. Their product is positive definite by the Schur product theorem, hence has nonnegative constant coefficient. Consequently $F=q[(x-u)q]+(u-t)q^2$ is positive definite and its constant coefficient is at least $(u-t)\int q^2$, the denominator above. Off-diagonal code pairs have $F\le0$. Summing $F$ over all ordered code pairs gives at most $|C|F(1)$ and at least $|C|^2$ times the constant coefficient. This proves the bound. The certificate checks polynomial signs at rational points directly.

| Width | $k$ | $10^6u$ | Upper bound on $\log T$ if void | Lower bound on $\log T$ throughout box | Starts for .25, .5, .85 GSA (zero-based) |
|---:|---:|---:|---:|---:|---|
|406|25|403296|130|133|24, 175, 47|
|506|31|409232|160|162|99, 15, 49|
|647|40|417789|201|204|197, 159, 168|
|800|50|424962|245|249|158, 24, 34|

Here $t=u-2(1-u)/b$. The two bounds in each row are strict. For each of the twelve boxes the certificate maximizes $b x_i-\sum_{l=i}^{i+b-1}x_l$ at its center and subtracts $2b\cdot10^{-6}$ to cover all permitted perturbations. Recentring cancels exactly. At these same starts the final $m=1$ section alone certifies $\log E>129,159,200,245$, respectively. Part 71 used a finite list of packing bounds. The stronger inequality above is consistent with feasibility for that earlier list.

## What the exponent measures

For these windows $-\log\Pr_\mu[N=0]=+\infty$. In particular the proposed $E^{0.11}$ bound holds there for their actual means. Using the earlier certified $\log E\ge129$ for the mean-selected window, a sufficient *hypothetical* uniform exponent for the previous argument was $842097+\log100$ nats. The corresponding power threshold is $\log(842097+\log100)/129$ (between .1057 and .1059), and $51(\log E)^2$ would also suffice. The smaller 828813 figure was a lower bound on relaxed intensity. The packing proof bypasses this comparison entirely. [Fixed-profile moments](wall1_mu_moments.md)

There is also a width-dependent threshold stated purely in terms of $E$. If $U_s$ bounds $2^s$ times the maximal packing density in dimension $s$, then
$$ E>\tfrac12\sum_{s=2}^b U_s\quad\Longrightarrow\quad\Pr[N=0]=0.$$
In fact each prefix must pack at radius $R/2$ if the full block passes. At endpoint $j=s-1$, the mean is the sum of positive-height section volumes divided by the horizontal determinant. The section volume is decreasing in height, so its sum at $mg_j$, $m\ge1$, is bounded by its integral over positive heights divided by $g_j$. This is precisely $V_s R^s/(2\det L_s)$ after the horizontal divisor. Summing proves the implication using the exact first moment. Testing $T$ directly avoids the loss from summing unrelated prefix caps. Below these deterministic thresholds a general fixed-profile law with exponent $E^c$ or $C(\log E)^2$ remains open here. No estimate for the complement of the twelve boxes, or improved radius for the full integral, follows.

## Why random affine avoidance gives a different estimate

For prefix lattice $D_j$, the fresh horizontal column is uniform on its torus by triangular backward rounding. For each positive $m$ with $m g_j<R$, the forbidden shifts are the inverse image under multiplication by $m$ of the projected open ball of radius $r_{jm}=\sqrt{R^2-m^2 g_j^2}$. Their union has conditional hit probability equal to its normalized torus volume. Iteration must average the uncovered fraction against the prefix law *conditioned on survival*. The several multiples use the same shift. [Part 68](wall1_covering_fraction.md) · [Part 60](wall1_poisson_smallball.md)

For a Haar-unimodular lattice with an independent Haar shift, Athreya's Theorem 1 gives an upper bound $1/(1+V)$ for avoidance of a set of volume $V$ by the mean and variance identities. For balls the fixed-dimension order is $\Theta_d(1/V)$, $d\ge2$. To see the lower order, take a dual vector of length below $1/(4r)$. A uniform shift misses the radius-$r$ ball with probability at least $1/2$ by projecting onto the circle of phases along that vector. The Haar probability of such a dual vector is $\gg_d r^{-d}$: count primitive pairs in the small ball of radius $a=1/(4r)$. Their mean is $V_da^d/(2\zeta(d))$ by primitive Siegel. In $d\ge3$ their second factorial moment is $O_d(a^{2d})$ by the independent-pair term of Rogers' second moment formula (distinct primitive sign pairs are independent over $\mathbb Q$). In $d=2$ two independent vectors in this ball are impossible for $a<1$ by the determinant bound. Bonferroni gives the claimed order, using invariance under duality. Thus the Haar exponent grows only as $\log V+O_d(1)$ in this limit. Strömbergsson's convex avoidance theorem concerns linear lattices, and the El-Baz–Marklof–Vinogradov mixed moments concern directions in an affine lattice. Neither gives a fixed-diagonal exponential void law. [Athreya](https://arxiv.org/pdf/1409.6355) · [Strömbergsson](https://arxiv.org/abs/1008.3805) · [El-Baz–Marklof–Vinogradov](https://arxiv.org/abs/1306.0028)

The proposed $j/2$ transference criterion can be tested without sampling a dual basis. In local block indexing $e_{j-1}/g_{j-1}\in D_j^*$, since its pairing with the prefix columns gives the last integer coefficient. Thus $2r_{j1}<j g_{j-1}$ implies $r_{jm}<j/(2\lambda_1(D_j^*))$ for every admissible $m$. The certificate verifies this strict obstruction at **every** endpoint of all twelve selected windows, with box perturbations included. The probability of reaching this sufficient transference threshold there is zero. Actual torus coverage can occur below the threshold. The packing contradiction needs neither coverage of an individual torus nor a product estimate for the dependent tests.

## Reproduction

Run the following Python from the repository root with NumPy and mpmath. It imports Part 71's certificate initialization and witness recurrence. All sign tests and code-size ratios use rational arithmetic. Logarithms and the comparisons on boxes use interval arithmetic. The final decimal output is diagnostic only.

```python
from pathlib import Path
from fractions import Fraction as Q
from math import comb
exec(Path("docs/research/wall1_surviving_mass.md").read_text()
     .split("```python")[1].split("for b,rounded")[0])
def ivq(q):
    return I.mpf(q.numerator)/q.denominator
for b,k,u6,cap,lb,rounded in [
    (406,25,403296,130,133,'.369'),(506,31,409232,160,162,'.816'),
    (647,40,417789,201,204,'1.822'),(800,50,424962,245,249,'3.413')]:
    u=Q(u6,10**6)
    t=u-2*(1-u)/b
    p=[Q(1),u]
    for l in range(1,k):
        p.append(((2*l+b-2)*u*p[l]-l*p[l-1])/(l+b-2))
    assert min(p[:-1])>0 and p[-1]<0 and 0<t<Q(1,2)
    h=[comb(b+l-1,l)-(comb(b+l-3,l-2) if l>=2 else 0)
       for l in range(k)]
    Acode=(1-t)*sum(a*x for a,x in zip(h,p))**2/(
        (u-t)*sum(a*x*x for a,x in zip(h,p)))
    capval=I.ln(ivq(Acode))+b*I.ln(ivq(2*(1-t)))/2
    assert capval<cap
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    G=I.exp((2*b-n-1)*slope)
    for f in ['.25','.5','.85']:
        R=I.mpf(f)*G
        v=solve(b,min(R,I.mpf(rounded)) if f=='.85' else R,False)
        i=max(range(n-b+1),key=lambda a:b*v[a]-sum(v[a:a+b]))
        lv=b*I.ln(I.pi)/2-I.loggamma(1+I.mpf(b)/2)
        lower=lv+I.mpf(b*v[i]-sum(v[i:i+b])-2000*b)/M
        assert lower>lb
        d=b-1
        rad=1-I.exp(2*I.mpf(v[i+d]-v[i]+2000)/M)
        assert rad>0
        log_section=(d*I.ln(I.pi)/2-I.loggamma(1+I.mpf(d)/2)
                     +I.mpf(d*v[i]-sum(v[i:i+d])-2000*d)/M
                     +d*I.ln(rad)/2)
        assert log_section>{406:129,506:159,647:200,800:245}[b]
        for j in range(1,b):
            z=I.exp(2*I.mpf(v[i+j]-v[i]-2000)/M)
            ratio2=4*max(I.mpf(0),1-z)*I.exp(
                2*I.mpf(v[i]-v[i+j-1]+2000)/M)/(j*j)
            assert ratio2<1
        print(b,f,i,float(capval.a),float(lower.a))
```
