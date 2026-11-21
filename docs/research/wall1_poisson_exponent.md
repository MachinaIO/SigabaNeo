# A row exponent and a packing exclusion for the rank-1023 Haar integral

The Part 50 boxes witnessing over 34,000 log units of relaxed intensity have **zero full SVP-test weight**, at all four widths. The same conclusion holds throughout each Part 59 modal prefix slab at its own terminal cap. A cubic spherical-code bound proves these exclusions deterministically. Removing the excluded profiles *before* integrating gives the following individual certificates for every fully BKZ-reduced basis of a Haar unimodular lattice. The new radii are one-sided bounds on the transition.

| Width | Previous A5 note | Certified radius | Upper bound on log bad mass | GSA | Linear target |
|---:|---:|---:|---:|---:|---:|
|406|0.005832301|0.005933200|−4.6086|0.434|0.859|
|506|0.015428983|0.015621412|−4.6097|0.960|0.959|
|647|0.039231048|0.039603438|−4.6098|2.143|1.084|
|800|0.139941828|0.140797866|−4.6098|4.015|1.206|

The independent-lift calculation itself certifies a total exponent above 227 on each entire Part 50 box. The zero-weight theorem is stronger for integration, but does not establish the conjectured size of the A5 exponent. The integral over all remaining profiles at the comparison targets is open.

## Combining lifts over rows

Write \(x_i=\log g_i\), \(S_j=\sum_{i<j}x_i\), and let \(H_l\) be any rigorously valid upper bound on \(\log(\lambda_1^l/\det)\) in dimension \(l\), with \(H_1=0\). At start \(j\), use the cut immediately after its first coordinate. Reveal rows in decreasing index order. For any eligible lower truncation of length \(1\le l\le\min(b-1,n-1-j)\), its shortest vector, chosen with a measurable tie rule, has norm relative to \(g_j\) at most
\[
 a_{jl}=\exp\big((H_l+S_{j+1+l}-S_{j+1})/l-x_j\big).
\]
The circle of circumference \(g_j\) has hit probability at least \(p_j=\min(1,2\sqrt{(1-\min_l a_{jl}^2)_+})\). Indeed the integer suffix is fixed given the revealed rows and its image in the fresh circle is Haar. Thus \(W\le\prod_j(1-p_j)\) by iterated conditioning, including after survival of the larger-index starts. A genuine larger list is available if the lower block has several short successive minima. At any fixed cut, take shortest suffixes successively outside the rational span of those already taken. Since projected-ball probability decreases with suffix length, the resulting successive-minimum lengths minimize each ordered length among independent lists of the same size. This proves optimality for that reveal. For a multidimensional upper torus one must also know its projected-ball measure.

On every Part 50 witness box the script verifies at least 1021 starts with \(\min_l a_{jl}\le e^{-1/200}\). Hence the combined row exponent is at least \(-1021\log(1-2\sqrt{1-e^{-1/100}})>227\). More generally, a rank-\(m\) suffix supplies at most \(m\) jointly independent shifts. To exceed 34,000 in one list even at rank 799 requires at least one miss probability below \(e^{-34000/799}\). Distinct primitive suffixes give pairwise independence up to sign but can contain dependent triples. Lower bounds on their count do not prove the required near-coverage. Also, the volume-to-covolume ratio counts lifts with multiplicity. Only a ball embedding almost everywhere gives that ratio directly as the hit probability. [Fixed-cut theorem](wall1_poisson_smallball.md)

## Excluding profiles by a cubic spherical-code bound

Scale a rank-\(d\) lattice to minimum one. Put \(D=d+1\), \(s=4/(5\sqrt D)\), \(a=1/(Ds)\), and \(r=[2(1-s)]^{-1/2}\). The points of any translate in the radius-\(r\) ball lift to the radius-\(r\) sphere in one extra dimension by appending \(\sqrt{r^2-|x|^2}\). Distances can only increase. After dividing by \(r\), distinct inner products are at most \(s\).

Set \(f(u)=(u-s)(u+a)^2\) and \(c=(2a-s)/D-sa^2\). For a code of size \(m\), summing \(f\) over ordered pairs gives at most \(mf(1)\) and at least \(cm^2\). For the latter inequality expand in the kernels
\[
 1,\quad u,\quad u^2-1/D,\quad u^3-3u/(D+2).
\]
The coefficients are respectively \(c,a^2-2as+3/(D+2),2a-s,1\), all positive in the dimensions used. The kernels are Gram kernels of the constant, vector, traceless square and traceless cube. Explicitly the last tensor has entries \(x_i x_j x_k-(x_i\delta_{jk}+x_j\delta_{ik}+x_k\delta_{ij})/(D+2)\) on the unit sphere. Summing a Gram kernel gives a squared norm. Averaging the translated-ball count over a fundamental domain now gives \(V_dr^d/\det\le f(1)/c\). Undoing the scale proves the block inequality
\[
 d x_i-(S_{i+d}-S_i)\le H_d^{\rm pack}
 =\log(f(1)/c)+\tfrac d2\log(2(1-s)/\pi)+\log\Gamma(1+d/2)
\]
whenever the first vector is shortest in the projected truncation. The certificate uses the smaller of this and the Part 50 bound. The polynomial and angle were chosen for simple finite-dimensional verification. [Spherical-code packing bounds, Cohn and Zhao](https://arxiv.org/abs/1212.5966)

For the four Part 50 boxes in width order, the violating (zero-based start, rank) pairs are (26,406), (7,506), (377,646), and (224,799). Even after allowing the entire box perturbation, the log residual exceeds the improved bound by respectively 3, 3, 4, and 5. Thus no coefficient choice survives these boxes. In particular, conditional on either pair of diagonal blocks at any internal cut of the violating truncation, the void probability is zero: every cross block gives a competitor. This also describes the distinction between the exact void exponent and A5. Coverage by the union of all suffix events need not give coverage by an independent subfamily. Part 50's 34,000 figure concerns relaxed intensity on its witnesses at radii 0.0060, 0.0150, 0.0361 and 0.0978. Part 59 concerns modes of a different density at different caps. Neither result locates a fixed fraction of the full weighted integral. [Part 50](wall1_volume_method.md) · [Part 59](wall1_volume_product.md)

| Width | Part 59 exponential pass cap: feasible upper bound on \(S_{k+1}\) | Old modal lower endpoint | Part 59 HKZ cap: feasible upper bound | Old modal lower endpoint |
|---:|---:|---:|---:|---:|
|406|356|357.34|413|419.68|
|506|449.7|449.76|540|544.63|
|647|404|405.31|506|508.54|
|800|245.1|245.56|370.4|370.94|

## Integration and reproducibility

Let \(D_*\) impose the strengthened block inequalities and terminal cap. Outside this set the bad-event integrand vanishes. Inside, the joint weight is at most the smaller of the Part 55 partition weight and the row product above. For the numerical upper bound retain the partition weight on \(D_*\). At fixed partition cuts its internal integrals are exactly the HKZ normalizations after dropping the internal caps. With consecutive ranks \(d_h\), each interior cut has coefficient \(c_j=d_{\rm left}+d_{\rm right}\). Integrating its half-line up to \(U_j\) gives \(e^{c_j U_j}/c_j\). The constant is \(2^{1-h}K_n/\prod K_{d_h}\) for \(h\) pieces. This directly bounds the integral of the pointwise minimum and the sign-divided bad-basis count. The gain in the table comes from the support restriction. [Partition identity](wall1_volume_svp_weights.md)

For clarity, the prefix supersolution uses the same maximum principle with the new constants. At each ordinary row a minimizing rank makes the supersolution satisfy the reverse block inequality; at the dent its terminal log length dominates the cap. A positive maximum of \(S-U\) propagates to its left neighbor by the corresponding convex-average inequality, contradicting the zero boundary. The old witness box uses the Part 50 integer center and log-coordinate perturbations of at most \(n/10^7\) after determinant correction. The residual changes by at most \(2dn/10^7\). The code bounds zeta by the integral test through dimension 32 and by \(0\le\log\zeta(d)\le3\,2^{-d}\) thereafter. All certificate decisions use integers or outward interval comparisons. The decimal output is for display.

```python
from fractions import Fraction
from mpmath import iv as I

I.dps = 45
n, M, m = 1023, 10**9, 10**7
small = [0, 0, Fraction(4,3), 2, 4, 8, Fraction(64,3), 64, 256]
old, C, A = [0,0], [0,0], [0,0]
for d in range(2,n+1):
    u = I.mpf(d)/2
    if d < len(small):
        z = Fraction(small[d])
        H = I.ln(I.mpf(z.numerator)/z.denominator)/2
    else:
        H = u*I.ln(2/I.pi)+I.loggamma(2+u)
    old.append(int((m*H).a))
    assert old[d] <= m*H and m*H < old[d]+1
    D = d+1
    s = 4/(5*I.sqrt(D))
    a = 1/(D*s)
    c = (2*a-s)/D-s*a*a
    assert c > 0 and 2*a-s > 0 and a*a-2*a*s+I.mpf(3)/(D+2)>0
    P = I.ln((1-s)*(1+a)**2/c)+u*I.ln(2*(1-s)/I.pi)+I.loggamma(1+u)
    bound = P if P < H else H
    C.append(int((M*bound).b)+1)
    assert C[d] > M*bound
    if d<=32:
        partial = sum(I.mpf(j)**(-d) for j in range(1,65))
        lo = partial+I.mpf(65)**(1-d)/(d-1)
        hi = partial+I.mpf(64)**(1-d)/(d-1)
        lz = I.mpf([I.ln(lo).a,I.ln(hi).b])
    else:
        lz = I.mpf([0,(3*I.mpf(2)**(-d)).b])
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u)-lz)

def recurrence(b,dent,original=False):
    T = [0]*(n+1)
    for i in reversed(range(n-1)):
        ds = range(2,min(b,n-i)+1)
        if original:
            v = min((old[d]-10000*d+T[i+1]-T[i+d])//(d-1) for d in ds)
        else:
            v = min((C[d]+d-2+T[i+1]-T[i+d])//(d-1) for d in ds)
        T[i] = T[i+1]+v-(dent if i==n-b else 0)
    return T

def envelope(b,dent):
    T = recurrence(b,dent)
    return [I.mpf((n-j)*T[0]-n*T[j])/(n*M) for j in range(n+1)]

# width, Part 50 lower-box dent, violating start/rank/margin,
# two Part 59 (dent, radius in billionths, upper prefix) witnesses,
# final dent/radius in billionths and partition cuts
rows = [
 (406,60281250,26,406,3,[(6307733310,5272503,356),(6071006227,5832182,413)],
  6034220356,5933200,list(range(13,170,13))+[183,197,212,618]),
 (506,52312500,7,506,3,[(5507766695,12846861,450),(5156325088,15428901,540)],
  5133616209,15621412,[12,518]),
 (647,47703125,377,646,4,[(5057827416,29833670,404),(4628124403,39230827,506)],
  4614294478,39603438,[377]),
 (800,42390625,224,799,5,[(4524703362,77676505,246),(3779105745,139940142,371)],
  3772651156,140797866,[224])]
for b,box,i,d,margin,witnesses,dent,r,cuts in rows:
    k = n-b
    T = recurrence(b,box,True)
    residual = d*(T[i]-T[i+1])-T[i]+T[i+d]
    assert I.mpf(residual-2*d*n)/m-I.mpf(C[d])/M > margin
    count = 0
    for j in range(n-1):
        # lambda_1 of an l-dimensional suffix starting at j+1
        # is at most exp(-1/200) g_j throughout the box.
        x = T[j]-T[j+1]
        if any(200*(C[l]*m + M*(T[j+1]-T[j+1+l]-l*x+2*l*n)) <= -l*M*m
               for l in range(1,min(b-1,n-j-1)+1)):
            count += 1
    assert count >= 1021
    hit = 2*I.sqrt(1-I.exp(-I.mpf(1)/100))
    assert -1021*I.ln(1-hit) > 227
    for dt,cap,upper in witnesses:
        U = envelope(b,dt)
        assert I.exp(U[k+1]-U[k]) > I.mpf(cap)/M
        # The two tight comparisons use tenths of a log unit.
        limit = {(506,12846861):'449.7',(800,77676505):'245.1',
                 (800,139940142):'370.4'}.get((b,cap),str(upper))
        assert U[k+1] < I.mpf(limit)
    U = envelope(b,dent)
    assert I.exp(U[k+1]-U[k]) > I.mpf(r)/M
    ends = [0]+cuts+[n]
    L = A[n]-len(cuts)*I.ln(2)
    for p,q in zip(ends,ends[1:]):
        assert 1 <= q-p <= b
        L += (q-p)*(U[p]+U[q])-A[q-p]
    L -= sum(I.ln(z-x) for x,z in zip(ends,ends[2:]))
    assert L < -I.ln(100)
    print(b,r,float(L.b))
```
