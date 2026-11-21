# Unfolding all size-reduced bases at Wall 1

The absolute first moment for the Part 6 profile polytope fails at **all four widths**, even after identifying column signs. The integral does give a simultaneous-over-bases terminal lower bound. Its 99% crossing in radius can be bracketed quite narrowly, far below GSA. This is a statement about Haar probability on unimodular lattices and the specific relaxation defined below.

| Horizontal width | Certified terminal radius | Radius where mean already exceeds 1 | Common prefix lower bound | Terminal length at density maximum | GSA | Linear target | Quadratic target |
|---:|---:|---:|---:|---:|---:|---:|---:|
|406|.00525|.0060|.00089|.318|.434|.859|10.614|
|506|.01281|.0150|.00430|.852|.960|.959|13.224|
|647|.02975|.0361|.01046|2.273|2.143|1.084|16.905|
|800|.07728|.0978|.03416|4.942|4.015|1.206|20.898|

The first three numerical columns give one-sided bounds. The maximum column has absolute error below .004, and the last three columns have absolute error below .001. All lengths are in determinant-one units. The probability exceeds 99% jointly for the four terminal certificates and every prefix index through the respective terminal index. The GSA column alone assumes the geometric series model. The physical length unit is $a=3329^{511/1023}$. The target columns are $\sqrt{6b}/a$ and $(1+1.5b)/a$ for horizontal rank $b$ after projection (Part 47 width including height is $b+1$). Using the Rankin note's alternative quadratic convention subtracts $1.5/a$. The quadratic comparison uses a mean squared plant length, not a tail quantile. [Normalization and benchmarks](wall1_rankin_route.md)

## Absolute mass

Use columns, zero-based indices, $n=1023$, $k=n-b$, $x_i=\log g_i$, $S_j=\sum_{i<j}x_i$, $S_0=S_n=0$. For $2\le d\le\min(b,n-i)$ impose
$$
 (d-1)x_i\le H_d+\sum_{i<h<i+d}x_h,
 \qquad H_d=d c_d
$$
with the exact small-dimensional and Blichfeldt constants of Part 6. These include every right truncation of every block and imply all the Part 6 prefix envelope and ratio inequalities. Impose $x_k<r$ for the bad set. Size reduction can always be achieved by column additions preserving all projected block lattices and GS lengths. Take the full unit cube of upper coefficients. This relaxation discards the shortest-vector tests involving those coefficients. [Prefix inequalities](wall1_prefix.md) · [Affine profile bounds for BKZ](https://perso.ens-lyon.fr/damien.stehle/downloads/bkz.pdf)

With rotations integrated to one and Lebesgue measure on $S_1,\ldots,S_{n-1}$, the unfolded intensity of positively oriented bases is
$$
 K_n e^F,\qquad K_n=\prod_{d=2}^n\frac{2\pi^{d/2}}{\Gamma(d/2)\zeta(d)},\qquad
 F=\sum_i(n-1-2i)x_i=2\sum_{j=1}^{n-1}S_j .
$$
Indeed unfold the signed primitive first column, with intensity $dv/\zeta(d)$. Given that column, quotient completions are oriented bases of the normalized Haar quotient with a unit torus of lift phases. Summing lifts unfolds that torus to Lebesgue measure in the first row of upper coefficients (translations of a unit lattice cell, equivalently a unit triangular change of coordinates). Repeat down to dimension one, where orientation fixes the column. At remaining rank $d=n-i$ the normalized radial variable is $s_i=\exp(x_i+S_i/d)$. Each log radius contributes the sphere area times $s_i^d/\zeta(d)$, and the change from the first $n-1$ log lengths to log radii is unit triangular. Multiplication gives the stated exponent. Passing to prefix sums also has determinant one. Equivalently $F=-\sum_{j=1}^{n-1}j(n-j)(x_j-x_{j-1})$, with the sign of the column convention in the Lean chart. Unfolding counts each positive basis once, so the integral upper bounds the existence probability. Any sign orientation gives the same bad profiles. [Primitive disintegration](wall1_haar_prefix_law.md) · [Column coordinates](../../SigabaNeo/Lib/Lattices/Reduction/Rogers/ColumnHaarCoordinates.lean) · [Siegel mass](../../SigabaNeo/Lib/Lattices/Reduction/Rogers/SiegelMass.lean)

## Maximizer and integral bounds

Here is a one-parameter construction of the exact LP maximizer. Set $v_{n-1}=0$. Working backward, put
$$
 v_i=\min_d (H_d+\sum_{i<h<i+d}v_h)/(d-1)-t\,\mathbf1_{i=k}.
$$
Subtract the overall mean of $v$ to obtain $x^*$ and take its prefix sums $U$. At $t=0$ this maximizes the uncut problem. At $t\ge0$ it maximizes the closed problem with cap $r=x_k^*$. Indeed every interior prefix row has a tight constraint. At $j=i+1$ the block constraint bounds $S_j$ by the weighted average of $S_i,S_{i+d}$ with weights $(d-1)/d,1/d$, plus $H_d/d$. At the cut row the cap bounds $S_j$ by $S_i+r$. A positive maximum of $S-U$ must propagate to its left neighbor using the tight row, contradicting the endpoints. Thus $S\le U$ coordinatewise. Since all coefficients in $2\sum S_j$ are positive, the maximizer is unique. A strict active cap gives the same supremum by continuity. Increasing $t$ by $h$ decreases $v_k$ by $h$, earlier entries by amounts in $[0,h]$ by the averaging recursion, and later entries by zero. Hence the centered cut coordinate decreases continuously by at least $h(n-k-1)/n$, covering every lower cap. The maximum resembles GSA in terminal scale in this table, but the truncated suffix has a distinct shape. For example its last log drop is $H_2$, independent of width. The maximizer describes density in log coordinates and carries no inference of typicality for actual reduced bases.

The containing orthant integrates exactly to $K_n e^{F(U)}2^{-(n-1)}$. This upper bound also holds for a supersolution with one dominating row at every interior index, by the same maximum argument. For a lower bound use any strictly feasible center and vary the first $n-1$ log lengths independently by at most $1/M$, $M=10^7$, correcting the last to maintain determinant. Each coordinate changes by at most $n/M$, so the block residual changes by at most $2dn/M$. A slack of $.001d$ suffices. The loss in $F$ is less than 1100 (even the bound $2n^2/M$ suffices, by the sum of absolute perturbations). The box volume is $(2/M)^{n-1}$. These estimates concern absolute intensity, with no division by the uncut profile mass.

At the radii in the second numerical column the resulting **log mean exceeds 34,000** in every row. Even the $2^{n-1}$ equivalent oriented sign choices cannot explain the excess. Monotonicity rules out an exponentially small integral at, for example, half the maximizing terminal length at every listed width. Large relaxed mass gives no lower bound on the probability of an actual bad BKZ basis. Further deterministic constraints outside this polytope or coefficient-dependent avoidance weights could change the conclusion.

For the prefix column use a single Haar ambient event $\lambda_1>7$ and Part 6 ratio propagation. Siegel on signed pairs bounds its failure by $V_n7^n/2$. The script propagates integer upper bounds on $M\log(g_0/g_j)$ backward from each target using translation invariance (the array index is distance to the target). The failure probability for the joint table is at most $V_n7^n/2+4e^{-140}<.01$. No transfer from Haar to the finite graph ensemble is used. The width-1000 graph certificate of Part 48 stands separately. No listed width clears either benchmark here, and the selected quotient law and lifting questions remain open. [Part 48](wall1_null_terminal.md) · [Part 47](wall1_decoupled.md) · [Frontier](../PROOF_GAP.md)

## Reproducible interval certificate

Python 3 with mpmath interval arithmetic. The suffix sums in the code are uncentered. In supersolution mode adding $d$ integer units before floor division compensates for both rounding the constant and rounding the quotient. In lower-box mode both roundings are inward. The uncut numerical maximum uses the inward recurrence without slack. Its uncentered entries differ from the exact recursion by at most $2n/M$ by induction through averages, hence the centered error is at most $4n/M$. For normalization the code brackets every $\zeta(d)$ between 1 and 2.

```python
from mpmath import iv as I
from fractions import Fraction
I.dps=40
n=1023; M=10**7
h=[0,0,Fraction(4,3),2,4,8,Fraction(64,3),64,256]
C=[0,0]; A=I.mpf(0)
for d in range(2,n+1):
    t=I.mpf(d)/2
    z=h[d] if d<9 else None
    H=I.ln(I.mpf(z.numerator)/z.denominator)/2 if z else t*I.ln(2/I.pi)+I.loggamma(2+t)
    C.append(int((M*H).a)) # positive, truncate lower endpoint
    assert C[-1] <= M*H and M*H < C[-1]+1
    A+=I.ln(2)+t*I.ln(I.pi)-I.loggamma(t)
def shape(b,dent,margin,upper=False):
    k=n-b; S=[0]*(n+1)
    for i in reversed(range(n-1)):
        v=min((C[d]+(d if upper else 0)-margin*d+S[i+1]-S[i+d])//(d-1) for d in range(2,min(b,n-i)+1))
        S[i]=S[i+1]+v-(dent if i==k else 0)
    X=[I.mpf(n*(S[i]-S[i+1])-S[0])/(n*M) for i in range(n)]
    return X[k],sum((n-1-2*i)*x for i,x in enumerate(X))
rows = [
    (406,63281250,'.00525','.0060','.00089','.318','.434','.859','10.614'),
    (506,55312500,'.01281','.0150','.00430','.852','.960','.959','13.224'),
    (647,50703125,'.02975','.0361','.01046','2.273','2.143','1.084','16.905'),
    (800,45390625,'.07728','.0978','.03416','4.942','4.015','1.206','20.898')]
a=I.mpf(3329)**(I.mpf(511)/n)
half=I.mpf(n)/2
assert half*I.ln(I.pi)+n*I.ln(7)-I.loggamma(1+half)-I.ln(2)<-20
for b,dent,r,R,prefix,opt,gsa,linear,quad in rows:
    y,F=shape(b,dent,0,True)
    assert I.exp(y)>I.mpf(r) and A+F-(n-1)*I.ln(2)<-140
    z,f=shape(b,dent-3000000,10000)
    mass=A-n*I.ln(2)+f-1100+(n-1)*I.ln(I.mpf(2)/M)
    assert I.exp(z+I.mpf(1)/M)<I.mpf(R) and mass>34000
    x,_=shape(b,0,0)
    err=I.mpf([-4*n,4*n])/M
    assert abs(I.exp(x+err)-I.mpf(opt))<I.mpf('.004')
    G=I.exp((2*b-n-1)*(I.ln(I.pi*b)/b+I.ln(b/(2*I.pi*I.exp(1))))/(2*(b-1)))
    for value,label in zip((G,I.sqrt(6*b)/a,(1+I.mpf('1.5')*b)/a),(gsa,linear,quad)):
        assert abs(value-I.mpf(label))<I.mpf('.001')
    p=[0]
    sums=[0,0]
    for j in range(1,n-b+1):
        p.append(min((C[d]+d+sums[j]-sums[j-d+1])//(d-1)
                     for d in range(2,min(b,j+1)+1)))
        sums.append(sums[-1]+p[-1])
    assert 7*I.exp(-I.mpf(max(p))/M)>I.mpf(prefix)
```
