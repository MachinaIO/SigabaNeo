# Counting bad primitive prefixes in the planted embedding

**Theorem.** Take all 511 samples, 512 secret coordinates, prime modulus 3329, unit height and ambient dimension 1024. Let the cutoff be the physical (unnormalized) Part 6 Hermite envelope for a fully BKZ-reduced basis at width $\beta$, and take the terminal prefix rank $k=1024-\beta$. For **every integer width from 2 through 1007**, every matrix, and every planting with horizontal coordinates of magnitude at most three, there is a primitive prefix under the cutoff with nonzero, nonprimitive projected plant. The all-prefix failure probability is exactly one. At widths 406 and 647 the **number** of bad prefixes on each input exceeds $2^{635}$ and $2^{286}$ respectively. Even at the smaller GSA cutoffs specified below it exceeds $2^{240}$ and $2^9$. No assumption about a reduction trajectory or distribution of lattices enters these bounds.

At width 1024 the mean bad count is below $2^{-1900}$. Thus for the full 1024-dimensional family the smallest width for a 99% first-moment certificate lies in **[1008,1024]**. Only 1024 is certified here. For the repo's equal-block loop, the only divisor of 1024 in that interval is 1024, if using this same determinant family. Part 6 establishes its cutoff for overlapping exact BKZ blocks. A slide approximation factor on the first vector alone does not prove that cutoff for slide prefixes. A different, tighter cutoff requires a new comparison. Deleting samples first gives a proven width 647 at 99% in dimension 647, with empty prefix. These are different experiments. [Part 6](wall1_prefix.md) · [Part 36](wall1_lower_bound.md) · [Part 39](wall1_projected_reference.md)

## A lower bound on the mean from distinct witnesses on every input

Write $L=L_0\oplus\mathbb Zu$, where $L_0$ is horizontal, of rank $N=d-1$ and determinant $D=q^m$. Fix any HKZ basis of $L_0$ and write $V_j=\langle b_1,\ldots,b_j\rangle_{\mathbb Z}$, $H_j=\det V_j$. For every signed integer $a$ with $|a|\ge2$ take
$$
 B_a=V_{k-1}+\mathbb Z(u+a b_k).
$$
This extends to a basis by a unimodular shear and permutation. Its height-one slice is $u+a b_k+V_{k-1}$, so all these sublattices are distinct. In the free quotient $[b_k]$ is a basis element and $[u]=-a[b_k]$. Hence the plant survives, and a competitor of exactly $1/|a|$ times its projected length exists. Orthogonalizing the last generator gives $\det B_a\le |a|H_k+96 H_{k-1}$ since $\|u\|^2\le9208$. Extending the $a=2$ construction from [Part 9](wall1_planted_prob.md) gives, pointwise and therefore also in expectation,
$$
 N_{\rm bad}(X)\ \ge\ 2\max\{0,\lfloor (X-96H_{k-1})/H_k\rfloor-1\}.
$$
The chance of failure for each of these matrix-dependent witnesses is one. This bypasses both the multiplicity of bases and the need to estimate a rare-event probability. None of the witnesses contains $u$. For a proposed positive result, the separate capture argument in Part 30 needs its hypotheses, including $k\le\beta$ and ambient uniqueness. Terminal identification of a projected pair also needs a lift argument if the requested output is the ambient plant. [Capture](wall1_contained.md)

Use logarithms to base two. Upper bounds $h_j$ on $\log H_j$ follow from $h_0=0$ and
$$
 h_j=(1-1/r)h_{j-1}+\log D/r+c_r,\qquad r=d-j,
$$
where $c_r$ is the Part 6 half-log Hermite bound and $c_1=0$. This uses HKZ only to construct witnesses. For a **lower** bound on the Part 6 cutoff, any feasible normalized prefix profile $S$ gives $x=(k/d)\log D+S_k\le\log X$. The following bounds are rounded outwards. The final column uses the unrounded bounds.

| Width | $k$ | lower $x$ | upper $h_k$ | upper $h_{k-1}$ | certified positive $a$ through |
|---:|---:|---:|---:|---:|---:|
| 406 | 618 | 5427.000 | 4791.552 | 4785.796 | $2^{635}$ |
| 647 | 377 | 3471.603 | 3185.403 | 3177.930 | $2^{286}$ |
| 1007 | 17 | 158.887 | 157.737 | 148.491 | 2 |

The executable certificate at the end checks *every* width in the stated range. It constructs a feasible profile with downward-rounded constants by rounding the required lower bound on each preceding value upwards. Subtracting its endpoint chord preserves feasibility. A profile feasible through width $b$ remains feasible at every smaller width. Subdivision only sharpens the lower bounds. At the full width the sole prefix is zero, so the mean equals the probability of a competitor in the ambient ball. The cube bound of Part 36 gives $V_d(96+16)^d/(2q^{511})<2^{-1900}$ for each plant.

## Exact discrete mean and the modular correction

Condition on $u$. Enumerate integral rank-$k$ subgroups $B$ of determinant at most $X$ once each by row HNF, excluding those whose real span $P$ contains $u$. This is finite since the primitive Plücker coordinates of $P$ are integers bounded by $X$, and the index in $S=P\cap\mathbb Z^d$ is bounded by $X/\det S$. Let $w$ be the basis rows, $U_B$ representatives of the nonzero cosets of $S/B$, and $C_B$ the integer competitor lifts $z$ with orthogonal component of length at most $\|\pi u\|$, $z\notin B+\mathbb Zu$, and parallel component in the half-open fundamental parallelepiped of $B$. This bounds both components; without reducing lifts the cylinder count is infinite for positive rank. Once $B$ is primitive in $L$, each projected competitor has exactly one such lift in $L$. Fractional plant multiples must be kept. No division by the size of a basis orbit or by a universal competitor multiplicity is valid.

For any finite list $T$ of triples put $Y_i=y_i-t_i s$, $E_i=x_i-t_i e$, and $p(T)=\mathbf1_{a=b}q^{-ma}$, where $a=\mathrm{rk}_qY$, $b=\mathrm{rk}_q[Y\ E]$. Each of the $m$ independent rows of the design must solve one consistent linear system. Thus $p$ is the exact joint membership probability, including for concatenated lists. With
$$
 J_B(F)=\sum_{I\subseteq F}(-1)^{|I|}p(w\cup I),
 \qquad
 \mathbb E_A N_{\rm bad}=\sum_B[J_B(U_B)-J_B(U_B\cup C_B)],
$$
the equality follows by inclusion-exclusion. The first term enforces membership and primitivity in $L$, and the second also forbids competitors. Averaging this finite expression over the CBD plant gives the unconditional mean. Keeping just one competitor at a time gives an upper bound, even with exact primitivity. The displayed equality specifies the mean without enumerating matrices; its enormous alternating sums have not been numerically evaluated. [Planted tuple identity](planted_qary_sieve.md) · [Q1 and Q2](qary.md)

Replacing ranks in $p$ by rational ranks defines $p_0$. The exact modular error in each summand is obtained by substituting $p-p_0$ for $p$ in both terms. A consistent drop of one in $a$ multiplies the positive rational weight by $3329^{511}$ (over 5979 bits); a change of consistency can turn a zero weight positive. At 406 the latter accounts for **the entire bad count**: since $u\notin P$, the rational shear $(x,y,t)\mapsto(y-ts,x-te)$ is injective on $P$, and already the basis has joint rational rank 618, versus at most 512 in $Y$. Appending points cannot remove this inconsistency. Every surviving tuple must lose at least 106 joint ranks modulo $q$. The rational-rank expression is exactly zero while its error exceeds $2^{635}$ at the proven cutoff. This is stronger than simply failing Q2's sufficient norm test. For the one-competitor tuple the uniform sufficient row bounds on the *sheared* matrices are strictly below $3329^{1/619}<1.014$ at 406 and $3329^{1/378}<1.022$ at 647. A prefix determinant and projected radius imply neither bound. For $k\le512$ the forced 106-rank mechanism no longer applies. Even there the witness tuple $(w,b_k)$ has a planted rational relation; it cannot be priced as $k+1$ independent checks.

## What the continuous count would predict

For comparison only, on a Haar lattice of determinant $D$ the exact mean number of rank-$k$ prefixes is $A(d,k)X^d/D^k$, with the unit-ball and zeta product $A$ in Part 5. If one additionally models the quotient background by a uniform intensity $s/D$ at prefix determinant $s$, a *fixed* physical radius $R$ gives a volume count $V_\beta R^\beta s/(2D)$ of signed pairs. Integrating against the prefix density multiplies the product of the prefix mean and the shell count at $s=X$ by $d/(d+1)$. The radius here is only a numerical proxy $R=\sqrt{1.5\beta}$ for the projected plant. Neither this substitution nor the background intensity is a theorem about the marked quotient. The count measures incidences; a shell population exceeding one is not a probability. [Part 5 formulas](wall1_sublattice.md) · [Kim's Haar mean-value theorem](https://arxiv.org/abs/2005.10874)

| Width | Cutoff | $\log X$ | log Haar prefix mean | log volume count per prefix at cutoff |
|---:|---|---:|---:|---:|
| 406 | Part 6 | 5427.00 | 1,087,402 | 391.56 |
| 406 | GSA | 5032.35 | 683,280 | −3.09 |
| 647 | Part 6 | 3471.60 | 548,181 | −1000.33 |
| 647 | GSA | 3194.43 | 264,356 | −1277.50 |

The GSA rows set $X=D^{k/d}\delta^{k\beta}$ with $\log\delta=[\log(\pi\beta)/\beta+\log(\beta/(2\pi e))]/[2(\beta-1)]$. At these numerical cutoffs the signed-integer witness lower bounds still apply pointwise. Thus at both benchmark widths even an exact planted integral with perfect error control could not give the requested small upper bound. For widths 1008–1023 the proof leaves the mean unresolved. A lack of witnesses from this determinant estimate does not supply an upper bound. Proving closure there needs control of both divisible projected plants and other short quotient lines in the discrete sum. At 406 and 647, improvements for a concrete reducer must instead exclude or control the selection of the exhibited bad prefixes, or prove a sufficiently smaller cutoff.

## Reproducible certificate

Python 3 with NumPy and mpmath. Scaled endpoints are enclosed by truncating an interval endpoint and adding a full outward unit. The recurrence uses integer ceiling division.

```python
from fractions import Fraction as F
from math import ceil
from mpmath import iv
import numpy as np
iv.dps = 45
d, T = 1024, 10**8
log = lambda x: iv.ln(x)/iv.ln(2)
lo = lambda x: int(x.a)-1
hi = lambda x: int(x.b)+1
C = [iv.mpf(0)]*2
for h in range(2,d+1):
    if h<=8:
        p=[(4,3),(2,1),(4,1),(8,1),(64,3),(64,1),(256,1)][h-2]
        C.append(log(iv.mpf(p[0])/p[1])/(2*h))
    else:
        C.append(log(2/iv.pi)/2+log(iv.gamma(2+iv.mpf(h)/2))/h)
L=511*log(3329)*T
low=np.array([lo(c*T) for c in C],dtype=np.int64)
H=[0]
for h in range(d-1,0,-1):
    H.append(ceil(F((h-1)*H[-1]+hi(L),h))+hi(T*C[h]))
def check(a,b):
    v=[0]*(d+1)
    for j in range(d-1,0,-1):
        h=np.arange(2,min(b,d-j+1)+1,dtype=np.int64)
        # Inputs small enough for signed 64-bit products.
        assert abs(v[j])<8*10**15 and max(abs(x) for x in v[j:j+len(h)+1])<8*10**15
        s=h*v[j]-np.array(v[j+1:j+1+len(h)])-h*low[h]
        v[j-1]=int(max(-((-s)//(h-1))))
    missed=[]
    for beta in range(a,b+1):
        k=d-beta
        x=F(k*lo(L)+d*v[k]-(d-k)*v[0],d*T)
        M=iv.power(2,iv.mpf(x.numerator)/x.denominator-iv.mpf(H[k])/T)-96*iv.power(2,iv.mpf(H[k-1]-H[k])/T)
        if M.a<2: missed.append(beta)
        if beta==b and beta in [406,647,1007]:
            print(beta,float(x),H[k]/T,H[k-1]/T,float(log(M).a) if M.a>0 else 0)
    if missed:
        assert a<b
        mid=(a+b)//2
        check(a,mid)
        check(mid+1,b)
for a,b in [(2,406),(407,647),(648,1007)]: check(a,b)
for b,t in [(406,240),(647,9)]:
    k=d-b
    g=(log(iv.pi*b)/b+log(b/(2*iv.pi*iv.exp(1))))/(2*(b-1))
    x=k*L/(d*T)+k*b*g
    assert (iv.power(2,x-iv.mpf(H[k])/T)-96*iv.power(2,iv.mpf(H[k-1]-H[k])/T)).a>2**t
```
