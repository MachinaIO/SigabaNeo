# Haar bounds for MW reduction and a terminating terminal-block variant

Let the ambient lattice have rank $n=1023$, determinant one and Haar law. Write $b=\beta$, $k=n-b$, $r=k+1$, $q=g_k$, $D=\det P$ for the rank-$r$ prefix $P$, and $h_j=V_j^{-1/j}$ for the unit-volume ball radius. The terminal quotient has Gaussian radius $R_T=h_b(q/D)^{1/b}$. Each row gives **two simultaneous lower bounds with probability at least 0.99 per width, uniformly over bases satisfying the row's predicate**. The third column of numbers divides the absolute bound by the Part 84 GSA reference. All entries round down.

| Predicate | $b$ | $q$ | $q/R_T$ | $q/G_b$ |
|---|---:|---:|---:|---:|
| MW |300|0.02564515|0.02754835|0.19885064|
| MW |325|0.03985949|0.03907396|0.22095292|
| MW |350|0.05920620|0.05311913|0.24278428|
| MW |375|0.08471671|0.06973447|0.26448133|
| MW |400|0.11749247|0.08891953|0.28617390|
| MW |406|0.12656799|0.09390205|0.29139210|
| MW |425|0.15870225|0.11062969|0.30797676|
| MW |450|0.20958694|0.13478752|0.32999931|
| MW |475|0.27145565|0.16128614|0.35233426|
| MW |500|0.34569490|0.19000024|0.37507069|
| MW |506|0.36551297|0.19720537|0.38059512|
| MW |512|0.38626645|0.20465252|0.38626645|
| Terminal variant |647|0.58986376|0.20945819|0.27531227|
| Terminal variant |800|1.01834742|0.23554251|0.25362356|

No integer width from 300 through 512 reaches $0.85G_b$ **with this certificate**. At 406 and 506 it reaches 34.28% and 44.78% of the target. The internal shape integration improves the endpoint $b=512$ from 0.386149 (determinant alone), but leaves the absolute radii at 406 and 506 unchanged to eight places. For the new algorithm the target exceeds the certificate by factors of about 3.09 and 3.35. Optimal uniform radii are unknown.

## MW witnesses and the normalized prefix

MW Algorithm 1 alternates forward primal and backward dual tours. Lemma 1 supplies Definition 1 under its stabilization condition. The latter definition allows an existential shortest-first change of the whole first block before projection. Thus the original interior rows cannot be treated as a primal BKZ flag. In particular $q$ need not be the terminal minimum. For $k<b-1$ the shear in Part 86 still rules out any positive uniform MW bound at the two wider widths. [MW, Algorithm 1, Definition 1 and Lemma 1](https://iacr.org/archive/eurocrypt2016/96650251/96650251.pdf) · [Part 86](wall1_dual_pinning.md)

For $m=r-b\ge0$, write $B_i$ for the witness block, $V_i$ for its determinant, $a_i$ for the removed shortest length and $U_i$ for the primitive prefix of the first $i$ witness vectors. All $U_i$ through $i=m$ lie in $P$, since earlier changes take place entirely inside it. Write $H_j$ for the audited Part 82 Hermite caps. Put $s=2H_b/[b(b-1)]$. The shared rank-$(b-1)$ determinant and the two shortest tests give
$$V_m\le e^{H_b}q^b,\quad V_i/a_i\le e^{H_b/b}V_{i+1}^{1-1/b},\quad a_i\le e^{H_b/b}V_i^{1/b}.$$
Eliminating $a_i$ gives $V_i\le e^s V_{i+1}$. Therefore $a_i\le q e^{l_i}$, $l_i=2H_b/b+(m-i)s$ for $i<m$, and $D=V_m\prod_{i<m}a_i\le e^U q^r$, where $U=H_b+\sum_{i<m}l_i$. These are the simultaneous maxima for this scalar recursion considered in isolation, since its equalities are compatible as scalar assignments. Realizing those equalities by lattices is a further constraint. We use all audited lattice caps in the construction and rank-dependent exclusions below. Truncated primal HKZ caps on the original rows would require an extra hypothesis. [Part 82 and audit](wall1_small_d_caps.md)

Rescale $P$ to determinant one and write $w=q/D^{1/r}$. In these units the tail $B_m^*$ has minimum $1/w$. Every dual vector restricts integrally to the witness prefix. At its first nonzero pairing with a witness column $j$, it is orthogonal to all preceding columns and has length at least $1/a_j$ (here $a_j$ is also rescaled). If every pairing vanishes it belongs to $B_m^*$. Thus the unit-determinant dual of $P$ has minimum at least $e^{-L}/w$, where $L=l_0$ if $m>0$ and zero otherwise. This intrinsic test on a *single* prefix is available even when its MW witness is nonunique.

## Counting distinct prefixes and retaining the quotient law

Let $v_0=e^{-U/r}$. For a fixed unit prefix shape take the infimum of $w$ over admissible internal witnesses, allowing infinity for no witness. Enforcing just necessary internal conditions enlarges the bad event. Write $J=v_0/w\le1$ using the infimum. For the variant below one uses its internal dual test alone. In the Haar split at $P$, the shape is Haar at fixed determinant $D$, and the radial intensity is $n e^{d_r}D^{n-1}dD$, where $d_r=A_n-A_r-A_{n-r}-\log(2n)$ as in Part 84. Equivalently the unit dual of $P$ is the Haar quotient at its annihilator in the ambient dual. This identity applies to the unweighted primitive incidence measure. [Part 84](wall1_prefix_level.md)

For a determinant scale $e^y$, set $x=(y-U)/r$. Failure of $q\ge e^x$ implies $D\le e^y J^r$. Failure of $q/R_T\ge \exp(((b-1)x+y)/b)/h_b$ implies $D\le e^y J^{r(b-1)/n}$ by $q^b/R_T^b=q^{b-1}D/h_b^b$. The latter radial range contains both. Integrating **once per distinct primitive prefix** gives a probability bound $e^{d_r+ny}\mathbb E J^{p}$ with $p=r(b-1)$. This common event avoids spending 0.005 on each conclusion.

For $0<f<1$, bound the moment by $f^p+\Pr(J\ge f)$. On the second event use $v=v_0/f$ as the upper cap on normalized $q$. Limit arguments allow nonattained infima. If $Q_d(t)$ is the exact Haar minimum survival at radius $t$, the dual test contributes $Q_r(e^{-L}/v)$. We evaluate it from above using $1/[1+(t/h_d)^d/4]$ in dimensions at least three, by the primitive-pair second moment and $\zeta(d)<2$. Hermite gives zero above $e^{H_d/d}$. The Haar law in the split is exact. Its survival function is enclosed, not numerically assumed equal to this bound. [Part 46](wall1_haar_prefix_law.md)

There is also a joint primal/dual test. For any $1\le i\le m$ put $d=r-i$, $S=\sum_{j<i}l_j+i\log v$. In the unit prefix, the covolume $u$ of $U_i$ satisfies $f^r e^S\le u\le e^S$. The lower endpoint follows by bounding every complementary factor in $1=V_m\prod a_j$. In particular $a_j\ge e^{l_j-U}v^{1-r}$. Every nonzero vector in $U_i$ has length at least its last nonzero coefficient's GS height. Thus the normalized primal minimum is at least $t_1=e^{l_{i-1}-U}v^{1-r}e^{-S/i}$. The first-nonzero-pairing argument on the remaining witness gives a normalized quotient-dual minimum at least $t_2=e^{-S/d-l'}/v$, where $l'=l_i$ if $i<m$, and zero otherwise. The normalization uses $\det(P/U_i)^*=u$, with quotient denoting orthogonal projection.

Unfold primitive rank-$i$ sublattices inside the Haar rank-$r$ shape. Conditional on $u$, the normalized primal and quotient shapes are independent under this **unselected** measure. Integrating their necessary tests with the endpoints just derived bounds $\Pr(J\ge f)$ by
$$
 e^{A_r-A_i-A_d-\log(2r)+rS}(1-f^{r^2})Q_i(t_1)Q_d(t_2).
$$
This inner first moment bounds existence of an internal witness. The outer count retains multiplicity one per $P$. Taking minima over valid tests and split points improves the scalar recursion without treating overlapping MW windows as independent. The script screens the internal ranks numerically and verifies each chosen inequality using intervals. This optimization does not solve the full completion integral or assert global optimality.

## A reducer with a terminal minimum for widths above half rank

Assume $r=k+1\le b$. Start with a $3/4$-LLL-reduced basis (size reduction parameter $1/2$). Fix $c=10001/10000$. Repeat the following pair of oracle operations.

1. Keep the first $k$ columns, SVP-reduce the rank-$b$ terminal quotient, and lift its primitive shortest vector as column $k$ (zero-based). Now $q=\lambda_1(T)$.
2. In the resulting rank-$r$ prefix $P$, compute $z=\lambda_1(P^*)$. Its present hyperplane has primitive normal of length $1/q$. If $1/q\le c z$, return the current basis. Otherwise install the kernel of a shortest primitive normal as the first $k$ columns of $P$, complete unimodularly inside $P$, and repeat.

The two terminal tests hold on the *same returned basis*. The second step requires no primal-dual orthogonality within a common window. Each accepted kernel replacement decreases the potential $D_k$ by a factor greater than $c$, since a primitive hyperplane with normal of length $z$ has covolume $Dz$. The first step preserves $D_k$. Ties can be broken by coefficient order among shortest vectors and integer basis completion by Hermite normal form.

Here is an input-independent oracle count. Let $g_j^0$ be the initial LLL heights. Echelon reduction from the highest occupied row of any rank-$k$ sublattice gives distinct pivot indices $i_j\ge j$ in increasing order. In orthonormal GS coordinates its exterior product has a pivot minor of magnitude at least $\prod_j g^0_{i_j}$, by integrality of the pivot coefficients. LLL gives $g^0_{i_j}\ge 2^{-(i_j-j)/2}g^0_j$ and $i_j-j\le n-k$. Thus every new $D_k$ is at least $2^{-k(n-k)/2}$ times its starting value. There are at most $1+\lceil k(n-k)\log 2/(2\log c)\rceil$ iterations, each with two exact SVP calls in rank at most $b$. This is polynomially many calls, hence within the requested oracle budget. Arithmetic is exact in this oracle model. A bit-complexity bound independent of the encoding of a real Haar input is not implicit.

At return, $q\ge1/(c\lambda_1(P^*))$. Hermite gives $D\le c^r e^{H_r}q^r$. Apply the distinct-prefix argument with $U=H_r+r\log c$, $L=\log c$, and the dual survival test. The primal condition makes $q$ the actual quotient minimum. This is a terminal-block reducer with its own predicate. It gives no assertion of MW fixed-point convergence in a polynomial number of tours or of BKZ reduction in every other window.

## Experimental comparison

Part 64's audited minimum relative to the same lattice's restart median was 0.871 (median 0.909); relative to its single standard BKZ run the minimum was 0.839. These were searches over primal BKZ bases in ranks 24–60 with widths 8–20. They supply upper bounds on the minima searched for. Neither baseline equals the fixed rank-1023 GSA reference by definition. The Haar certificates leave room for the observed ratios and give no extrapolation of an experimental floor to either output predicate. [Part 64 and audit](wall1_bad_bases_experiment.md)

## Interval certificate

Run the block from the repository root with NumPy and mpmath. It imports the audited cap construction through Part 84, checks every integer width in the crossing question, and rounds the displayed endpoints downward. Floating-point rank selection only chooses an inequality to verify.

```python
from pathlib import Path
def block(s):
    return Path('docs/research/wall1_'+s+'.md').read_text().split('\n```python\n')[1].split('\n```')[0]
exec(block('prefix_level').split('kz =')[0])
def D(j): return A[n]-A[j]-A[n-j]-I.ln(2*n)
def lower(j): return (-I.ln(100)-D(j))/n
def out(x): return int((x*10**8).a)/10**8
def solve(b,variant=False):
    r=n-b+1
    m=r-b
    if variant:
        U=I.mpf(C[r])/M+r*I.ln(I.mpf(10001)/10000)
        L=I.ln(I.mpf(10001)/10000)
    else:
        H=I.mpf(C[b])/M
        step=2*H/(b*(b-1))
        U=H+m*2*H/b+m*(m+1)*step/2
        L=2*H/b+m*step if m else I.mpf(0)
    t=I.exp(U/r-L)/gh(r)
    p=r*(b-1)
    F=I.mpf(1)
    cuts=range(1,m+1) if not variant else ()
    # Shortlist the least upper bound on the log mean by ordinary arithmetic.
    # Only the selected witness enters the interval calculation.
    import numpy as np
    ranks=np.array(list(cuts),dtype=int)
    if len(ranks):
        dims=r-ranks
        prefix=ranks*(float(L.a)-(ranks-1)*float(step.a)/2)
        logs=np.array([float((A[r]-A[int(i)]-A[r-int(i)]-I.ln(2*r)).a)
                       for i in ranks])
        heights=np.where(ranks==m,0,float(L.a)-ranks*float(step.a))
        ghlogs=np.array([float(I.ln(gh(int(d))).a) for d in dims])
    for j in (500,900,950,975,990,995,998,999):
        f=I.mpf(j)/1000
        c=1/(1+(f*t)**r/4)
        if len(ranks):
            v=-U/r-I.ln(f)
            logsizes=prefix+ranks*float(v.a)
            power=-logsizes-dims*(float(v.a)+heights+ghlogs)
            i=int(ranks[np.argmin(logs+r*logsizes-np.logaddexp(0,power-np.log(4)))])
            d=r-i
            S=i*(L-(i-1)*step/2+v)
            rem=L-i*step if i<m else I.mpf(0)
            z=-S/d-v-rem
            logmean=A[r]-A[i]-A[d]-I.ln(2*r)+r*S
            joint=I.exp(logmean)/(1+I.exp(d*(z-I.ln(gh(d))))/4)
            # Both shapes are independent in this unselected split.
            low=L-(i-1)*step-U+(1-r)*v-S/i
            if i>=3:
                joint/=1+I.exp(i*(low-I.ln(gh(i))))/4
            if z>I.mpf(C[d])/(M*d) or low>I.mpf(C[i])/(M*i):
                joint=I.mpf(0)
            joint*=1-I.exp(r*r*I.ln(f))
            c=imin(c,joint)
        F=imin(F,f**p+c)
    y=(lower(r)-I.ln(F)/n)
    x=(y-U)/r
    rel=((b-1)*x+y)/b-I.ln(gh(b))
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    G=I.exp((2*b-n-1)*slope)
    return I.exp(x),I.exp(rel),I.exp(x)/G
for b in list(range(300,513))+[647,800]:
    vals=solve(b,b>512)
    if b<=512: assert vals[-1]<I.mpf('.85')
    if b in (300,325,350,375,400,406,425,450,475,500,506,512,647,800):
        print(b,*map(out,vals))
```
