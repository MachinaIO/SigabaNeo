# Dual pinning of the terminal GS length

At covolume one and rank 1023 the following are **99% Haar lower radii per width**, simultaneous over bases satisfying the indicated predicate. The comparison column is 85% of the Part 63 GSA reference, rounded to three decimals. Only the comparison uses GSA.

| Width | Both profiles fully exact BKZ | Micciancio–Walter Definition 1 | $0.85G$ |
|---:|---:|---:|---:|
|406|0.12656799|0.12656799|0.369|
|506|0.36551297|0.36551297|0.816|
|647|0.58973995|no positive uniform radius on a lattice admitting an output|1.822|
|800|1.01811978|same obstruction|3.413|

These are bounds on $g_k$ for $k=N-b$, $b=\beta$. The fully exact primal predicate identifies it with the terminal minimum. A single upper bound on a dual prefix determinant cannot upper-bound its last height. The certificate instead forces a **small determinant in rank $b-1$** if $h_{b-1}=1/g_k$ is large. The rank difference of one matters. On a unimodular lattice the primitive primal prefix of rank $r=k+1$ and its dual annihilator of rank $N-r=b-1$ have identical covolumes, by extending a basis and taking reciprocal GS products. Counting either counts the same sublattice incidence. V9 gives the law of the transformed shears at fixed profile and supplies no second independent event. [V9](wall1_void_duality.md) · [Part 63](wall1_profile_rigidity.md)

## Two-ended window inequalities

Put $x_i=\log g_i$ and $H_d\ge\log(\gamma_d^{d/2})$, $H_1=0$. On a window $[i,e]$ of length $d$, shortest-first primal and shortest-first reversed dual tests respectively give
$$d x_i-H_d\le\sum_{v=i}^e x_v\le d x_e+H_d.$$
This follows by applying Hermite to the projected block and its reciprocal. Shortening a tested block at the far end preserves the shortest head, also in reversed dual coordinates. When both tests hold, $x_i-x_e\le2H_d/d$. For a fully tested basis write $p_t$ for an upper bound on $x_{j-t}-x_j$, independent of $j$. Set $p_0=0$. For $2\le d\le\min(b,t+1)$ take the minimum over both
$$
 (H_d+\textstyle\sum_{v=t-d+1}^{t-1}p_v)/(d-1),\qquad
 2H_d/d+p_{t-d+1}.
$$
The first inequality propagates from the primal head, and the second passes through the jointly tested endpoint. Induction proves both. This gives the deterministic two-sided envelope
$$\lambda_1(L)e^{-p_i}\le g_i\le e^{p_{N-1-i}}/\lambda_1(L^*),$$
using the first vector and the last reciprocal vector. For $b=985$ the lower side already clears $\sqrt{6b}$ on Part 48's rank-1023 null event $\lambda_1(L)>443.0664$. Thus a sufficient width falls from 1000 to at most 985 **under the stronger predicate**. This is no claim of a first crossing. For unrestricted determinant-one inputs even orthogonal sorted diagonal bases admit arbitrarily small $g_k$ at a proper nonfinal index (shrink the first $k+1$ lengths and compensate in the rest). Both profiles pass every head test.

For the Haar calculation put $u_0=0$ and for $1\le j\le r$ minimize
$$u_j=\min_{1\le d\le\min(j,b)}(u_{j-d}+d p_{k-j+1}+H_d).$$
Partitioning off the last $d$ rows and applying the dual window inequality proves $\log D_j\le j x_k+u_j$ by induction, where $D_j$ is the primal prefix covolume. Thus the bad event implies $\log D_r\le r\log\rho+u_r$. This proof uses boundary windows explicitly.

## The recursive DBKZ predicate

Micciancio–Walter Definition 1 requires a dual-shortest endpoint on the first full block and permits **a change of basis in that block** to expose a primal shortest vector before recursing. At recursive level $i$ denote the block determinant by $V_i$ and the removed primal length by $a_i$. The witness changes preserve all original prefix determinants at ranks at least $i+b$ when the removed rows are included. Consequently $D_{i+b}=a_0\cdots a_{i-1}V_i$. The last height of block $i$ before its own change of basis equals the original $g_{i+b-1}$ for $i>0$ as well, since all previous changes preserve both prefix determinants defining this ratio.

For $m=k-b+1\ge0$, the dual check gives $V_m\le e^{H_b}g_k^b$. At the next level the first $b-1$ determinant is $V_i/a_i$, hence
$$V_i/a_i\le e^{H_b/b} V_{i+1}^{1-1/b},\qquad
a_i\le e^{H_b/b} V_i^{1/b}.$$
The first inequality uses the next level's dual check; the second is primal Hermite. Thus $V_i\le e^{2H_b/(b-1)}V_{i+1}$. Multiplying the resulting bounds on $a_i$ yields
$$\log D_r\le r x_k+H_b\left(1+2m/b+m(m+1)/(b(b-1))\right).$$
It also yields the deterministic $g_k\ge\lambda_1(L)\exp[-2H_b/b-2mH_b/(b(b-1))]$ using the first block's primal minimum (also for $m=0$). A simultaneously tested basis meets the recursive definition by retaining its current shortest heads. The recursive bound wins in the first two table rows.

For $1\le k<b-1$ the named predicate has a sharper obstruction. In **any** basis satisfying Definition 1, replace rows $v_{k-1},v_k$ by $v_{k-1}+M v_k,v_k$ for integer $M$. This preserves the first block lattice, its last reciprocal vector, the outside rows, and the existence of exactly the same recursive witness. It fixes $D_{k+1}$ and sends $D_k$ to infinity by exterior multilinearity and independence. Hence $g_k=D_{k+1}/D_k\to0$ on the very same lattice. Definition 1 makes no additional restriction on these interior flags. This algebraic obstruction covers widths 647, 800 and 985. An implementation may select a much smaller set of flags.

## Counting, cost and scope

With $A_j$ as in Part 65 and $U$ either bound on $\log D_r-r x_k$, its primitive-chain formula with one cut gives
$$\Pr[\exists\text{ bad basis}]\le
 \exp(A_N-A_r-A_{N-r}-\log(2N)+N(r\log\rho+U)).$$
Indeed the density in $\log D_r$ has exponent $N\log D_r$; integrating the lower half-line gives the divisor $N$. Duality preserves Haar measure and reverses the cut. No assumption on the shape of a selected projection enters. The four radii for simultaneous tests improve the audited Part 82 primal values 0.00654258, 0.01696600, 0.04255794, 0.15090292 under stronger assumptions. They reach about 34%, 45%, 32%, 30% of the displayed targets. Haar probabilities do not transfer to the finite null ensemble by normalization. [Primitive-chain formula](wall1_one_sided_terminal.md) · [Audited caps](wall1_small_d_caps.md)

Repository slide requires $N=sb$. Its aligned primal and shifted dual checks imply the Part 48 lower bound $g_{N-b}\ge\lambda_1(L)(\sqrt q\,\gamma_b)^{-b(s-1)/(b-1)}$ for squared dual factor $q$, by applying Hermite on each shifted block and substituting the primal determinant bound. There is also an aligned upper envelope. Put $F=(\sqrt q\,\gamma_b)^{b/(b-1)}$ and $a_j=g_{jb}$. For $i<j$ use $a_i\ge\lambda_1(L)F^{-i}$, and for $i\ge j$ use $a_i\ge a_j F^{-(i-j)}$. Multiplying the primal block determinant lower bounds gives $a_j^{s-j}\le (\det L)^{1/b}\gamma_b^{s/2}\lambda_1(L)^{-j}F^{[j(j-1)+(s-j)(s-j-1)]/2}$. The checks cost $s$ primal and $s-1$ dual width-$b$ oracle evaluations per full verification. Even the single-block diagonal $(1,5,4)$ passes but its reversed dual fails the head test. All four widths violate divisibility here. The existing sufficient slide width remains 1023. [Slide checker](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Conditions.lean) · [Part 48](wall1_null_terminal.md) · [Part 76](wall1_jw_slide.md)

MW Algorithm 1 uses $N-b$ primal and $N-b+1$ dual width-$b$ calls per tour. Its polynomial-tour Hermite-factor analysis does not certify simultaneous shortest heads in the returned basis. The stronger table column applies to a supplied basis passing both window checks, with at most $2N$ exact SVP calls of rank at most $b$ for verification. Neither existence on every lattice nor a construction at that cost follows from the checks. A fixed number of practical tours has no certified radius here solely by its stopping rule. [Micciancio–Walter, Algorithm 1, Definition 1 and §4](https://iacr.org/archive/eurocrypt2016/96650251/96650251.pdf)

## Interval certificate

Run the following block from the repository root. Integer recurrences round caps upward in billionths of a nat. The script imports certified packing inputs and interval chain constants from the earlier reports. The additional False-mode diagnostic uses only simultaneous full-tour checks on a single basis, with dual ends at indices at least $b-1$; this is stronger than the recursive predicate. Output radii are rounded down in hundred-millionths.

```python
from pathlib import Path
def note(name):
    return Path('docs/research/wall1_'+name+'.md').read_text()
base=note('surviving_mass').split('\n```python\n')[1]
exec(base[:base.index('import numpy')])
# Part 77 integer upper bounds, already certified by its rational witnesses.
tab=note('lcz_all_widths').split('d k numerator LCZ Part65\n')[1].split('```')[0]
for line in tab.strip().splitlines():
    d,_,_,lc,old=map(int,line.split())
    assert C[d]==old
    C[d]=min(old,lc)
# A conservative subset of Part 82 (omit the disputed SDP decimals).
data=note('small_d_caps').split('density = """')[1].split('"""')[0].split()
for d,s in enumerate(data,4):
    if d>=17 and s!='-':
        u=I.mpf(d)/2
        H=d*I.ln(2)+I.ln(I.mpf(s))+I.loggamma(1+u)-u*I.ln(I.pi)
        C[d]=min(C[d],int((M*H).b)+1)
C[24]=int((24*M*I.ln(2)).b)+1
for d in range(3,n+1):
    C[d]=min(C[d],(d*C[d-1]+d-3)//(d-2))
def ceildiv(a,b): return -(-a//b)
def bounds(b,both):
    k=n-b
    p=[0]
    s=[0,0]
    for t in range(1,k+1):
        v=min(ceildiv(C[d]+s[t]-s[t-d+1],d-1)
              for d in range(2,min(b,t+1)+1))
        for d in range(2,min(b,t+1)+1):
            e=k-t+d-1
            if both or e>=b-1:
                v=min(v,p[t-d+1]+ceildiv(2*C[d],d))
        p.append(v)
        s.append(s[-1]+v)
    u=[0]
    for j in range(1,k+2):
        e=j-1
        ds=min(b,j) if both or e>=b-1 else 1
        u.append(min(u[j-d]+d*p[k-e]+C[d] for d in range(1,ds+1)))
    return p,u[-1]
for b in (406,506,647,800):
    for both in (True,False):
        p,U=bounds(b,both)
        r=n-b+1
        a=A[n]-A[r]-A[n-r]-I.ln(2*n)
        radius=I.exp(((-I.ln(100)-a)/n-I.mpf(U)/M)/r)
        print(b,both,int((radius*10**8).a),flush=True)
for b in range(940,1001):
    p,_=bounds(b,True)
    if I.mpf('443.0664')*I.exp(-I.mpf(p[-1])/M)>I.sqrt(6*b):
        print('sufficient width',b,flush=True)
        break
for b in (406,506):
    r=n-b+1
    m=r-b
    H=I.mpf(C[b])/M
    U=H*(1+I.mpf(2*m)/b+I.mpf(m*(m+1))/(b*(b-1)))
    a=A[n]-A[r]-A[n-r]-I.ln(2*n)
    rad=I.exp(((-I.ln(100)-a)/n-U)/r)
    print('recursive',b,int((rad*10**8).a))
```

## Audit note (independent audit, Nov 2026)

All numbers reproduce (also from independent code from Schmidt's constant). The direction is correct: g_k small means the
rank-(k+1) primal prefix covolume D_{k+1} = D_k·g_k is small (equivalently the dual annihilator of rank β−1), and D_{k+1} is
bounded via dual-window Hermite inequalities and the primal height caps. **Meaning of the columns:** the "primal and reversed
dual both fully BKZ-reduced" predicate is not known to be produced by any reducer, and may be empty on many lattices (in each
full window it forces the block's shortest vector to be orthogonal to its shortest dual vector); bounds under it may be largely
vacuous. The Micciancio–Walter Definition 1 column is the one attained by a real algorithm (MW self-dual BKZ, Algorithm 1,
Lemma 1): at β = 406 / 506 every MW-reduced basis has g_{1023−β} ≥ 0.12656799 / 0.36551297 (99%, Haar); at β = 647 / 800 no
positive uniform bound exists under Definition 1 (in-block basis changes send g_k → 0 when k < β − 1). Gains over Part 82:
≈ 19× / 21.5× at 406 / 506. The plain Blichfeldt cap alone already gives 0.1191 at β = 406.
