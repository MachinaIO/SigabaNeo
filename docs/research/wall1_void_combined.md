# Truncated shallow windows and Fourier continuation at rank 1023

None of the twelve radii is certified by the combined estimate below. The tighter packing facets move the high-density boxes, but the smallest new box still has relaxed log mass above 228841. At that radius and width, even granting the finite Fourier martingale its entire disjoint-window budget leaves over 50526 nats after also allowing the shallow penalty. This is a shortfall of the estimate. The accepted Haar mass itself could be much smaller.

## A profile-dependent suppression bound

Fix the diagonal and use the independent uniform triangular chart. A competitor in a truncated projected block pads by zeros to a competitor at the same start in the BKZ test. Normalize each block by its head and write its resulting lengths as $h_j$, with $h_0=1$. Starting at its head, keep the longest prefix of length at most $\beta$ on which **every** length is at least $a=e^{-0.32}>1/\sqrt2$. The all-index check matters across a dent. Write $m$ for the minimum on that prefix. For each noninitial column let
$$
 s_j=(1-h_j^2)_+^{1/2},\qquad e_j=V_j s_j^j/\prod_{k<j}h_k .
$$
Only height one can contribute in the shallow prefix, so its exact mean is $E_{\rm sub}=\sum e_j$. V7 gives the conditional product penalty $(2m^2-1)E_{\rm sub}$, including for nonmonotone diagonals. Indeed, on each passing history the minimum separation is at least one. The list-size bound $1/(2h_j^2-1)$ for lifts in the fresh ball gives failure probability at least $(2h_j^2-1)e_j$ for $h_j<1$. At $h_j\ge1$ the contribution vanishes. [Shallow-window theorem](wall1_void_numerics.md)

For **each subsequent column at this same start**, a concrete V5 penalty valid uniformly over passing histories is
$$
 f_j=\tfrac12(e_j/2^j)^2.
$$
Here $e_j$ always denotes the height-one section, even when other heights occur. For $s_j>0$, convolve the radius-$s_j/2$ ball indicator with its reflection, divide by its volume and periodize on the prefix torus. The weight is nonnegative, vanishes outside the projected open radius-$s_j$ ball, and has mean $A=e_j/2^j$. Its Fourier coefficients are nonnegative squared moduli. Parseval for the periodized small ball gives their sum as one, since the small ball embeds up to null boundaries on a passing prefix. Equivalently the normalized convolution at zero is one. Thus the series converges absolutely and the nonconstant Fourier groups in V5 have $\sum b_l=1-A\le1$. The martingale inequality gives conditional miss probability at most $\exp(-A^2/2)$, also valid for a zero section. Absolute convergence justifies revealing the phases for this continuous weight. This supplies a deterministic lower bound on the deep penalty without averaging dual data over a biased surviving law. [Fourier martingale](wall1_void_fourier.md)

Choose disjoint blocks, with these shallow heads and any number of deep continuation columns subject to the width limit. Sum their penalties to obtain $P(x)$, or maximize the sum over such choices. At fixed profile $x$, $W(x)\le e^{-P(x)}$ by successive conditioning inside blocks and independence across blocks. In particular the Haar upper bound is $K_n\int_D \exp(F(x)-P(x))\,dS$ over the deterministically surviving domain $D$. Multiple starts inside an already charged block cannot be multiplied using this independence argument. The fresh rectangles in the multiscale argument also require their own conditional estimate. [Multiscale conditioning](wall1_void_multiscale.md)

## Relocated boxes and numerical bounds

Use all Part 65 facets and all four explicitly certified Part 73 facets, at every applicable start and width $d\le\beta$. The latter have log-determinant caps $\mathrm{capval}_d-\log V_d$, with the full rational code ratio evaluated before interval rounding. This domain specifies the finite list of exclusions being tested. Use the Part 71 backward recurrence with these replacements, the same .055 drop cap, $10^{-6}$ perturbations, and the exact cut $\rho=cG_\beta$. The code specifies every box center. It checks every facet over the *entire* perturbed box. The density deficit compares its center with the supremum over the new domain. [Box recurrence and Haar normalization](wall1_surviving_mass.md) · [Four packing certificates](wall1_dense_packing_ld.md)

The relaxed column encloses the logarithm of the unweighted integral on $D$. Its lower endpoint also holds for the single indicated box. The mixed penalty interval holds throughout that box for the following particular schedule. Take the longest shallow head certified by the box's log-ratio endpoint bounds, append one deep column when the width and remaining rank permit, then restart. Rounding may shorten a prefix at the threshold. Longer deep continuations and different disjoint schedules are covered by the last column, which gives a lower bound on the residual log integral even with the optimistic finite budgets derived below. All log quantities are in nats.

| $\beta$ | $c$ | Relaxed log mass | Center deficit upper | Mixed penalty | Residual lower |
|---:|---:|---:|---:|---:|---:|
|406|.25|[805584,827405]|9108|[6,7]|706153|
|406|.50|[820329,834496]|1452|[5,6]|720898|
|406|.85|[822677,835504]|112|[4,5]|723246|
|506|.25|[569168,592294]|10411|[6,7]|435237|
|506|.50|[585856,601101]|2531|[4,5]|451925|
|506|.85|[590231,603046]|100|[4,5]|456300|
|647|.25|[371247,393126]|9165|[6,7]|225368|
|647|.50|[385817,401448]|2916|[4,6]|239938|
|647|.85|[390696,403737]|327|[3,4]|244817|
|800|.25|[228841,251995]|10440|[6,7]|50526|
|800|.50|[245325,261936]|3897|[5,6]|67010|
|800|.85|[251526,264961]|721|[3,4]|73211|

For the residual column, the shallow exponent per charged column is at most $V_j<6$. Indeed $s_j\le1/\sqrt2$ and every preceding normalized length exceeds $1/\sqrt2$, so $e_j\le V_j$. The ball-volume recurrence $V_{j+2}=2\pi V_j/(j+2)$ gives the stated uniform constant by checking dimensions one through seven. Thus even the layer-weighted version of V7 can spend at most $6n$ over disjoint windows.

Grant the deep columns $j/2$ each, where $j$ is the local prefix rank. For widths at most $b$, the disjoint-window sum is bounded by
$$ B_b=\{q b(b-1)+r(r-1)\}/4,\qquad (q,r)=\mathrm{divmod}(1023,b). $$
Indeed shifting a column from a smaller block to a larger unsaturated one increases the sum. Rounded upwards with slack, the budgets are 93293, 127793, 139741 and 172177. The concrete penalty $f_j$ fits this budget on the domain: $A\le1$ already follows from the Part 65 prefix caps since $s_j\le1$. For $j\ge9$ their Blichfeldt candidate gives $V_j/(2^j\prod h_k)\le(1+j/2)2^{-j/2}\le1$, and for $2\le j\le8$ the tabulated small-dimensional caps give the same inequality directly. At $j=1$ use $h_0=1$. Subtracting $6n+B_b$ from the box log mass therefore lower-bounds the log of the *upper-bound integral* even for an optimized disjoint schedule. The full domain integral for the concrete combined estimate has the same relaxed upper endpoint by $P\ge0$.

For arbitrary smooth Fourier weights $j/2$ is a ceiling on the V5 martingale exponent on histories admitting a hole, by Cauchy–Schwarz. It is **not** a penalty available for every column. A separate proof of exact coverage, or suppression from histories where the Fourier test certifies coverage, could evade the finite-budget comparison. No such coverage estimate on the relocated boxes follows from the four Part 73 cuts. This leaves the true weighted Haar integral unresolved. [Wall 1 frontier](../PROOF_GAP.md)

## Reproduction

Run the following Python from the repository root with mpmath and NumPy. It imports the integer recurrence and interval normalization from Part 71, then installs the exact Part 73 cuts before either envelope is built. Outputs are the table columns with the Fourier budget before the residual and the mixed interval last.

```python
from pathlib import Path
root=Path('docs/research')
def source(name):
    return (root/name).read_text().split('```python')[1].split('```')[0]
exec(source('wall1_surviving_mass.md').split('for b,rounded')[0])
from fractions import Fraction as Q
def ivq(q):
    return I.mpf(q.numerator)/q.denominator
packing=(root/'wall1_dense_packing_ld.md').read_text()
exec(packing[packing.index('for b,k,u6'):packing.index('    slope=')]+'''
    logV=b*I.ln(I.pi)/2-I.loggamma(1+I.mpf(b)/2)
    value=M*(capval-logV)
    C[b]=min(C[b],int(value.b)+1)
    assert C[b]-2 <= value < C[b]
''')
def mixed(v,b):
    # Fix cuts from the box center. Include one deep endpoint if available.
    lower=I.mpf(0)
    upper=I.mpf(0)
    i=0
    while i<n:
        shallow=I.mpf(0)
        minimum=I.mpf(1)
        total=0
        for j in range(1,min(b,n-i)):
            delta=v[i+j]-v[i]
            z=I.exp(I.mpf([delta-2000,delta+2000])/M)
            s2=I.mpf([max(0,(1-z*z).a),max(0,(1-z*z).b)])
            total+=v[i]-v[i+j-1]
            inv=I.exp(I.mpf([total-2000*(j-1),total+2000*(j-1)])/M)
            e=I.pi**(I.mpf(j)/2)/I.gamma(1+I.mpf(j)/2)*s2**(I.mpf(j)/2)*inv
            deep=delta-2000 < -320000000
            if deep:
                f=(e/(2**j))**2/2
            else:
                shallow+=e
                minimum=imin(minimum,z)
                f=I.mpf(0)
            lower+=f.a
            upper+=f.b
            if deep: break
        else:
            f=(2*minimum**2-1)*shallow
            lower+=f.a
            upper+=f.b
            i+=min(b,n-i)
            continue
        f=(2*minimum**2-1)*shallow
        lower+=f.a
        upper+=f.b
        i+=j+1
    return int(lower.a),int(upper.b)+1
for b in (406,506,647,800):
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    G=I.exp((2*b-n-1)*slope)
    for frac in ['.25','.5','.85']:
        R=I.mpf(frac)*G
        v=solve(b,R,False)
        U=solve(b,R,True)
        L=A[n]+score(v)-2+(n-1)*I.ln(I.mpf(2)/10**6)-I.ln(n)
        H=A[n]+score(U)-(n-1)*I.ln(2)
        # Verify cut and every packing facet over the perturbed box.
        assert I.exp(coords(v,n-b)+I.mpf(2)/10**6)<R
        T=np.array([0]+list(np.cumsum(v)),dtype=np.int64)
        for d in range(2,b+1):
            assert max(d*np.array(v[:n-d+1])-T[d:]+T[:-d])+2000*(d-1)<=C[d]-2
        q,r=divmod(n,b)
        budget=(q*b*(b-1)+r*(r-1))//4+1
        print(b,frac,flooriv(L),ceiliv(H),ceiliv(score(U)-score(v)),budget,flooriv(L-budget-6*n),mixed(v,b),flush=True)
 ```
