# Two-block generalized slide reduction on a Haar lattice

For a covolume-one Haar lattice of rank 1023, each row below holds with probability at least 0.99 **simultaneously for every qualifying basis at that width**. The observable is the first GS length of the last block. With an exact terminal SVP call it equals the minimum of that block. Positive slack in the twin test is compatible with an exact terminal call.

| Width | Prefix rank | Exact twin | Algorithm 1, exact oracle and 1% slack | Part 86 | 0.85 GSA |
|---:|---:|---:|---:|---:|---:|
|406|617|0.12656799|0.12531282|0.12656799|0.36920|
|506|517|0.36551297|0.36188705|0.36551297|0.81632|

The exact twin certificate reaches 34.3% and 44.8% of the respective GSA comparison values. Only the comparison uses GSA. The exact column states a predicate theorem. Algorithm 1 has a positive slack parameter.

## Published conditions and termination

Use one-based inclusive projected blocks, write disjoint block widths as first block of rank $b+s$ followed by blocks of rank $b$, and put $n=pb+s\ge2b$, $0\le s<b$, $b\ge2$. Write $D_j$ for prefix covolumes. In Definition 1 at quality $c\ge1$, put $h=(c^2\gamma_b)^{1/(2(b-1))}$ and $a=h^{b+s-1}$. Size reduction is required. The twin test on $[1,b+s+1]$ requires $a$-HSVP on $[1,b+s]$ and $a$-HSVP on the reversed dual of $[2,b+s+1]$. HSVP bounds the head length by the factor times the geometric mean. Each $[ib+s+1,(i+1)b+s]$ for $1\le i<p$ needs $c$-SVP. Each $[ib+s+2,(i+1)b+s+1]$ for $1\le i<p-1$ needs reversed-dual $c$-SVP. The latter list is empty for $342\le b\le511$ at rank 1023. [Li–Walter, pp. 5–7](https://eprint.iacr.org/2023/140.pdf)

Theorem 2 concerns generic $(h,b,r)$ reduction, $1\le r<b$, $h\ge1$. The reduced test on a rank-$m$ block is $D_r\le h^{(m-r)r}D_m^{r/m}$ in its own coordinates. The dual test applies it on the reversed dual. Definition 3 requires size reduction, the first primal test on $[1,b+s]$, its shifted dual test on $[1+r,b+s+r]$, the ordinary primal blocks above, and their shifts by $r$ for the dual indices above. The theorem gives
$$D_j\le h^{j(n-j)}D_n^{j/n},\qquad j=r\text{ or }j=ib+s,\quad 1\le i<p\text{ for the latter}.$$
Definition 1 implies Definition 3 at $r=1$ with the stated $h$. Thus at $k=n-b=b+s$ the cap is $D_k\le h^{kb}$ and the terminal geometric mean is at least $h^{-k}$.

On integral input $B_0$, Theorem 1 gives at most $\lceil(p-1)(n+s)\log\|B_0\|/\log(1+\epsilon)\rceil$ slide tours for $0<\epsilon\le1$, using a rank-$b$ $\delta$-SVP oracle, with output quality $c=(1+\epsilon)\delta$. In the two-block case the last unchanged tour actually gives terminal quality $\delta$ and both twin factors at most $a=(1+\epsilon)(\delta^2\gamma_b)^{(k-1)/(2(b-1))}$ (steps 2–8). This sharper factor is used in the table. A changed dual step increases the last height of its block by a factor exceeding $\sqrt{1+\epsilon}$ at fixed block determinant and fixed first column, reducing $D_k^2$ by a factor exceeding $1+\epsilon$. For a fixed real lattice $D_k$ is bounded below by the shortest nonzero length in its exterior-power lattice. Hence the outer stopping argument also holds in exact real arithmetic given the indicated block subroutines. The stated integral-input bit model does not describe a Haar sample.

Each two-block tour has one terminal oracle call and up to two capped DBKZ subroutines of rank $k$. Appendix A, Theorem 7, on LLL-reduced input and $1\le\delta<(3/2)^{(b-1)/4}$, charges $(2k-2b+1)N+1$ rank-$b$ calls per subroutine for $N=O((k/b)^2\log(k/t))$ inner tours at slack $0<t<0.1$. For the 1% example $t=0.004$ suffices for either invocation. The polynomial overhead is relative to the SVP oracle. These inner tours terminate by a preset count. MW's open stabilization question concerns running to its recursive self-dual predicate. [Li–Walter, Algorithms 1 and 4, Theorems 1 and 7](https://eprint.iacr.org/2023/140.pdf) · [MW stopping qualification](wall1_literature3.md)

## Counting a prefix or its extension

Let $x=\|b_1\|$, $g=D_{k+1}/D_k$, $v=D_k$, and $a$ be the actual twin factor. The two tests read $x\le a v^{1/k}$ and $(vg/x)^{1/k}\le ag$. Eliminating $x$ gives
$$v\le M_0 g^k,\qquad M_0=a^{k(k+1)/(k-1)}.$$
Thus a small $g$ forces a small determinant of the primitive extension $P=L_{k+1}$, equivalently its rank-$(b-1)$ annihilator in the dual lattice. This uses just the single shifted Hermite test inside the twin. For $g<\rho$, $\det P<M_0\rho^{k+1}$. Write $K_j=\exp(A_n-A_j-A_{n-j})/(2n)$, with $A_1=0$ and $A_i-A_{i-1}=\log(iV_i/\zeta(i))$, $V_i$ the unit ball volume. The Haar mean number of unoriented primitive rank-$j$ sublattices up to determinant $z$ is $K_j z^n$. Markov gives failure at most $K_{k+1}(M_0\rho^{k+1})^n$. This proves the table by outward rounding. For $c=1$, $\log M_0=k(k+1)\log h$, exactly the exponent obtained in Part 86 by a different set of tests. [Part 86](wall1_dual_pinning.md)

For comparison, apply the quotient law directly at the rank-$k$ split. Under primitive-prefix incidence at fixed $v$, $J=v^{1/b}T$ has unimodular Haar law. Let $F_b$ be its minimum CDF. A bad head requires $\lambda_1(T)\le g<\rho$. Combining Theorem 2 with the twin bound, the mean number of candidate prefixes is bounded by
$$nK_k\int_0^{\min(h^{kb},M_0\rho^k)} v^{n-1}F_b(\rho v^{1/b})\,dv.$$
Here $h$ uses the full Definition 1 guarantee. Part 46's exact minimum density is $bV_b r^{b-1}Z_b(r)/(2\zeta(b))$, with $0\le Z_b\le1$. Inserting its upper envelope and using just the second cap gives failure at most $nK_k V_b M_0^{n+1}\rho^{b+k(n+1)}/(2(n+1))$. At exact quality this certifies 0.12643034 and 0.36538813, slightly below extension counting. The extension count charges a bad extension once even if it admits several prefixes. Either bound separately can be used at the full 1% budget. [Part 46](wall1_haar_prefix_law.md) · [Part 84](wall1_prefix_level.md)

These probability statements apply to an output rule returning a passing witness on every input. For an approximate terminal test $g\le\delta\lambda_1(T)$, divide the head bound by $\delta$ for a minimum bound. For a partially run algorithm or a proposed prefix selected by another rule, conditioning literally on a pass event $E$ gives only $\Pr(\mathrm{bad}\mid E)\le0.01/\Pr(E)$ from the simultaneous theorem. A conditional quantile for that experiment needs its sampling rule and pass probability. Replacing its selected quotient by an independent Haar shape would drop the selection weight. A finite-modulus result would additionally require an ensemble transfer. [Wall 1 frontier](../PROOF_GAP.md)

## Reproducible interval certificate

Run this Python block from the repository root. It reuses the audited integer Hermite caps and interval normalization of Part 86. Each returned integer rounds a lower endpoint down in units of $10^{-8}$.

```python
from pathlib import Path
source = Path('docs/research/wall1_dual_pinning.md').read_text()
setup = source.split('\n```python\n')[1].split('def ceildiv')[0]
exec(setup)
def logK(j):
    return A[n]-A[j]-A[n-j]-I.ln(2*n)
for b in (406,506):
    k = n-b
    logh = I.mpf(C[b])/(M*b*(b-1))
    logV = (I.mpf(b)/2)*I.ln(I.pi)-I.loggamma(1+I.mpf(b)/2)
    for slack in ('0','.01'):
        loga = (k-1)*logh + I.ln(1+I.mpf(slack))
        logM = loga*k*(k+1)/(k-1)
        ext = ((-I.ln(100)-logK(k+1))/n-logM)/(k+1)
        split = (-I.ln(100)-logK(k)-logV-I.ln(I.mpf(n)/(2*(n+1)))
                 -(n+1)*logM)/(b+k*(n+1))
        print(b, slack, *(int((10**8*I.exp(y)).a) for y in (ext,split)))
```

## Audit note (independent audit, Nov 2026)

Checked against the authors' HAL deposit (hal-03983826). Attribution: the slide definition, algorithm and tour bound are
ALNS20's (Def. 2, Alg. 3, Th. 8), restated by Li–Walter; Theorem 7 is credited to LN20. The final tour has step 7 idle, so the
output satisfies both twin tests with factor (1+ε)η and the terminal δ-SVP test; eliminating ‖b_1‖ uses both halves of the
twin. Implementation caveats: η must be computed from a Hermite value no larger than the Part 77/82 cap (an implementation with
a looser γ' is not covered), and an LLL pre-pass (which leaves D_k unchanged) should be inserted before Algorithm 4. Li–Walter's
Theorem 4 (GSR, real LLL-reduced input) gives a tour bound independent of ‖B_0‖.
