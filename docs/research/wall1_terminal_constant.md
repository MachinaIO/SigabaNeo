# Terminal minima under overlapping BKZ windows

Let $L$ be Haar unimodular, $b/N\to a\in(0,1)$, $k=N-b$, and use zero-based indices and natural logs. Write $W_j$ for the primitive prefix of rank $j$, $T=\pi_{W_k^\perp}L$ (orthogonality is to the real span), $h_d=V_d^{-1/d}$, and $R_T=h_b\det(T)^{1/b}$. Exact full BKZ gives $g_k=\lambda_1(T)$. We obtain a width-independent leading coefficient in the squared-log loss and a polynomial bound for a local geometric mean. The polynomial bound for the individual $g_k$ remains open.

## Propagating averages through overlapping windows

**Theorem 1.** Outside a single event of probability at most $2^{-N}$, simultaneously for every fully BKZ-$b$ basis,
$$
 \log(g_k/R_T)\ge-\tfrac14\log^2 N-O_a(\log N).
$$
Moreover, for $s=\min(k+1,\lfloor b/2\rfloor)$ the geometric mean of $g_{k-s+1},\ldots,g_k$ is at least $R_T N^{-O_a(1)}$.

**Proof.** Put $x_i=\log g_i$. In any interval ending at $v$, let $m_i$ be the mean from $i$ through $v$ and $d=v-i+1$. Every initial truncation of a tested window retains its shortest head. Minkowski thus gives $x_i\le m_i+C_d$ with $C_d=\log(2h_d)=\frac12\log d+O(1)$ for $2\le d\le b$. Hence
$$
 x_i\le m_{i+1}+dC_d/(d-1),\qquad
 m_i\le m_{i+1}+C_d/(d-1).
$$
Decompose $[0,k]$ from the right into chunks of $s$ entries, allowing the leftmost one to be shorter. There are $O_a(1)$ chunks. Given the mean $M$ on one full chunk, append the chunk to its left, keeping the same right endpoint. Every newly added entry is at most $M+O(\log N)$ by the first inequality and the second summed over $s<d\le2s$: the harmonic sum there is bounded. Thus its chunk mean is bounded by the same quantity. This also bounds $x_0$ on reaching the leftmost chunk. In the single-chunk case apply the first inequality at $0$ or directly $x_0\le m_0+C_s$. In all cases $x_0\le M_{\rm last}+O_a(\log N)$. Finally
$$
 M_{\rm last}-x_k\le\sum_{d=2}^s C_d/(d-1)
 \le \tfrac14\log^2 s+O(\log s)
$$
by integral comparison. Only the rightmost chunk pays this full sum.

Siegel's signed-pair bound on $L$ and $L^*$ gives both minima at least $h_N/2$ except on mass $2^{-N}$. On this event $g_0\ge h_N/2$, while Minkowski on $T^*=L^*\cap W_k^\perp$ gives $R_T\le4h_b^2/h_N$. Hence $g_0/R_T\ge h_N^2/(8h_b^2)=\Theta_a(1)$ as a lower bound. This proves both assertions. [Part 65](wall1_one_sided_terminal.md)

The endpoint sum reflects a real obstruction in a single window. Hanrot and Stehlé construct HKZ bases in dimension $d$ with first-to-last GS ratio $\exp[(1/4)\log^2 d-O(\log d)]$. Every internal primal window of such a basis passes. Even relative to its determinant root, the last GS can be superpolynomially small, since the first is at most $2h_d$ times that root. Therefore a polynomial last-GS lower bound from transference or Rankin inequalities valid for every isolated HKZ window would be false. Transference bounds the shortest dual vector, whereas the reciprocal last GS is the length of a particular primitive dual vector. This construction supplies no Haar probability estimate for the ambient problem. [Hanrot and Stehlé](https://arxiv.org/abs/0801.3331)

**Corollary (all crossing windows, worst-case input).** For each proportional width there are unimodular lattices with a full HKZ basis satisfying
$$
 \log(g_k/R_T)=-\tfrac14\log^2 N+O_a(\log N).
$$
Take the preceding HKZ example in dimension $d=k+1$, with last length $u$ and first length $v$. Form its orthogonal direct sum with $b-1$ orthogonal lines of common spacing $B$, the largest GS length in the example. Use the given basis first, then the orthogonal generators. At every step inside the first summand the projected minimum is the current head, since the extra summand has minimum $B$. Thus the entire basis is HKZ, including every BKZ crossing test. Corollary 5.5 gives $\log(B/u)=\frac14\log^2 d+O(\log d)$: the lower bound follows from $B\ge v$ and the upper bound from the same explicit formula at each remaining dimension $1\le r\le d$. The terminal determinant is $uB^{b-1}$, so the relative length is $(u/B)^{1-1/b}/h_b$. Common rescaling to determinant one preserves this ratio. This is an existence construction on special lattices; obtaining a polynomial floor on Haar input requires some use of ambient typicality. [Hanrot and Stehlé, Corollary 5.5](https://perso.ens-lyon.fr/guillaume.hanrot/Papers/kannan-final.pdf)

## Primitive prefixes under a determinant cap

**Theorem 2.** Put $F=k b d_b$, with $d_b$ as in Part 63, and $X=e^F$. On the same event, for all sufficiently large $N$ there exists a primitive rank-$k$ sublattice $W$ with $X/2\le\det W\le X$ such that its quotient satisfies
$$
 \log\frac{\lambda_1(T)}{R_T}
 \le-\left(\frac{1-a+a\log a}{2}+o(1)\right)N\log N.
$$
Here $T=\pi_{W^\perp}L$. Thus even restricting determinants to within a factor two of the GSA value cannot yield the desired uniform estimate by counting all primitive sublattices. The GSA cap is an explicit comparison scale. The theorem does not characterize the determinants attained by actual BKZ prefixes.

**Proof.** Start with a size-reduced full HKZ basis $v_i$. Denote its prefix determinants by $D_j$. The deterministic Blichfeldt recursion from Part 63 gives $\log D_j\le U_j$, $U_0=0$, $U_{j+1}=(1-1/r)U_j+c_r$ for $r=N-j$, $c_r=\frac12\log(2/\pi)+r^{-1}\log\Gamma(2+r/2)$. Dividing by $r-1$ before summing gives
$$
 U_j=(N-j)\sum_{r=N-j+1}^N c_r/(r-1).
$$
For $j=k-1,k,k+1$, Stirling gives $c_r=\frac12\log N+O_a(1)$ throughout the sum, so $U_j/(N\log N)\to-a\log a/2$. Meanwhile $F/(N\log N)\to(1-a)/2$. Their limiting gap is strictly positive. [Part 63](wall1_profile_rigidity.md)

Keep the first $k-1$ vectors and append $v_k+m v_{k-1}$, $m\ge0$ integral. This primitive prefix extends by $v_{k-1}$ to the fixed primitive rank-$(k+1)$ prefix. Write $D(m)$ for its determinant. Size reduction gives $D(0)\le D_{k-1}g_k+D_k/2$ in the starting basis. There $g_k\le 2h_b\det(T_{\rm start})^{1/b}\le8h_b^2/h_N$ on our event. Also $D(m)\to\infty$ and $|D(m+1)-D(m)|\le D_k$ by the triangle inequality on exterior products. Thus $D(0)<X$ and $D_k<X/2$ for large $N$. Immediately before the first overshoot we have $D(m)\in[X/2,X]$. The projected extension vector has length $D_{k+1}/D(m)$ and $\det T=1/D(m)$. Consequently
$$
 \log(\lambda_1(T)/R_T)\le U_{k+1}-(1-1/b)(F-\log 2)-\log h_b.
$$
Substituting the two limits proves the claim. The construction also rules out a corresponding uniform covering-radius estimate: for a shortest $t\in T$, points of $T^*$ lie on hyperplanes perpendicular to $t$ spaced $1/\|t\|$ apart, so $\mu(T^*)\ge1/(2\lambda_1(T))$.

**Rank 1023.** At widths 406, 506 and 647 respectively the last display bounds the log relative minimum from above by $-166$, $-85$ and $-5.99$ for some primitive prefix in the specified band. These are obstruction certificates. The interval checks below use natural logs throughout. The same coarse recursion does not certify the band construction at width 800.

```python
from mpmath import iv as I
I.dps = 45
n = 1023
log = I.ln
def lh(d):
    return I.loggamma(1+I.mpf(d)/2)/d-log(I.pi)/2
u = [I.mpf(0)]
for r in range(n, 1, -1):
    c = log(2/I.pi)/2 + I.loggamma(2+I.mpf(r)/2)/r
    u.append((1-I.mpf(1)/r)*u[-1]+c)
for b, cap in [(406, '-166'), (506, '-85'), (647, '-5.99')]:
    k = n-b
    f = k*b*(log(b/(2*I.pi*I.exp(1)))+log(I.pi*b)/b)/(2*(b-1))
    assert u[k] < f-log(2)
    assert u[k-1]+log(8)+2*lh(b)-lh(n) < f-log(2)
    assert u[k+1]-(1-I.mpf(1)/b)*(f-log(2))-lh(b) < I.mpf(cap)
```

**A smaller cap where counting succeeds.** Let $A(N,k)$ be the primitive-sublattice mean constant in Part 5 and $X_*=A(N,k)^{-1/N}$. For $\det W\le X_*e^t$ the probability of any quotient ratio at most $\rho$ is bounded by
$$
 e^{Nt}\rho^b/(2\zeta(b)).
$$
Indeed integrate the two-rank flag density $Nb A(N,k)A(b,1)s^k z^{b-1}$ over $s\le X_*e^t$, $z\le \rho h_b s^{1-1/b}$, where $s=\det W$ and $z$ is the determinant of its primitive one-rank extension. Use $A(b,1)h_b^b=1/(2\zeta(b))$ and Markov. Thus $t=O(1)$ admits a constant floor at failure probability $2^{-N}$, and $t=O(\log N)$ admits a polynomial floor, by taking $\rho=\exp[-N(t+\log 2)/b]$. Extending this to a larger family requires controlling the actual prefix selection. [Flag density and normalization](wall1_sublattice.md)

## Remaining gap

Theorem 1 controls the mean log length on a linear-sized neighborhood of the terminal index. A sufficient missing estimate is $M_{\rm last}-x_k=O_a(\log N)$ simultaneously for completable prefixes on Haar input. Theorem 2 shows why determinant information at the GSA scale alone cannot supply it. A constant relative floor requires control at the actual quotient scale. Part 64's observed ratios compare against typical BKZ outputs, which are a different denominator. The rank-1023 positive lower bounds for fully reduced bases remain those certified in Part 65. [Experiments and audit](wall1_bad_bases_experiment.md) · [Wall 1 frontier](../PROOF_GAP.md)
