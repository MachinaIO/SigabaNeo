# Joux–Węgrzycki propagation on the horizontal graph lattice

**Result.** The scalar argument of Appendix A gives a two-sided simultaneous GS envelope. Its dual half applies to the reversed reciprocal of the *same* basis. It needs neither a second reduction nor dual equivariance of the algorithm. Numerically the envelope loses too much within a block. None of the four requested horizontal widths clears the linear benchmark by this argument. For the actual equal-block slide checker none of those widths even defines a rank-1023 instance. The certified crossings in Parts 48–49 stand.

## The random-input theorem

In Theorem 3 the positive weights are independent uniform integers up to the ceiling of the square root of $Y^{n^2}2^{\Theta(n\log n)}$, with fixed $Y>1$. The tester uses one deterministic reduction for all targets. The profile result is Lemma 10, on the lift of the line spanned by the weight vector modulo the paper's prime $p$. Its determinant is $D=p^{n-1}$. With failure probability $2^{-\Omega(n\log n)}$, every output GS length is at most $C_Y Y^{(n-1)/2}D^{1/n}$. The paper chooses the least admissible width $w>2$ with $\gamma_w^{1/(w-1)}\le Y$, where $\gamma_w$ is the Hermite constant for squared lengths. [Joux–Węgrzycki, §§3.1–3.3 and Appendix A](https://drops.dagstuhl.de/storage/00lipics/lipics-vol364-stacs2026/html/LIPIcs.STACS.2026.57/LIPIcs.STACS.2026.57.html)

Conditioning on complete residue periods and an invertible first weight costs overwhelming-small probability in their regime. After normalization by that weight, the other residues are independent uniform. Each possible short nonzero primal vector with nonzero first residue determines the other normalized weights (probability $p^{1-n}$). Each candidate in the scaled dual satisfies one orthogonality check (probability $1/p$ if a coefficient of a random residue is nonzero). The remaining nonzero candidates inside the respective balls are impossible. Union bounds count integer points using enlarged Euclidean balls at radii $D^{1/n}$ and $p/D^{1/n}$. Thus Claim 7 supplies, simultaneously for **every basis**, $g_0\ge H\ge g_{n-1}$, $H=D^{1/n}$. The last inequality uses the actual last reciprocal row. There is no probability estimate conditional on an oracle's choice.

Here and below indices start at zero. Write $c$ for the adjacent LLL decline factor. Claim 11 gives $g_a/g_{a+w}\le Y^w$ at aligned starts. For $i<j$, take every whole aligned jump contained in $[i,j]$ and use adjacent steps on the uncovered edges. At most $2w$ edges remain, also when there is no jump. Hence $g_i/g_j\le K Y^{j-i}$ with $K=c^{2w}$. This derives Claim 12 without using the misprinted boundary index and exponents in (7)–(8).

For $k\ge(n-1)/2$, comparison to the last row proves the upper bound immediately. For earlier $k$, multiply lower bounds on the first $k$ rows propagated from $g_0$ and on the remaining $s=n-k$ rows propagated from $g_k$. Their product is $D$, so
$$g_k^s\le D H^{-k} K^{n-1}Y^{[k(k-1)+s(s-1)]/2}.$$
(The empty prefix at $k=0$ uses only the second product.) Since $k\le s$, the bracket is at most $s(n-1)$ and $(n-1)/s<2$. Thus $C_Y=K^2$ suffices. The immediate lower estimate $g_k\ge H/(KY^k)$ deteriorates with distance from the first row because the inequality allows a decline at every step.

**Reflection lemma.** Apply exactly this scalar proof to $h_i=1/g_{n-1-i}$. Its determinant scale is $1/H$, its endpoints satisfy the same oriented inequalities and $h_i/h_j=g_{n-1-j}/g_{n-1-i}$. Consequently every $g_i\ge H/(K^2Y^{(n-1)/2})$ on the very same event. This improves the *exponent in distance* deep in the suffix, at the cost of the fixed-width constant. Neither statement models a typical slope.

## Finite replacement for Claim 7

Let $A$ be uniform over the $511\times512$ matrices over $\mathbb F_{3329}$. Write $N=1023$, $q=3329$, $D=q^{511}$. The residue kernel is the graph $(-Ay,y)$. Its annihilator is $(u,A^Tu)$, so $qL_0^*$ after coordinate exchange is the graph lattice for $-A^T$, with determinant $q^{512}$. This follows also by pairing with $q\mathbb Z^N$ and then with the graph. For radius $R<q$, each nonzero candidate with nonzero free component modulo $q$ passes the graph check with probability $q^{-m}$, where $m$ is the number of checks. Others have probability zero. Counting signs once and using Poisson summation gives failure probability at most
$$F_m(R)=\tfrac12 q^{-m}e^{tR^2}
 [\sqrt{\pi/t}(1+2z/(1-z))]^N,\qquad t=N/(2R^2),\quad z=e^{-\pi^2/t}.$$
Indeed the Gaussian majorizes the ball indicator after multiplication by $e^{tR^2}$, and $j^2\ge j$ bounds the positive Fourier tail by a geometric sum. At $(m,R)=(511,442),(512,446)$ the respective base-two log bounds are below $-10.22,-8.62$. Hence with probability greater than 0.996, simultaneously $g_0>442$ and $g_{N-1}<U=q/446$ for every basis. These straddle $D^{1/N}$. All widths can use this one event.

## What the repository certifies

For $N=sw$, let $a_j=g_{jw}$ and $V_j$ be the aligned block determinant. The primal check gives $V_j\ge(a_j/\sqrt{\gamma_w})^w$. The shifted block has determinant $V_ja_{j+1}/a_j$. Hermite on its reciprocal and the squared approximation factor $\rho$ imply $a_{j+1}\ge(V_ja_{j+1}/a_j)^{1/w}/\sqrt{\rho\gamma_w}$. Thus each aligned decline factor is at most $(\sqrt\rho\,\gamma_w)^{w/(w-1)}$. The final aligned head equals the projected minimum by the primal check. This recovers the Part 48 slide bound. The checker has no all-adjacent LLL test. Its successful loop postcondition is the checker itself. [Conditions](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Conditions.lean) · [Loop](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Loop.lean)

Reversal sends an aligned primal window to an aligned reciprocal window. The available reciprocal checks are shifted by one and omit a boundary. Even with one block the diagonal basis with lengths $(1,5,4)$ passes, while its reversed dual starts at $1/4$ and contains a row of length $1/5$. This example also satisfies the primal adjacent LLL decline with $c=\sqrt2$. Thus passing the primal checker does not imply passing it after reversal. A fresh reduction of the transposed graph supplies no identity of output flags. The reflection lemma bypasses this obstruction **only for scalar inequalities already proved on the original output**.

## Numbers at the requested indices

To quantify Appendix A even off the repository's width grid, state the output hypotheses explicitly. Suppose the rank-$N$ basis satisfies the adjacent inequality with $c=\sqrt2$ (ordinary size reduction and Lovász parameter $3/4$ suffice), and Claim 11 for every full jump between aligned heads, including a jump to the head of a partial final block. These are checkable hypotheses for a textbook-style profile. For $i\le j$, set
$$a=\max(0,\lfloor j/b\rfloor-\lceil i/b\rceil),\quad
 f(i,j)=(j-i-ab)\log c+a B,\quad
 B=\frac{b\log(2/\pi)+2\log\Gamma(2+b/2)}{b-1}.$$
Here $b=\beta$ and Blichfeldt's Hermite bound gives $\log(g_i/g_j)\le f(i,j)$ by the path proof. At $k=N-b$ take the larger of $442e^{-f(0,k)}$ and
$$\exp\left(\frac{\log D-(b-1)\log U-\sum_{i=0}^k f(i,k)-\sum_{i=k+1}^{N-1} f(i,N-1)}{k+1}\right).$$
The second expression is the reflected determinant argument with the actual endpoint and actual edge costs. Multiply the upper bounds for $g_i$ anchored respectively at $g_k$ and $g_{N-1}$. The determinant alternative is smaller in every row.

| Horizontal width | $k$ | Conditional JW lower bound on $g_k$, rounded down | Fully overlapping exact BKZ lower bound, rounded down | $\sqrt{6b}$, nearest 0.001 |
|---:|---:|---:|---:|---:|
|406|617|$1.53\,10^{-31}$|0.0569|49.356|
|506|517|0.1576|0.2726|55.100|
|647|376|$1.12\,10^{-54}$|0.6624|62.306|
|800|223|$1.20\,10^{-31}$|2.1626|69.282|
|1000|23|0.1526|79.0418|77.460|
|1020|3|156.27|308.89|78.230|

The JW column bounds the specified GS length. With a partial block at the end, $k$ need not be an aligned shortest-first index. In that case $g_k$ is an **upper** bound for the suffix minimum, so even the JW entry at 1020 does not certify the minimum. For fully overlapping exact BKZ the head equals the suffix minimum. That column uses the separate Part 48 primal event of probability at least 0.99 and its width-capped recurrence, $443.0664\exp(-P_k)$. For equal-block slide the rigorous answer at **each** displayed width is “outside the predicate”. Its Part 48 crossing is 1023. Padding or selecting a new partition would change the mathematical experiment. [Part 48, proofs and Hermite constants](wall1_null_terminal.md)

For reproducibility, the following Python (mpmath) interval calculation checks the finite endpoint and table inequalities. The recurrence rounds each Hermite cost upward before taking integer minima.

```python
from mpmath import iv as I
from math import ceil
I.dps = 45
n, q, M = 1023, 3329, 10**12
ln, exp = I.ln, I.exp
for m,R,cut in [(511,442,'-10.22'),(512,446,'-8.62')]:
    t = I.mpf(n)/(2*R**2)
    z = exp(-I.pi**2/t)
    logF = t*R**2+n*ln(I.sqrt(I.pi/t)*(1+2*z/(1-z)))-m*ln(q)-ln(2)
    assert logF/ln(2) < I.mpf(cut)
for b,jw,bk in [(406,'1.53e-31','0.0569'),(506,'.1576','.2726'),
                 (647,'1.12e-54','.6624'),(800,'1.20e-31','2.1626'),
                 (1000,'.1526','79.0418'),(1020,'156.27','308.89')]:
    k = n-b
    B = (b*ln(2/I.pi)+2*I.loggamma(2+I.mpf(b)/2))/(b-1)
    def f(i,j):
        a = max(0,j//b-(i+b-1)//b)
        return (j-i-a*b)*ln(2)/2+a*B
    head = ln(442)-f(0,k)
    refl = (511*ln(q)-(b-1)*ln(I.mpf(q)/446)-sum(f(i,k) for i in range(k+1))
            -sum(f(i,n-1) for i in range(k+1,n)))/(k+1)
    assert refl < head and exp(head) > I.mpf(jw)
    small = [0,0,I.mpf(4)/3,2,4,8,I.mpf(64)/3,64,256]
    C = [0,0]
    for l in range(2,min(k+1,b)+1):
        v = (ln(small[l])/2 if l<9 else
             l*ln(2/I.pi)/2+I.loggamma(2+I.mpf(l)/2))
        u = ceil(float((M*v).b))+1
        assert I.mpf(u) >= M*v
        C.append(u)
    S = [0,0]
    for j in range(1,k+1):
        p = min(-(-(C[l]+S[j]-S[j-l+1])//(l-1))
                for l in range(2,min(j+1,b)+1))
        S.append(S[-1]+p)
    assert I.mpf('443.0664')*exp(-I.mpf(p)/M) > I.mpf(bk)
```

Part 49 improves the BKZ width-1000 radius to 80.21 by propagating a two-plane constraint. Its separate Rankin quotient clears 88.98 at 1020. Width 506 is the heuristic GSA crossing for this horizontal benchmark. Width 647 in Part 39 uses prescribed deletion and exact SVP on a different lattice. The unresolved estimate here is a finite lower quantile for the selected terminal minimum at smaller widths. The target is a fixed comparison length. Part 47 counts an extra embedding coordinate, and its higher-height and prefix-lifting conditions require additional estimates. B2's fixed-direction conditional CBD bounds concern the projected random vector given the null geometry and do not supply the missing quantile. [Part 49](wall1_rankin_route.md) · [Part 47](wall1_decoupled.md) · [Projected CBD bounds](wall1_random_plant_heights.md)
