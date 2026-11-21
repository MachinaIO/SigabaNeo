# An ambient obstruction at height two

For every graph design, the ambient sum over nonintegral frequencies of physical length below 10 at height two exceeds **$10^{257}$**, including both the exact CBD weight and the Gaussian heat weight. Dropping the plane therefore loses too much even on the Part 92 event. For the CBD weight alone, both ranks also admit an actual horizontal basis prefix violating the proposed ceiling. Whether a prefix passing the width-506 reduction tests satisfies the heat-weighted ceiling remains open. [Finite test](wall1_theta_heights.md) · [Part 97](wall1_dist_unique.md) · [Wall 1](../PROOF_GAP.md)

## Physical coordinates

Let $m=511,n=512,N=m+n,q=3329$. The horizontal lattice consists of $(a,b)$ with $a+Ab=0\bmod q$. Pairing with $(qe_i,0)$ and $(-Ae_j,e_j)$ gives exactly
$$
qL_0^*=D=\{(x,z)\in\mathbb Z^N:z=A^Tx\bmod q\}.
$$
For horizontal prefix complement $V$ and orthogonal projection $Q$ onto it, $w\in V$ satisfies $\langle w,Qv\rangle=\langle w,v\rangle$. Consequently $(QL_0)^*=V\cap(D/q)$ in physical coordinates. The full projector is $Q\oplus1$ and the height-$k$ slice is $(kQX+QL_0,k)$. The Fourier argument is $kw$ in the original horizontal coordinates. Height introduces no extra dual coordinate in this sum. Each tested $k$ permutes the graph code modulo $q$, so a nonintegral frequency never becomes exactly integral. [Part 47](wall1_decoupled.md) · [Part 92](wall1_qary_gap.md)

## Distinct small residues with multiplicity certified from below

Embed the $q^m$ distinct graph codewords as their canonical representatives divided by $q$ in $[0,1)^N$. Partition each axis into $p$ equal half-open intervals. One box has at least $q^m/p^N$ points. Subtract a fixed member from every other member **in real coordinates**. The resulting $w$ lie in $D/q$, have distinct nonzero residues, and satisfy $|w_j|<1/p$. At $k=2$ the doubled residues are still distinct, with centered coordinates $2w_j$ for $p>4$. No independence or random-code approximation enters the count.

With $p=25$ this supplies more than $10^{369}$ terms with $\|w\|^2<N/625$. Each contributes at least
$$
e^{-cN/625}\cos^{6N}(2\pi/25),\qquad c=2\pi^2(1+1.9d)/d<38.
$$
The product of the count and this weight exceeds $10^{257}$ at both ranks. The wrapped-Gaussian majorant $A_2$ in the finite test is at least as large when evaluated in the ambient space, by the cosine inequality in that note. This obstruction holds pointwise in $A$, hence averaging or conditioning cannot fix the ambient bound. It gives no such lower bound in a prescribed plane.

## What a worst case over planes permits

For the CBD-only statistic one can put many integer translates of **one** nonintegral mode in the same plane. Take $p=55$ in the box argument and choose any nonzero difference $w$. For each $d\in\{505,506\}$ take $d-1$ coordinate axes omitting a nonzero coordinate of $w$. Their span together with $w$ is a rational $d$-plane $V$. Add to $w$ every signed sum of 80 distinct chosen axes. All resulting vectors lie in $V\cap(D/q)$, have length at most $\sqrt{80}+\sqrt N/55<10$, and carry identical CBD weight. Their combined CBD weight exceeds $10^{100}$ at height two. An actual horizontal basis realizes this plane since $L_0\cap V^\perp$ is saturated in $L_0$, has rank $N-d$ by rationality, and its basis extends to one of $L_0$.

These prefixes have no certificate of passing the twin tests or of arising by dropping the shortest head of a passing block. Also the translates pay a substantial Gaussian penalty in the heat-weighted statistic. Thus the unrestricted-prefix CBD-only assertion has probability zero, while the all-passing-prefix assertion still needs a bound on the intersection with the selected plane. An ambient multiplicity estimate alone cannot establish the requested joint 99.5% certificate.

## The confidence of the minimum event

The published Part 92 estimate by itself charges nearly 1%. Its same threshold $T$ actually admits a charge below 0.42% by retaining two ball coordinates before applying the exponential majorant. At fixed remaining coordinates of squared length $s\le T^2$, put $r^2=T^2-s$. Centered unit squares at the integer pairs in the disk fit in the disk of radius $r+1/\sqrt2$. For $a=N/(2T^2)$,
$$
(r+1/\sqrt2)^2 e^{-ar^2}\le 1.05/(ae)+10.5
$$
by the quadratic Young inequality and $x e^{-ax}\le1/(ae)$. Sum the resulting bound $\pi(1.05/(ae)+10.5)e^{a(T^2-s)}$ over the remaining coordinates. Pair opposite vectors and apply the $q^{-n}$ membership bound to eligible nonzero vectors as in Part 92. This improves the confidence of the minimum event alone and leaves the multiplicity obstruction intact.

## Interval certificate

Run the following with Python and mpmath. All comparisons involving real quantities use interval arithmetic.

```python
from math import comb, gcd
from mpmath import iv as I
I.dps = 60
q,m,n,N = 3329,511,512,1023
assert all(gcd(k,q)==1 for k in range(2,32))
for d in (505,506):
    c = 2*I.pi**2*(1+I.mpf('1.9')*d)/d
    assert c < 38 and N < 100*25**2
    count = (q**m-1)//25**N
    assert count > 10**369
    assert count*I.exp(-I.mpf(38)*N/625)*I.cos(2*I.pi/25)**(6*N) > 10**257
    assert q**m > 55**N
    assert I.sqrt(80)+I.sqrt(N)/55 < 10
    assert comb(d-1,80)*2**80*I.cos(2*I.pi/55)**(6*N) > 10**100

T = I.exp(I.mpf(n)/N*I.ln(q))*I.sqrt(N/(2*I.pi*I.exp(1)))*I.exp(I.ln(I.mpf('.0199'))/N)
a = N/(2*T**2)
v = I.exp(-I.pi**2/a)
theta = I.sqrt(I.pi/a)*(1+2*v/(1-v))
factor = I.pi*(I.mpf('1.05')/(a*I.exp(1))+I.mpf('10.5'))
assert T < q
assert factor*I.exp(a*T**2)*theta**(N-2)/(2*q**n) < I.mpf('.0042')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT. Each result was verified separately.

* **Ambient obstruction.** The bound log₁₀ > 257.70568 holds for every A. It comes from pigeonholing the q^511 graph-code
  representatives into boxes of side 1/25.
* **Scope of the ambient obstruction.** Part 99's A_k is restricted to w ∈ H* = V ∩ (D/q). The ambient bound therefore only
  rules out summing over the whole ambient dual. It says nothing about the count inside H*.
* **Cosine-only prefixes.** The construction is legitimate, with log₁₀ > 101.11 / 101.19 at ranks 505 / 506. It certifies
  neither the reduction tests nor a heat-weighted violation.
* **Minimum event.** Its probability is > 99.5888646%.

All embedded blocks pass, as do those of Parts 92, 97 and 99.
