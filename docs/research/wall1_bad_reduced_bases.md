# How small can the terminal block start be over all reduced bases?

The rank-1023 high-probability question remains open at all four widths. There is a genuine choice of terminal length on a positive-Haar-measure set already in rank three. An exhaustive finite graph ensemble below shows how often that choice actually lowers the minimum. At the other endpoint, full width, the proposed fixed-factor deficit is false asymptotically.

## Which minimum and which probability?

Put $k=N-b$, use zero-based indices and normalize the ambient covolume to one. Write $M_b(L)=\min_B g_k(B)$ over fully size-reduced exact BKZ-$b$ bases, including truncated windows. This minimum is attained. Indeed $g_{i+1}\ge t g_i$, $t=\sqrt3/2$, by the adjacent two-column test and size reduction. The determinant bounds the first length from above by $t^{-(N-1)/2}$, so there are finitely many first vectors. For each choice its projection quotient is a lattice and the same proof in that quotient gives finitely many next vectors. Size-reduced lifts have bounded coefficients along the prefix. HKZ supplies at least one basis.

For fixed rank an operational threshold needs a probability level. For example the 1% lower quantile is $Q_{.01}=\inf\{r:\Pr(M_b\le r)\ge .01\}$. Existence of a bad basis with probability 99% instead calls for the **99% quantile**. Concentration sufficient to identify these two scales is a separate claim. At the four widths A6 gives individual 99% lower certificates 0.005933200, 0.015621412, 0.039603438 and 0.140797866. Its zero-weight boxes cannot be used to bound either quantile from above. For an actual count $C$ of bad unsigned flags a sufficient second-moment estimate would be $(\mathbb E C)^2/\mathbb E C^2\ge .99$, by Cauchy–Schwarz. Neither moment ratio nor even a positive contribution to the first moment follows from the relaxed witness boxes. [Unfolding](wall1_volume_method.md) · [Disjoint tests](wall1_volume_svp_weights.md) · [Packing exclusion](wall1_poisson_exponent.md)

For a primitive prefix sublattice $W$, $T=\pi_{W^\perp}L$ has determinant $1/\det W$. Its shortest vector realizes the minimum of $\det W'/\det W$ over primitive one-rank extensions $W'\supset W$, by the base-times-height identity. Thus one minimizes this ratio over *completable* prefixes. Small prefix determinant makes the quotient covolume larger. Even fixing the quotient shape and appending its HKZ basis leaves crossing tests to verify. For full HKZ there is almost surely a unique projected shortest **line** at every depth. For any fixed integer flag and two independent candidate directions, equality of projected squared norms is a nontrivial polynomial equality in the Gram matrix after clearing the prefix determinant. Nontriviality follows by varying the metric on the quotient. Taking the countable union over flags and directions preserves nullity. Hence optimizing over full HKZ bases on Haar input leaves a single GS profile, even when inspecting an interior coordinate. [Recursive quotient law](wall1_haar_prefix_law.md)

## Haar bounds and examples

**Full width.** For $b=N$, $M_N=\lambda_1(L)$. With $V_N$ the unit-ball volume, Siegel's mean theorem on signed pairs gives
\[
 \Pr[M_N\le c V_N^{-1/N}]\le c^N/2 .
\]
The GSA convention in the volume note gives $G_{N,N}=(\pi N)^{1/(2N)}\sqrt{N/(2\pi e)}$, whose ratio to $V_N^{-1/N}$ tends to one by Stirling. For every fixed $c<1$ the probability of $M_N\le cG_{N,N}$ tends to zero exponentially. Moreover $V_N M_N^N$ converges to an exponential random variable of rate $1/2$, so $M_N/G_{N,N}\to1$ in probability. This establishes the asymptotic threshold at that endpoint only. [Södergren's Poisson theorem](https://arxiv.org/abs/1001.3623)

**A Haar probability bound at finite width.** In rank three and width two, $\Pr(M_2\le c)\le 8c^6/(9\zeta(3))$ for $0<c\le1$. In particular the probability of a 10% deficit from GSA is at most 39.3%. To prove this, write $r=g_0$, $h=g_1$ and $g_2=1/(rh)$. In the oriented basis chart of Part 50 the density after division by the four orientation-preserving sign choices is $(K_3/4)r^4h^2\,d\log r\,d\log h\,d\mu$, with $K_3=8\pi^2/(\zeta(2)\zeta(3))$. The first adjacent test forces $r\le h/t$. Integrating over the entire coefficient cube, $0<h\le c$, and $0<r\le h/t$ bounds the expected unsigned count by $K_3c^6/(96t^4)=8c^6/(9\zeta(3))$. Markov gives the claim. Even the probability of reaching GSA from below is at most 74.0% here. [Basis intensity](wall1_volume_method.md)

**Positive measure versus typicality.** For every fixed $N\ge b\ge2$ and every $r>0$, $\Pr(M_b<r)>0$. Choose a diagonal basis with strictly increasing lengths, product one, and the first $k+1$ lengths below $r$. The remaining $b-1\ge1$ lengths absorb the determinant constraint. Every projected suffix has a unique shortest line with strict gap. These finitely many gaps persist on a neighborhood, since bounded-length tests in a neighborhood of an invertible basis involve only finitely many integer candidates. This is an open set of HKZ bases and its lattice image has positive Haar measure. The construction gives no dimension-uniform mass bound.

**Two terminal lengths on the same Haar input.** In rank three take $u=(1,0,0), v=(0,0,.94), w=(.49,.90,0)$ and scale all columns by $s=.846^{-1/3}$. For width two, both orders $(v,u,w)$ and $(u,w,v)$ are reduced. The pair $u,w$ is Gauss reduced with strict inequalities since $.49<1/2$ and $.49^2+.90^2>1$. The other pair test compares orthogonal lengths .94 and 1 in the first order, .90 and .94 after projection in the second. Hence the terminal lengths are $s$ and $.90s$. The first order is full HKZ since $v$ is globally shortest and the quotient is Gauss reduced. Both flags persist under small perturbations, up to orientation signs. This gives an open set where optimizing BKZ beats full HKZ and the ratio is below .91. It yields no frequency estimate at the four requested widths.

## Exhaustive finite experiment

Use the uniform graph $z=ax+by\pmod {47}$ in rank three with independent uniform $a,b$. All 2,209 inputs have determinant 47 before rescaling. At width two the repository's GSA terminal convention gives exactly 1 after normalization. In 48 inputs there are multiple terminal lengths. In 24 the minimum beats every full HKZ choice. The exact counts with $M_2\le c\,G_{3,2}$ are 269 for $c=.8$, 625 for $c=.9$, and 1,197 for $c=1$. In particular a deficit of 10% occurs on 28.3% of inputs, and even a threshold of 1 only covers 54.2%. Small terminal lengths usually need no exceptional basis in this ensemble.

The enumeration works in unscaled integer coordinates. Write $s=|v|^2$ for a primitive first vector. The adjacent bounds give $27s^3\le64q^2$. Its rank-two projected quotient has area $q/\sqrt s$, so its squared minimum is at most $q/(t\sqrt s)$ by Gauss reduction. Every shortest line has a size-reduced lift $w$ with $h=|w|^2\le q/(t\sqrt s)+s/4 <60$ for the allowed integer $s$ at $q=47$, using $1\le s<18$. For such lifts the remaining first-window test is exactly $h\ge s$, since the pair is size reduced. The quotient shortest vector is primitive and extends to a Gauss basis in rank two. Size reducing the final lift along the first column preserves both tests. Thus the list of possible terminal *values* is exhaustive, including ties. Primitivity is tested in graph-basis coordinates. All threshold comparisons use integer or rational arithmetic.


```python
from itertools import product
from collections import Counter
from fractions import Fraction
from math import gcd

q = 47
dot = lambda v,w: sum(x*y for x,y in zip(v,w))
vectors = []
for v in product(range(-8,9), repeat=3):
    s = dot(v,v)
    if 0 < s <= 60 and next(x for x in v if x) > 0:
        vectors.append((s,v))

counts = Counter()
for a,b in product(range(q), repeat=2):
    short = [(s,v) for s,v in vectors if (v[2]-a*v[0]-b*v[1])%q == 0]
    ambient = min(s for s,v in short)
    values, hkz = set(), set()
    for s,v in short:
        if 27*s**3 > 64*q*q: continue
        z = (v[2]-a*v[0]-b*v[1])//q
        if gcd(v[0],v[1],z) != 1: continue
        lifts = []
        for h,w in short:
            p = dot(v,w)
            D = s*h-p*p
            if D > 0 and 2*abs(p) <= s:
                lifts.append((D,h))
        D = min(d for d,h in lifts)
        if any(d == D and h >= s for d,h in lifts):
            values.add(Fraction(D,s))
            if s == ambient: hkz.add(Fraction(D,s))
    assert hkz
    counts['distinct'] += len(values)>1
    counts['beats every HKZ'] += min(values)<min(hkz)
    for c in (Fraction(4,5),Fraction(9,10),Fraction(1)):
        counts[str(c)] += min(values)**3 <= c**6*q*q
print(dict(counts))
```

## Implication for the frontier

The small example disproves uniqueness for finite-width BKZ and the full-width theorem rules out a universal fixed-factor deficit across all width regimes. Neither locates the minimum at rank 1023 and widths 406, 506, 647 or 800. A positive-measure cusp cannot refute a 99% guarantee. The finite graph experiment also supplies no transfer at rank 1023. The fixed-rank Hecke limit concerns increasing modulus and does not give the required finite-modulus error. [Graph-to-Haar transfer](wall1_hecke_transfer.md)

If one proves that more than 1% of inputs possess a basis with terminal length strictly below a given target, a simultaneous 99% lower bound at that target is impossible. A theorem for a selected output could still follow from an additional static property of that output or a selection law. Even an existence theorem for bad bases would not logically require tracking a particular trajectory step by step. At the stated widths, neither the impossibility of a simultaneous near-GSA theorem nor its truth has been established. [Wall 1 frontier](../PROOF_GAP.md)
