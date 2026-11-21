# Conditioning on a shortest-vector void in the first tour

Two comparisons fail. Even for a primitive mark present on every draw, conditioning on its selection can *increase* the expected short-vector count of its quotient. For the actual selected process, a conditional probability of a short vector in the next window can exceed the entire unconditional first moment of short pairs, at a threshold below that window's own GH. Both examples start at the cubic graph append of [Part 108](wall1_first_tour.md).

## The comparison and its reference law

Fix the incoming physical lattice, subgroup and frame. Draw one uniform displacement and write its window as $W$. For a candidate $v$, take the incidence law conditional on $v$ being primitive in $W$. Under this law $Q_vW$ exists as a lattice before testing shortestness. Let $A_v$ require absence of all strictly shorter nonzero competitors and all lexicographically earlier signed minimizers. The point-set order is inclusion of competitor configurations, excluding the marked pair and using the prescribed sign for the mark. The acceptance indicator decreases in this order.

Put $N_R(L)=\#\{x\in L:0<|x|<R\}/2$. One natural output order compares the radial counting functions pointwise for every $R$. Stochastic domination in this order would imply, in particular,
$$
 E[N_R(Q_vW)\mid A_v]\le E[N_R(Q_vW)]
$$
under incidence. Equivalently the acceptance indicator and the count must have nonpositive covariance. One can also use determinant-normalized radii. For actual histories the analogous comparison averages over the true selected outputs in the reference law. If $S'$ is the resulting marked state and $F_c(S')$ the expected short-pair count in its next window at its own relative threshold $c$, the proposed probability bound would require $P(\text{next window short}\mid A_v)\le E F_c(S')$. This last inequality asks less than stochastic domination. Its right side integrates out the current draw as well as the fresh next draw. Keeping the current state fixed in Part 110's formula already gives a valid conditional bound, but leaves the history dependence intact.

## A common horizontal mark, rank four

Take $L=2\mathbb Z^3$, $H=(\mathbb Z/2)^3$, and $v=(-2,0,0,0)$. Every window contains this primitive vector. For bits $g=(a,b,d)$ the shortest squared length in either unit-height layer is $1+a+b+d$. All layers of absolute height at least two have squared length at least four. Thus $A_v$ is exactly $g=(1,1,1)$, of probability $1/8$. At equality the first coordinate of any competing vector of length two is greater than $-2$. In particular the event is exactly the strict-shorter void even with the ambient lexicographic rule.

Project away the first coordinate. At $R^2=7/2$ the quotient has no nonzero horizontal point inside the ball and only heights $\pm1$ contribute. At height one the allowed horizontal coordinates are congruent to $(b,d)$ modulo two. Each odd coordinate gives two choices and each even coordinate gives one. Hence the short-pair count is $2^{b+d}$. Its conditional mean is **4**, against the incidence mean **9/4**. The quotient determinant is four on every incidence draw, so rescaling by its own GH preserves this comparison at the corresponding radius. Even the hit event $N_R\ge4$ increases from $1/4$ to one. The reversal comes from several equally close representatives of a single retained coset. Distinct graph windows of the same determinant cannot be properly nested, and their radial counts need not be ordered by their sets of forbidden competitors. Uniformity of the bits supplies no Harris inequality of the required sign for these observables.

## A future window below its own GH, ranks two through four

Take $q=5$, window rank $b=2,3,4$, $r=b-1$, initial $L=5\mathbb Z^r$ and full mark. Use two graph appends. Let $A$ record selection of the negative vertical unit vector at the first. This is exactly the zero draw, of probability $5^{-r}$. Here incidence itself identifies the draw. This example tests conditioning on the *actual selection history*, while the common-mark example isolated the effect of the void within incidence.

Write $s$ for the first selected length. The next window determinant is $5^r/s$. Choose
$$
 c_b=\frac{\sqrt{11/10}}{G_b\,5^{r/b}},\qquad
 R(s)^2=(c_b G_b(5^r/s)^{1/b})^2=(11/10)s^{-2/b}.
$$
All three constants are below one (use $V_2=\pi,V_3=4\pi/3,V_4=\pi^2/2$ and $G_b=V_b^{-1/b}$). On $A$, projection restores the original state. Only a zero second displacement contributes, giving one short pair. Off $A$, integrality and the absence of unit vectors give $s^2\ge2$. Then $R(s)^2\le(11/10)2^{-1/b}<1$. Every nonhorizontal layer misses the ball. The horizontal minimum is at least $\sqrt3\,s/2>1$ by nearest-lift rounding. Consequently
$$
 P(\lambda_1(W_{\rm next})<R(s)\mid A)=5^{-r},
 \qquad E F_{c_b}(S')=5^{-2r}.
$$
The latter is also the unconditional hit probability since the pair count is zero or one. The values of the Part 110 averaged positive-layer count are respectively $5^{-r}$ and zero on the two classes of histories. Thus it increases upon revealing this selection. The calculation uses the determinant of each tested window, including on histories excluded by conditioning.

## Exact enumeration

The first loop enumerates projected points. The second enumerates both graph columns in each rank. It computes the first SVP squared length by testing all heights through five (the horizontal competitor has length five) and minimizing each horizontal residue separately. For nonunit selections it checks the two exclusion bounds above using integers. For unit selections the small ball around a height-one point allows only horizontal coordinate zero.

```python
from itertools import product
from fractions import Fraction as F

bits = list(product(range(2), repeat=3))
counts = []
accepted = []
for a,b,d in bits:
    n = sum(2*(x*x+y*y+1)<7 for x,y in product(range(-2,3),repeat=2)
            if (x-b)%2 == (y-d)%2 == 0)
    counts.append(n)
    if 1+a+b+d >= 4:
        accepted.append(n)
assert accepted == [4] and F(sum(counts),8) == F(9,4)

for width in (2,3,4):
    draws = list(product(range(5), repeat=width-1))
    joint = on_A = mass_A = 0
    for g in draws:
        s2 = min([25] + [k*k+sum(((k*x+2)%5-2)**2 for x in g)
                         for k in range(1,6)])
        if s2 > 1:
            assert 11**width < 10**width*s2 and 3*s2 > 4
        for z in draws:
            pairs = int(s2 == 1 and 10*(1+sum(((x+2)%5-2)**2
                                               for x in z)) < 11)
            joint += pairs
            if s2 == 1:
                mass_A += 1
                on_A += pairs
    assert (joint, on_A, mass_A) == (1, 1, len(draws))
```

## What survives

Within a fixed marked parent, adding individual vetoes shrinks the accepted set. For any nonnegative count $X$, $E[X\mid A]\le E[X]/P(A)$ for $P(A)>0$; the two-append example attains equality. On a fixed history, uniformity on $kH$ still gives the exact mean at height $k$ as $\#(L_k\cap B^\circ_{\sqrt{R^2-k^2}})/|kH|$, where $L_k$ is the torus preimage of $kH$ and $0<k<R$. Add the horizontal pair count and sum positive heights to bound the hit probability. Averaging that bound with the actual history weights remains valid. The examples leave open estimates specific to likely histories, particular thresholds or large ranks. Neither a sign rule nor a new terminal constant at widths 406 and 506 follows. The certified last-window thresholds from [Part 110](wall1_additive_tour.md) are respectively $8.66605\times10^{-6}$ and $5.27489\times10^{-6}$ with zero failure probability. The Haar incidence law of [Part 105](wall1_selection_law.md) and the Hecke calculation of [Part 111](wall1_hecke_gap.md) use different reference measures.

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT. Both counterexamples were re-enumerated with integer arithmetic under Part 108's model.

* **Rank 4.** The mean of 9/4 rises to 4 short pairs within the same incidence law, and the quotient determinant is fixed at 4.
* **Ranks 2–4.** The conditional hit probabilities are 1/5, 1/25 and 1/125, against unconditional means 1/25, 1/625 and
  1/15625. Here c_b^b = (11/10)^{b/2}·V_b/5^{b−1} < 1.

Part 110's layer expectation stays exact conditional on the marked state. What fails is using the unconditional average as an
upper bound after a selection has been revealed.
