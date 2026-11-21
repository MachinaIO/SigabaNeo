# Probabilistic depth truncation for the terminal plane

There is a conditional product bound using only the marked lattice at the **start** of a block. Its factors are finite torus coverage probabilities. A reachable width-506 state makes every factor equal to one for a block of 103 draws, and its designated plane can actually have depth 103. This rules out a useful small-depth bound uniform over starting states. The frequency of such states, and the contribution from shallow planes, are separate questions.

## What a deep plane forces

Use the unit appends, physical scale and inherited signed lexicographic selector of [Part 108](wall1_first_tour.md). In the unconditioned reduced experiment of [Part 117](wall1_idea_round2.md), let draw i take the old lattice to retained lattice L_i. Set n=406. In L_n select its shortest line and then the designated shortest line modulo the first. Their full preimage is the saturated plane P_n. Its area is exactly the a_0 of [Part 120 and its audit](wall1_plane_count.md). Depth counts consecutive horizontal full inverse images of this plane, backwards from draw n. The independent last draw n+1 is outside this definition.

At draw i let W_i be its window, v_i its winner and Q_i its quotient. Starting with N_n=P_n, form M_i=(Q_i restricted to W_i)^{-1}(N_i). A successful horizontal pullback means that height vanishes on **all** of M_i. Then set N_{i-1}=M_i inside L_{i-1}. Thus depth at least k means precisely k such successes at i=n,...,n-k+1. At each one the kernel line v_i lies horizontally and must be the designated shortest of L_{i-1}. Also every generator of N_i must have a horizontal lift. For a horizontal kernel, adding a multiple of v_i cannot change lift height. These incidence conditions explain why a run of horizontal winners can overcount depth. At the start the lifted lattice has rank k+2 and determinant equal to the terminal area times the product of the k winner lengths. This follows by basis extension at each quotient. [Part 121 and its audit](wall1_global_quotient.md)

For example, with B_i the event of a horizontal winner, the ordinary chain rule bounds the tail by the product of Pr(B_i | all earlier B's in this block), in chronological order (stop at any zero factor). Each factor averages the actual w_0 over the surviving past. Multiplying unconditional rates, or averaging a product of w_0 evaluated on unrestricted trajectories, has no such justification.

## A product without adaptive survivor laws

Condition on the entire history through n-k and denote its marked state by (L,H,frame). Compute the first k vectors of successive exact shortest-vector selection **in L alone**, projecting after each selection. Before selection j write E_j for this projected old space, L^j for its lattice, H^j for the projected initial mark in E_j/L^j, and t_j for its minimum. Index j from 1, so L^1=L. Embed the spaces using the original ambient frame with zeros in all appended coordinates.

On depth at least k the k chronological winners are exactly these prescribed vectors. Indeed the composite inverse image inside L contains the lifted kernel flag of all the intervening quotient maps. At each stage the selected line therefore belongs to the projection of L. As that projected lattice is contained in the actual window, its designated minimizer must coincide with the global winner, including the tie rule. This argument also works for the two terminal flag selections once the whole plane is old.

Along this forced path the j-th raw column has an independent initial displacement uniform in H, by the fixed linear map of Part 108. Its forced projection gives a uniform class u_j in H^j. In physical coordinates the previous new height axes are orthogonal to these prescribed projections. In particular competitors made from this column and L^j alone have squared lengths
\[
 h^2+\|y\|^2,\qquad y\in h\tilde u_j+L^j,\quad h=1,2,\ldots .
\]
One may test both signs for ties. Ignoring all competitors involving other columns can only increase the chance of survival. Define p_j as the fraction of u in H^j for which some displayed competitor is strictly shorter than t_j. Then
\[
 \Pr(\mathrm{depth}\ge k\mid\mathcal F_{n-k})
 \le \prod_{j=1}^k(1-p_j).
\]
This uses independence **before** imposing any winner or incidence test. No evaluation of an adaptive transition kernel is needed inside the product. For an unconditional bound take its expectation over the actual block-start law. One can also multiply by the initial-state indicator that the deterministic old plane after the k removals passes the terminal area gate, for a bound on the weighted bad tail: on depth at least k its two lengths are forced and the actual determinant is the starting determinant divided by the k lengths. The terminal selector weight is at most one.

## Computing a factor

For any of these old projected states write t for its minimum. At positive height h<t put r_h=sqrt(t²-h²), and let C_h be the number of points of the strict ball of radius r_h in the coset h u+L. The [Part 110 layer mean](wall1_additive_tour.md) is m_h = #(L_h intersect ball)/|hH| where L_h/L=hH. The single-height hit probability instead counts **distinct cosets** hit, divided by |hH|. The full hit probability counts their union after pullback to H. In particular a raw first moment generally gives an upper bound on a hit. Exact w_0 additionally compares tied competitors under the selector.

A lower bound needing only first moments and a deterministic multiplicity cap is
\[
 p\ \ge\ \max_{1\le h<t} m_h/(1+2r_h/t)^{\mathrm{rk}(L)}
\]
with empty maximum zero. Disjoint balls of radius t/2 around points of one coset fit in the ball of radius r_h+t/2. Alternatively count only the open ball of radius min(r_h,t/2) in each layer: it has at most one representative per coset, so its mean is already a lower bound. These factors are computable given the starting lattice; neither the nesting L ⊆ L_h ⊆ L/q (here L/q means the scaled lattice) nor the determinant specifies their values. The universally available vector at height q has length q, whereas projected q-axes give an old minimum at most q. Strict improvement requires more.

## A reachable obstruction at 506

In the reduced experiment take the zero 400-by-105 graph and zero suffix columns up to the chosen block start. At restart the lattice is orthogonally q Z^400 plus Z^105. Each zero draw adds a new unit axis and removes the earliest surviving unit axis by the tie rule. Consequently the same description holds with later coordinate labels at *any* block start. Its probability is positive under independent uniform residues. Here t=1. A positive-height tie can only be the pure new unit axis, and the negative old unit axis precedes it. The actual conditional w_0 is exactly one, even though the next column is random.

On the forced path the first 105 old minima are one. In fact, for k≤103 and arbitrary next k columns, the next k winners and the two terminal selections are the earliest k+2 starting unit axes in order. To see this, project away the successive old unit axes. Each vector using the new columns has a nonzero integral coordinate in their new height space, and equality at length one forces a pure signed new axis. It loses the lexicographic tie to an earlier unit axis. All the lifted generators are the old axes. Thus the conditional depth tail is **one** for these k. The weighted bad tail is also one conditionally: the two old lengths and the terminal winner length are one, the retained determinant is still q^400, and the area cutoff exceeds one since G_505 ≥ 1/2 by the cube of side two enclosing the unit ball and q^(400/505)>3. The exceptional all-zero past is tiny; this example does not lower-bound the unconditional tail by a budget-sized number. It shows exactly why a uniform fresh-win floor or a state-uniform shallow estimate fails.

## What the truncated first moments still cost

Use the convention that depths 0 through K are retained, and charge depth ≥K+1 once. Take K<406. For exact depth l≤K, stop at draw i=n-l, the first positive-height inverse image encountered going backwards. Its incoming witness has rank r=2+l, its inverse image has rank r+1, and the horizontal kernel P at that draw has rank r in L_{i-1}. Thus the bound K+2 applies to the **old kernels**; a transition itself can involve rank K+3. There are l+1 draws back to and including the stopping draw, plus the terminal weight which is already integrated as w_0.

Here is an explicit conditional first-moment bound. Given the state just before i, enumerate saturated rank-r kernels P and triples (P,h,[y]) with positive height generator h and y in hU+L_{i-1} modulo P. Their covolume is
\[
 b(P,h,y)=\det P\sqrt{h^2+\|\pi_{P^\perp}y\|^2}.
\]
Charge one if the generated lattice is saturated, contains v_i, and after projection and the next l horizontal pullbacks read in reverse it gives the designated bad terminal plane. Concretely, project the candidate by Q_i, embed it horizontally at each later draw, require it to contain that draw's winner and project again. Compare the final plane with P_n and test its area. Multiply by w_0 at the final state. The area test is equivalently
\[
 b(P,h,y)< A(t_{\rm end})\prod_{j=i}^n |v_j|.
\]
The first moment of this sum is actually the weighted exact-depth charge: the terminal plane and all its full preimages are unique, and a lattice at the stopping draw determines P,h,[y] uniquely. The incidence tests with saturation ensure the reverse projections recover full preimages.

Average over hU by the Part 120 fiber formula, keeping its conditional average over U, then over subsequent independent raw columns in chronological order. More explicitly, the sum over [y] uses the projected disk in the displayed covolume test with weight 1/|hH| and an inner mean over U satisfying hU=y modulo L. Future selectors, cutoffs and weights stay inside that mean. On deterministic upper bins for the right side one may use the disk for the bin ceiling and drop filters for a first-moment upper bound. This bounds the shallow contribution by a sum of bounded-rank statistics at the appropriate late states. Those states can also be generated from one common block start by integrating the remaining earlier draws of the block. Even at l=0 the disk sum runs over **old planes** P, with radii depending inversely on det P. Averaging fresh displacements counts extensions of each existing P. It gives no upper bound on the abundance of those kernels at that state. Integrating one more draw to estimate their abundance raises the old horizontal rank again. Thus truncation of horizontal depth alone does not close the first moments.

Let S_l denote the history average of the filtered moment above and T the history average of the product for k=K+1 (optionally gated). At width 506 a sufficient test is
\[
 T+\sum_{l=0}^K S_l\le 0.00488848,\qquad \mathbb E F_*\le 0.00488848 .
\]
The latter is the separate positive-height charge on draw 407. For scale, even an assumed uniform fresh-win probability of 1/2 would take eight draws to get the tail alone below the horizontal budget, leaving 0.00098223 for all shallow terms. The zero-graph history rules out that hypothesis. Neither the distribution of the forced-path product nor the filtered kernel sums have the required quantitative estimates at 506. This leaves the two [Wall 1](../PROOF_GAP.md) budgets open.

## Exact small experiments

I reran the [Part 119 SVP kernel](wall1_experiments.md) with the Part 121 flag lifts. At q=17 the entries below are counts out of 64 seed labels (0 through 63) at each step. A fresh win means the selected vector has nonzero height, including any selected tie. The rows are frequencies along simulated paths.

| Width | Fresh wins at draws 1 through 10 | Depth-one planes at the same draws |
|---|---|---|
| 5 | 64,64,62,63,61,63,63,59,60,56 | 0,0,0,0,0,0,0,0,0,1 |
| 7 | 64,64,63,61,60,63,60,55,55,61 | 0,0,0,0,0,0,0,1,1,1 |

All remaining planes had depth zero. For exact **conditional probabilities**, I also enumerated every next raw column at each of six states on one seed-0 path of width 5 with q=3. The fresh-win probabilities in order were (81,81,81,81,79,63)/81. Strict improvements gave the same numerators. Enumeration counts residue preimages even if the mark loses rank. These tests do not estimate the width-506 tail.

To reproduce the q=17 table, run Part 121's Python block with the following line immediately after `past.append(T)` and assertions immediately before its assignment to `Y,P,H,dy,dp`. Keep its existing depth and interval assertions.

```python
            row['fresh'] += int(T[0,-1] != 0)
```

```python
    expected = {4:[64,64,62,63,61,63,63,59,60,56],
                6:[64,64,63,61,60,63,60,55,55,61]}
    assert [r['fresh'] for r in out] == expected[d]
```

For the exhaustive check, use the imports and cut function in that same block, then run the following in Sage Python. All comparisons below use exact arithmetic.

```python
from fractions import Fraction
from itertools import product
d,q=4,3
rng=Random(0)
B=q*identity_matrix(QQ,d)
C=identity_matrix(ZZ,d)
for expected in [81,81,81,81,79,63]:
    def window(raw):
        a=vector(QQ,[x%q for x in vector(ZZ,raw)*C])/q
        return B.stack(matrix([a*B])).augment(matrix(QQ,d+1,1,[0]*d+[1]))
    old=shortest(B)[1]
    fresh=strict=0
    for raw in product(range(q),repeat=d):
        c,s,_,_=shortest(window(raw))
        fresh+=int(c[-1]!=0)
        strict+=int(s<old)
    assert fresh==strict==expected
    T,H,B,_=cut(window([rng.randrange(q) for _ in range(d)]))
    C=(C.augment(zero_matrix(ZZ,d,1))*H.transpose())[:,1:]%q
assert 3329**400 > 3**505 and Fraction('0.954')*3/2 > 1
budget=Fraction('0.00488848')
assert Fraction(1,128)>budget>Fraction(1,256)
assert budget-Fraction(1,256)==Fraction('0.00098223')
assert 2*budget==Fraction('0.00977696')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Product bound.** The block-start product bound ∏(1 − p_j) holds. All k winners are computable at block start, and each test
  uses its own independent raw column.
* **Reachable obstruction.** The zero restart graph plus 303 zero suffix columns has probability q^{−400·408} > 0. On it the
  depth is exactly 103 and the terminal plane fails the area gate.
* **Shallow accounting.** At depth ℓ the old kernel has rank ℓ+2. The sum over old planes under the late-state law has no
  estimate, even at ℓ = 0.
* **Reruns.** Both experiments match exactly.

Neither 0.00488848 budget is established.
