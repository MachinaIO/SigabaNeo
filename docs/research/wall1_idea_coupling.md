# Coupling the terminal observation of the first tour

For the horizontal-first, no-lookahead model with the ties of [Part 108](wall1_first_tour.md), the most economical independent-window comparison uses just the last draw. There is an explicit coupling for a threshold event, and a first-moment bound for replacing the discrete displacement by continuous torus noise. These solve different parts of the comparison. Even with full torsion, the latter leaves a random horizontal lattice in the reference window. An exact two-draw example below measures the cost of erasing that dependence.

## What can agree exactly?

Work in physical coordinates. At the penultimate marked state S write L for the retained lattice, H for the displacement subgroup, and W(g) for the extension of L by (g,1). Include the ambient frame in S. A terminal statistic f can use the full window or its quotient by the chosen shortest vector. It can include normalization by the observed determinant. On the real side f has finite support at fixed tour length. For an independent Haar reference in rank at least two, the determinant-normalized minimum is atomless: for each nonzero integer label the fixed-length level set in the determinant-one matrix group has measure zero, and there are countably many labels. Thus in *any* coupling the exact minima differ almost surely. The same argument applies to a reference quotient with a shape law absolutely continuous with respect to Haar. Equality at a fixed threshold, or equality of a binned minimum, is a meaningful weaker target.

Fix a reference window law ν in advance and a finite-valued observation f. Let p_S(j) and p*(j) be the real conditional and reference bin masses. Couple the labels by assigning common mass min(p_S(j),p*(j)) on each diagonal entry, then pairing the residual laws by their normalized product when residual mass is positive. Given the labels, sample the uniform real displacement within its fiber and the reference window within its bin. The mismatch probability conditional on S is exactly TV(p_S,p*), optimal by the diagonal mass bound. For an independent sequence of ideal windows, use this construction conditional on the entire joint past at every step, with fresh auxiliary randomness and the prescribed real transition. The ideal conditional marginal is always ν, so its windows are independent of each other. They can depend on their simultaneous real partners.

For a terminal hit bit this costs E|p_S-p*|. For terminal-only comparison one can omit all earlier ideal partners. If arbitrary noncausal coupling is allowed, the optimum drops to |E p_S-p*| by coupling the unconditional labels first and sampling conditional paths. Computing that quantity already requires the terminal probability. For a last-K comparison, condition on the state K transitions before observation and use its K-step hit probability in place of p_S; sample the real suffix conditional on that bit. Independent earlier ideal windows can be sampled separately. This is optimal among couplings requiring the ideal terminal bit to have its prescribed law conditional on that starting state. Increasing K can only reduce this cost by conditional Jensen. Markov sufficiency makes this formula exact, but supplies no decay rate with K. Matching earlier hit bits does not synchronize the marked states. The reachable zero-prefix examples of [Part 109](wall1_terminal_mixing.md) specifically obstruct a history-uniform near-GH restart.

## A local coupling with a first-moment error certificate

At fixed S let M be the inverse image of H in the horizontal space. Couple g uniform on H to U uniform on the continuous torus by adding an independent uniform error in the origin Voronoi cell of M, modulo L. The translated cells tile the torus, so U is Haar on this torus. Write δ for the covering radius of M. The torus distance between kg and kU is at most kδ. This couples two *extensions of the same L*, not two independent lattice shapes.

For a closed physical ball of radius R, horizontal hits coincide. At positive height k ≤ R let t = sqrt(R²-k²). If the layer-hit indicators differ, some point of L+kg has norm in the closed shell [max(0,t-kδ), t+kδ]. Indeed translate a witness by the coupled error or its negative; the partner of a hit on a missed layer lies outside the ball. Consequently a conditional upper bound on window-bit mismatch is zero on horizontal hits and otherwise

    min(1, Σ_k #(M_k ∩ shell_k) / |kH|),     M_k = preimage of kH.

This is the [Part 110](wall1_additive_tour.md) fiber count on a shell. Counting positive k suffices by sign symmetry. It works for predictable thresholds, including full-window own-GH units since the window determinant is det L. For full q-torsion δ = ρ(L)/q. A large subgroup order alone gives no small covering radius in a long unrefreshed direction. Even for a dense grid the bound must be summed over the relevant heights. Grazing layers and boundary atoms are included.

Write c_S for the continuous-extension hit probability. It is exactly the torus volume fraction of the union of the preimages under U ↦ kU of the projected slice balls (one on a horizontal hit). Thus the causal comparison to an independent reference bit costs at most the expected shell bound plus E|c_S-p*|, by the triangle inequality. This isolates a precise missing estimate: concentration of a union volume over the actual penultimate marked states. Even estimating every individual slice volume does not determine the union, because the multiples share U. [Part 111](wall1_hecke_gap.md) similarly couples a full-mark chart to a uniform labeled Hecke neighbor of the *same split base* with failure below 1/q by retaining the neighbor on the chart and resampling on its complement. Neither local coupling erases the base. For quotient observations the bin coupling still applies directly, but the shell estimate above is for the window: displacing a competing vector can change the selected line, the projection and its determinant. A separate shortest-versus-runner-up gap or a direct quotient-bin estimate would be needed.

## Exact two-draw stress test

Take q=3, m=b, two graph columns, r=b−1, and ambient lexicographic minimization over signed shortest vectors. After freezing the first cubic axis the effective residues of each graph column are independent uniform labels in U = {0,1,2}^r. Compare the last full window to an independent fresh first-graph window from the same cube. Both use physical squared threshold 2, inclusive. For the reference the zero residue and the 2r signed unit residues hit, giving (1+2r)/3^r. In the histogram, h:n means n first residues give exactly h hitting second residues out of 3^r.

| Window rank | Conditional hit histogram | Independent restart | Real last window | Optimal causal bit mismatch |
|---:|---|---:|---:|---:|
| 2 | 3:3 | 1 | 1 | 0 |
| 3 | 5:5, 7:4 | 5/9 | 53/81 | 8/81 |
| 4 | 7:7, 9:12, 15:8 | 7/27 | 277/729 | 88/729 |
| 5 | 9:9, 11:40, 17:32 | 1/9 | 355/2187 | 112/2187 |

Here all first shortest vectors have height ±1: centered first residues give a candidate of squared length at most 1+r ≤ 5, horizontal nonzero vectors have squared length at least 9, and height ±2 has the same horizontal residue distances as height ∓1 and greater vertical cost. Higher heights cost at least 9. Projection therefore maps the old horizontal basis to a basis of the quotient (eliminate the last coordinate using the primitive unit-height vector). Full torsion survives. In these examples every conditional rate is at least the reference rate, so even unrestricted coupling cannot improve the displayed mismatch. Threshold mismatch also lower bounds exact-minimum mismatch for this finite comparator.

The Python enumeration below tests the real projected window. For first residue u, the old integer window consists exactly of x with residue x_horizontal − x_last u equal to zero mod 3. The coset with residue z projects to the possible horizontal components of a second height-one vector with fresh residue z. For first shortest vector v of squared norm a, the squared projected length of x is h/a in the code. Subtracting an integer multiple of v preserves its coset and makes the squared parallel component at most a/4. Hence every projected witness of squared length ≤2 has a lift with squared norm ≤2+a/4. Zero projected length counts at fresh height one only. Higher fresh heights cannot hit. These bounds make the finite box exhaustive.

```python
from collections import Counter
from itertools import product

for r in range(1, 5):
    labels = list(product(range(3), repeat=r))
    points = [(sum(t*t for t in x), x)
              for x in product(range(-3, 4), repeat=r+1)
              if sum(t*t for t in x) <= 9]
    histogram = Counter()
    for u in labels:
        def residue(x):
            return tuple((t-x[-1]*s) % 3 for t, s in zip(x, u))
        a, v = min((n, x) for n, x in points if n and not any(residue(x)))
        hits = set()
        for n, x in points:
            if 4*n > 8+a:
                continue
            h = a*n - sum(i*j for i, j in zip(v, x))**2
            z = residue(x)
            if not any(z) and 0 < h <= 2*a:
                hits = set(labels)
                break
            if h <= a:
                hits.add(z)
        histogram[len(hits)] += 1
    print(r+1, sorted(histogram.items()))
```

A separate exact check of the shell argument uses the same initial cube and threshold. Replace continuous cell noise by independent uniform coordinates in {−1/3,0,1/3}; this gives the uniform grid of mesh 1/3 in the torus, with displacement error at most √r/3. Exhausting the 9^r pairs (g,e), the coarse bit tests ∥g∥² ≤ 1 for centered g and the fine bit tests ∥center(3g+3e mod 9)∥² ≤ 9. The mismatch fractions for r = 1,2,3,4 were 2/9, 8/27, 46/243, 544/6561. The corresponding shell bounds were 2/3, 8/9, 2/3, 32/81, obtained by counting integer points with |∥x∥−1| ≤ √r/3 and dividing by 3^r. This checks the local inequality on finite grids; the continuous case follows from the cell coupling proof above.

## Assessment

The last-window shell certificate avoids propagating a radius backward through repeated projections. It could help if typical penultimate states have both small shell charges and a controlled continuous-extension hit rate. For a one-sided lower-tail certificate it suffices to bound E c_S plus the expected shell charge; closeness to a particular independent reference is a stronger demand. Neither expectation has been bounded at the target widths. The small examples disprove exact refresh even for a full mark, but give no dimension-uniform lower bound on the error. Parts [105](wall1_selection_law.md), [106](wall1_chain_law.md) and [112](wall1_void_monotone.md) give no concentration estimate for this average under the concrete reducer. The quotient and a quantitative short-suffix forgetting theorem remain open. There is no improved terminal 99% floor from this comparison.

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

**First-moment shell bound.** The proof holds. Voronoi translates partition the torus, the discrete coset meets the closed shell
in either direction, and the union bound over heights needs no independence.

**Independent enumeration.** The real terminal hit probabilities, by window rank, are:

| Rank | Hit probability |
|---:|---:|
| 2 | 1 |
| 3 | 53/81 |
| 4 | 277/729 |
| 5 | 355/2187 |

In rank 4, 88/729 is the attainable minimum disagreement against the cubic-restart marginal 7/27.

**Open.** Two quantities still need quantitative control under the actual penultimate-state law: the expected shell charge and
E|c_S − p_*|.
