# Two actual winners and the terminal physical floor

The full competitor test leaves exactly one winner branch per input. Its remaining first-moment loss is measurable: it is the number of *additional* short primitive quotient lines on a failure with no horizontal witness. In a fully enumerated width-three experiment the conditional bound was below one on every history, yet its exact history average was 0.4608 against a failure probability of 0.416768. At widths four and six the same count can exceed one even with both selectors exact. The width-506 obstacle is an expectation over the old marked lattice.

## Conditional certificate

Use the framed, signed ambient lexicographic kernel of [Part 119](wall1_experiments.md). Condition on the entire prefix through time \(T-2\), with retained lattice \(A\) and finite mark \(H\). For a representative of \(U\in H\) form \(W_-=(A,0)+\mathbb Z(U,1)\). Write \(p\) for projection off its signed winner \(e\), \(u=|e|\), and \(L=pW_-\). Its mark \(K\) is the image of the inherited marked generators under projection modulo \(L\). For \(V\in K\) let \(W=(L,0)+\mathbb Z(V,1)\); write \(f,s=|f|,Q=\pi_f W\) for the final winner, length and output. The physical test is strict, \(\lambda_1(Q)<R\), with \(R^2=1+3d/2-\sqrt{d/22}\), \(d=b-1\).

For a candidate signed winner \(a\) in a framed lattice \(M\), give its branch weight zero if any nonzero \(z\in M\) in the closed ball of radius \(|a|\) precedes \(a\) in the order \((|z|^2,z_{\rm ambient})\); otherwise give it weight one. Call this weight \(J_M(a)\). Multiplying \(J_{W_-}(e)J_W(f)\) by \(1/(|H||K_e|)\) and summing over both input classes and candidate winners gives the exact inverse-branch measure. The second frame and mark in this expression depend on the first branch. Each draw has exactly one winning signed primitive vector. The exclusions are joint tests on that input, including ties. Restricting to certified competitors only enlarges each branch weight; any upper sum must then include *all* surviving candidate branches. This is the finite input weight corresponding to the branch domain in [Part 127](wall1_adjacent_methods.md).

Count saturated planes \(P\subset W\) containing \(f\) with \(\det P<sR\). The full inverse image of each primitive unoriented line in \(Q\) is precisely one such plane when its generator is shorter than \(R\): extending \(f\) to a basis of the plane multiplies the projected length by \(s\). Write \(h\) for existence of a counted horizontal plane and \(N\) for the count of all short primitive lines. On the inverse-branch measure,
\[
 p(A,H)=E[\mathbf1_{N>0}],\qquad
 B(A,H)=E[h+(1-h)N],\qquad
 B-p=E[(1-h)(N-1)_+].
\]
Thus \(\min(1,B)\) is a conditional probability bound; averaging must use the prefix law. Taking presence instead of multiplicity on each draw gives equality. Positive-height planes are counted even when their winner is horizontal. Once a horizontal hit is paid, the residual charge vanishes. These are the two disjoint charges of [Part 120](wall1_plane_count.md).

**Where the triple lives.** For \(P\subset L\), the full lift \(p^{-1}P\cap W_-\) is saturated, contains \(e\) and every lift of \(f\), and has covolume \(u\det P<usR\). It contains the nested rank-two lift of the final winner line. This includes triples with nonzero height in \(W_-\). For a final plane of positive height there is no such preimage of the whole plane in \(W_-\): the map has image \(L\). One can either apply Part 120 on the second draw or form the rank-\((b+1)\) extension of \(W_-\) by \((\widehat V,1)\), where \(\widehat V\) is any real lift of a representative of \(V\) under orthogonal projection along \(e\). Extending that projection by the identity on last height gives image \(W\) and lattice kernel \(\mathbb Ze\). There the full lift is again saturated of rank three and has covolume \(u\det P\), by the same basis argument. Its intersection with \(W_-\) is only rank two, the lift of the primitive horizontal kernel of \(P\). The last-height fiber \(jV=y+L\) has weight \(1/|jK|\) if nonempty, followed by uniform conditional weight \(1/|K[j]|\). Both the membership of \(f\) and its void test must be evaluated on that fiber.

## Exact finite computations

The code below implements the incident-flag count in quotient coordinates, where each primitive sign pair is a unique flag for the two given winners. It evaluates the truth independently by exact SVP. A dual coordinate bound makes the count exhaustive: in a basis with Gram matrix \(G\), every vector of norm below \(R\) has coefficient \(|z_i|\le R\sqrt{(G^{-1})_{ii}}\). All squared norms are rational and the floor comparison uses a real algebraic number. LLL only changes the basis. For horizontal existence we project the old lattice off the winning horizontal vector and test its minimum. The conditional averages enumerate the row space of each actual mark, including deficient ones, and normalize separately on every child.

**All histories.** Take \(n=b=3,d=2,q=5\) and start at \(5I_2\). Width tracks the number of appends here; the next experiment uses the Part 123 offset \(b=n-6\). Enumerate all 25 first residue pairs and every class of both subsequent marks. The following numerators have common denominator 625, and the multiplicities sum to 25. The horizontal hit is zero throughout.

| First histories | Conditional bound × 625 | True conditional failures × 625 |
|---:|---:|---:|
|1|48|48|
|4|104|104|
|4|204|180|
|12|356|308|
|2|412|404|
|2|412|412|

The exact averages are \(7200/15625\) and \(6512/15625\); the excess is \(688/15625\). Even in this small case, a bound below one on every prefix says little about a one-percent budget.

**Part 123 width convention.** For \(b=4,n=10,d=3\) use prefix seeds 0 through 7 at each modulus. These are sampled prefixes, followed by *exhaustive*, exactly weighted suffixes. Each table cell gives the exact bound on the indicated prefix. The conditional failure probability equals one in all sixteen cases.

| q | Seed 0 | Seed 1 | Seed 2 | Seed 3 | Seed 4 | Seed 5 | Seed 6 | Seed 7 | Mean |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 8 | 8 | 8 | 8 | 5 | 8 | 7/2 | 99/16 |
| 3 | 1252/81 | 916/81 | 5924/729 | 6046/729 | 218/27 | 403/27 | 200/27 | 32/9 | 2083/216 |

The mean horizontal contributions were respectively \(79/128\) and \(242/729\). On these same suffixes I also replaced the final horizontal selector by the following cheaper exclusion. Compute the signed old minimum \(x\) in \(L\), retain its incident bad-plane test, then compare \((x,0)\) against height \(\pm1\) only, with the same tie rule. In coefficients \(a=V\), enumerate integers \(z_i\) with \(|z_i+a_i|\le\sqrt{(|x|^2-1)(G^{-1})_{ii}}\) if \(|x|\ge1\); check the norm and both signs at every resulting point. This replacement gives the same horizontal contribution on every tested prefix. Dropping the bad-plane test but retaining the exact horizontal selector likewise gives the same charge on all sixteen. The positive-height residual used its exact selector in these comparisons. Here the measured excess comes entirely from multiplicity on residual branches. In the width-three, modulus-five census the old-plane test alone gave zero on every branch. Keeping the exact horizontal winner while forgetting its required bad-plane incidence charged an extra 16/625 unconditionally.

**Larger moduli.** Exact enumeration of short lines and SVP on one sampled suffix per prefix gives the following totals. Here the mean score estimates the *unclipped* history average by iterated expectation. The fraction of realized scores below one equals the observed success fraction; it cannot estimate the fraction of prefixes with conditional bound below one. Seeds start at zero in each row. These are new trajectories following the [Part 123](wall1_experiments2.md) parameter convention.

| n | b | q | passes | horizontal hits | residual count | true failures | mean score |
|---:|---:|---:|---:|---:|---:|---:|---:|
|10|4|257|80|1|253|76|254/80|
|10|4|3329|40|0|53|27|53/40|
|12|6|3329|40|1|16|16|17/40|
|14|8|3329|40|0|3|3|3/40|
|16|10|3329|40|0|0|0|0|

The observed excess fell from 26 extra lines over 40 passes at width four to one at width six and zero at widths eight and ten. Forty sampled suffixes with zero failures still give a one-sided 95% binomial endpoint above 7% under independent sampling. The result at width ten supports computing the actual incident moment at larger widths, but does not resolve a one-percent tail.

## What the next averaging step would have to prove

On the twice-horizontal subbranch a saturated triple in \(A\) is already present before either draw. If both winners are horizontal, their identities are determined by the old signed minimum and the signed minimum in its appropriate projected window. A fresh input can defeat the prescribed winners; it cannot supply a density factor for the existence of that old triple. On the subbranch where the lifted triple has preceding height \(i>0\), one needs a saturated old plane kernel \(S\subset A\) and a disk count transverse to it. Its covolume is \(\det S\sqrt{i^2+|\pi_{S^\perp}y|^2}\), with \(y\in iU+A\) modulo \(S\). The disk, height congruence, flag incidence and both competitor exclusions are evaluated together. For a positive-height final plane its horizontal kernel also pulls back to an incident plane in \(W_-\). Its transverse disk in the final window depends on that particular projected kernel. Thus fresh classes average some disk placements and voids. They leave a weighted distribution of old sublattices and marked fibers. Going back another step lifts an inherited triple to an incident rank-four subgroup. No closed one-step estimate for that distribution follows from the two uniform draws. This is the unresolved old-lattice statistic in [Part 126](wall1_band_moments.md).

A state-uniform estimate from determinant and mark would already fail on abstract framed states. In rank 505 take zero mark and a rectangular lattice with three orthogonal sides of length 1/2 and all other sides sufficiently long. Each append is a unit orthogonal axis. The two winners are old half-unit axes, and the third survives, so the physical horizontal hit has probability one. An equal-determinant cube can have side larger than the physical cutoff by increasing the long sides. From that cube both appended units win and the terminal minimum is the cube side. This example concerns the marked-state kernel; a graph-ensemble estimate must control the mass of the relevant histories.

**Width 506.** In the reduced law \(T=407\); the outer expectation is over the uniform restart graph and the first 405 displacements. Rounding a lift along the final winner gives \(\lambda_1(Q)\ge\alpha s\), \(\alpha=\sqrt3/2\). Hence \(27.45375<R<27.45377\) and failure requires \(s<31.701\) and plane area below 870.309. On a horizontal terminal witness \(f\in L\), so \(s\ge\alpha u\) by the preceding projection. In particular the *branch-specific* triple cap \(usR\) is strictly below \(R^3/\alpha^3<31860\). This last gate uses the final winner's membership in \(L\). For a positive-height plane with horizontal kernel generated by \(x\), one has \(j\alpha u\le j|x|<sR\); one cannot use \(s\ge\alpha u\) for a nonhorizontal winner. None of these physical covolumes gives a probability without the surviving incidence count.

For a numerical sensitivity calculation, grant a terminal conditional primitive-line first moment at most \(M\) times the Haar value at its determinant, and a terminal GH radius at least 28.8095. Then \(E B\le E N < M\,1.342\cdot10^{-11}\) by the primitive line formula \((R/\mathrm{GH})^{505}/(2\zeta(505))\). The decimal inequality follows by raising the rational upper ratio \(27.45377/28.8095\) to the integer power and using \(\zeta(505)>1\). Even \(M=7\cdot10^8\) would fit the combined budget on these assumptions. The GH floor is available on the original pass; a determinant bound alone imposes no such bound on \(M\). With the more optimistic stipulated GH floor 35.18 and \(M=1\) the same rational computation gives less than \(2.059\cdot10^{-55}\). This is a reference-law calculation only. [Determinant estimates](wall1_idea_drift.md)

Even granting perfect competitor exclusions and removing every multiplicity, the resulting quantity at 506 is precisely the unknown history-averaged hit probability. With the established estimates the numerical probability upper bound from this calculation is still one. It must reach 0.00977696 on the reduced law to meet the one-percent original budget after coupling. The large loss previously measured for unrestricted triples at a uniform *relative-GH* cap does not quantify the loss here. The test isolates an observable worth measuring; a proof route needs a bound on its old incident flags jointly with the exclusion probabilities. [Wall 1](../PROOF_GAP.md)

## Reproduction

Run the following as a Python script from the repository root in the Sage environment of Part 123. Each returned row includes the per-prefix or realized horizontal charge, residual count and truth in that order. The height-one diagnostic is optional. The window reduction before completion is unimodular. Using the original Part 119 completion gives the same ambient winners.

```python
from pathlib import Path
from itertools import product
from math import gcd
from sage.all import AA

note = Path("docs/research/wall1_experiments.md").read_text()
exec(note.split("```python\n", 1)[1].split("def trial(", 1)[0])

def projected_basis(B, c):
    v = c*B
    _, H = matrix(c).transpose().hermite_form(
        transformation=True, include_zero_rows=True)
    rest = H.inverse().transpose()[1:]*B
    return rest - rest*matrix(v).transpose()*matrix(v)/(v*v), H

def append(B, C, q, residue):
    d = B.nrows()
    a = vector(QQ, residue)/q
    W = B.stack(matrix([a*B])).augment(matrix(QQ, d+1, 1, [0]*d+[1]))
    _, U = (W.denominator()*W).change_ring(ZZ).LLL(transformation=True)
    reduced = U*W
    c, _, _, _ = shortest(reduced)
    Q, H = projected_basis(reduced, c)
    K = C.augment(zero_matrix(ZZ, d, 1))*U.inverse()*H.transpose()
    return Q, K[:, 1:].change_ring(ZZ)%q, c*U

def support(C, q):
    rows = C.change_ring(GF(q)).row_space().basis_matrix()
    return [vector(ZZ, vector(GF(q), t)*rows)
            for t in product(range(q), repeat=rows.nrows())]

def lines(Q, R2):
    den = Q.denominator()
    A = (den*Q).change_ring(ZZ).LLL().change_ring(QQ)/den
    inverse = (A*A.transpose()).inverse()
    limits = [int((R2*x).sqrt().floor()) for x in inverse.diagonal()]
    count = 0
    for z in product(*(range(-k, k+1) for k in limits)):
        if z > tuple(-i for i in z) and gcd(*z) == 1:
            v = vector(ZZ, z)*A
            count += int(v*v < R2)
    truth = int(shortest(Q)[1] < R2)
    assert truth == bool(count)
    return count, truth

def survives_unit_height(L, V, q, x):
    t2 = x*x
    if t2 < 1:
        return 1
    a = vector(QQ, V)/q
    inverse = (L*L.transpose()).inverse()
    ranges = []
    for ai, di in zip(a, inverse.diagonal()):
        radius = AA((t2-1)*di).sqrt()
        ranges.append(range(int((-ai-radius).ceil()), int((-ai+radius).floor())+1))
    for z in product(*ranges):
        y = (a+vector(ZZ, z))*L
        first = min(tuple(y)+(1,), tuple(-y)+(-1,))
        if (y*y+1, first) < (t2, tuple(x)+(0,)):
            return 0
    return 1

def measure(args):
    d, q, seed, mode = args
    rng = Random(seed)
    R2 = 1+QQ(3)*d/2-AA(QQ(d)/22).sqrt()
    B, C = q*identity_matrix(QQ, d), identity_matrix(ZZ, d)
    def draw(mark):
        return vector(ZZ, [rng.randrange(q) for _ in range(d)])*mark % q
    if mode == 'census':
        B, C, _ = append(B, C, q, divmod(seed, q))
    else:
        for _ in range(d+5):
            B, C, _ = append(B, C, q, draw(C))
    def inputs(mark):
        return [draw(mark)] if mode == 'sample' else support(mark, q)
    totals = [QQ(0)]*5
    us = inputs(C)
    for U in us:
        L, K, _ = append(B, C, q, U)
        c0 = shortest(L)[0]
        x = c0*L
        old_bad = int(shortest(projected_basis(L, c0)[0])[1] < R2)
        vs = inputs(K)
        for V in vs:
            Q, _, c = append(L, K, q, V)
            count, truth = lines(Q, R2)
            horiz = int(c[-1] == 0)
            hit = horiz*old_bad
            assert not horiz or c[:-1]*L == x
            assert hit <= truth
            partial = (old_bad*survives_unit_height(L, V, q, x)
                       if mode != 'sample' else hit)
            assert hit <= partial
            row = (hit, (1-hit)*count, truth, partial, horiz)
            for i, value in enumerate(row):
                totals[i] += QQ(value)/(len(us)*len(vs))
    return args, tuple(map(str, totals))

if __name__ == '__main__':
    jobs = [(2, 5, j, 'census') for j in range(25)]
    jobs += [(3, q, j, 'suffix') for q in (2, 3) for j in range(8)]
    jobs += [(3, 257, j, 'sample') for j in range(80)]
    jobs += [(d, 3329, j, 'sample') for d in (3, 5, 7, 9) for j in range(40)]
    with Pool(8) as pool:
        for result in pool.imap_unordered(measure, jobs):
            print(result, flush=True)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

**Valid conditional upper bound.** The test bounds the failure probability from above. Its excess over the true failure
indicator is exactly (1 − h)(N − 1)_+. Positive-height planes need the last appended direction, with the lift checked on the same
fiber.

**Reproduction.**

* The replay produced all 281 records.
* An independent census of all 15,625 histories gave bound 7200/15625 against failure 6512/15625. The maximum prefix bound was
  412/625.
* At b = 4, n = 10, all 16 prefixes have failure 1. One has bound exactly 1 and the other 15 have bound > 1.

**Scope.**

* The width-6 seed-6 score of 2 is a realized sample. It does not establish B > 1 on that prefix.
* 0.00977696 is sufficient under the coupling allowance, not necessary.
