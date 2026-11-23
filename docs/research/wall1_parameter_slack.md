# Wall 1 parameter slack and the scope of the certificates

**The existing certificates establish no minimum width in the proposed range at which both residuals vanish.** A determinant floor could exclude the small-scale branch by definition. Excluding a wholly old plane is a different implication. Even at a prescribed determinant, a Euclidean lattice can have a primitive plane of arbitrarily small area and arbitrarily small internal spacing. The original finite-chain results exploit more structure than the determinant. Also, the quoted cost of roughly 799 bits belongs to an SVP call in rank 647. [Part 226](wall1_high_codim_sections.md) · [Part 140](wall1_adrs_explicit.md)

## Rank dependence of the Hermite cap

Write the cap as $\lambda_1(L)^2\le c_d\det(L)^{2/d}$, with determinant denoting covolume. The following are **upper bounds on the squared-length coefficient**, rounded upwards. The Blichfeldt column uses $B_d=(2/\pi)\Gamma(d/2+2)^{2/d}$. The next column transports the rank-506 theorem using Mordell’s inequality. Iterating $c_{k+1}\le c_k^{k/(k-1)}$ for the optimal constants telescopes the exponent to $(d-1)/505$. The last column uses the actual Part 77 witness in dimension $d$. [Blichfeldt theorem](../../SigabaNeo/Lib/Lattices/Reduction/Hermite2.lean) · [Mordell step](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledSuffixMordell.lean) · [Part 77 witness integers](wall1_lcz_all_widths.md#all-dimensions)

| Rank $d$ | Blichfeldt | From $56.2142$ by Mordell | Part 77 witness |
|---:|---:|---:|---:|
| 506 | 61.45238 | 56.21420 | 56.37784 |
| 510 | 61.92332 | 58.03717 | 56.79788 |
| 520 | 63.10060 | 62.85743 | 57.84689 |
| 530 | 64.27776 | 68.07804 | 58.89576 |
| 550 | 66.63176 | 79.85606 | 60.99269 |

At rank 506 the Lean sphere/lens certificate gives the best of these three bounds. Its degree-63 expansion and signed shell estimate are dimension-specific. At the four larger ranks the strongest entries here come from Part 77. That note gives an integer $C_d$ bounding $10^9\log(\lambda_1^d/\det L)$, so the coefficient is $\exp(2C_d/(10^9 d))$. These rows use Part 77's existing paper certificates. They do not assert a Lean specialization of the lens witness or optimality of the displayed coefficients. [Rank-506 theorem](../../SigabaNeo/Lib/Lattices/Research/Wall1/HermiteSphereCertificate506.lean) · [Part 77 derivation](wall1_lcz_all_widths.md)

To check the table, run the following Python block from the repository root. It reads the five witness integers directly from the appendix and uses interval arithmetic to check the printed ceilings to the last decimal place. The rank-506 seed is exact.

```python
from math import factorial
from pathlib import Path
from mpmath import iv

iv.dps = 70
appendix = Path("docs/research/wall1_lcz_all_widths.md").read_text().split("## All dimensions")[1]
rows = {
    506: ("61.45238", "56.21420", "56.37784"),
    510: ("61.92332", "58.03717", "56.79788"),
    520: ("63.10060", "62.85743", "57.84689"),
    530: ("64.27776", "68.07804", "58.89576"),
    550: ("66.63176", "79.85606", "60.99269"),
}
certificates = {}
for line in appendix.splitlines():
    fields = line.split()
    if len(fields) == 5 and all(x.isdigit() for x in fields):
        rank, degree, numerator, cap, old_cap = map(int, fields)
        if rank in rows:
            assert rank not in certificates
            certificates[rank] = cap

for d, ceilings in rows.items():
    b = 2 / iv.pi * iv.mpf(factorial(d // 2 + 1)) ** (iv.mpf(2) / d)
    m = iv.mpf("56.2142") ** (iv.mpf(d - 1) / 505)
    p = iv.exp(iv.mpf(2 * certificates[d]) / (10**9 * d))
    for j, (value, ceiling) in enumerate(zip((b, m, p), ceilings)):
        if (d, j) == (506, 1):
            assert ceiling == "56.21420"
            continue
        upper = iv.mpf(ceiling)
        assert upper - iv.mpf("0.00001") < value < upper
```

## What the scale can exclude

Fix $d\ge3$ and any covolume $D>0$. Consider the diagonal lattice with side lengths $\varepsilon,\varepsilon,(D/\varepsilon^2)^{1/(d-2)},\ldots,(D/\varepsilon^2)^{1/(d-2)}$. Its covolume equals $D$ for every $\varepsilon>0$. For $\varepsilon<D^{1/d}$ the first two axes span a saturated plane of area $\varepsilon^2$. Modulo either shortest axis the other has spacing $\varepsilon$. Thus at the same Gaussian-heuristic length $(D/V_d)^{1/d}$, both quantities approach zero. This proves a limitation on deductions from a scalar floor. Realizability of such a lattice along the finite chain is a separate question.

For the original rank-506 window, the reported draw-406 floor is $32.18553$ rounded down. Part 216's split at $34.807$ pays a specified *joint probability* on the upper side. It is a choice of split in a probability majorant. Crossing it on draws 396–406 requires at least 100 previous winners above $1.10$ times their own incoming scale. Part 225's 36-winner statement has a different multiplier ($1.15$), a restricted draw range and an exceptional event. Neither count is a geometric constant of rank 506. Part 226's wholly old residual covers codimensions 133–400 after its controlled charges and has no corresponding upper cutoff on the scale. [Small-scale frequency](wall1_small_g_frequency.md) · [Part 225](wall1_raw_graph_winner_cap.md) · [Wholly old and mixed hits](wall1_z1_last_pieces.md) · [Part 226](wall1_high_codim_sections.md)

## Probability laws and cost

| Certificate | Verified scope in the source | Dependencies when dimensions change |
|---|---|---|
| Haar spacing law | At the specified rank-505 determinant floor and spacing 26, Part 190 encloses $\Pr(E)$ in $(9.97119357603,9.97119357604)\,10^{-63}$. The spacing is internal to the witness plane modulo the shortest line. | Parent rank, covolume and physical spacing enter the reference integral. Transferring that probability to a selected finite lattice requires a separate comparison. [Part 190](wall1_rank2_transverse.md) |
| Part 183 finite discrepancy | The concrete theorem gives $\Pr(F\triangle J)<5.244\,10^{-9}$ for a uniform $400\times512$ matrix, including the last column. | The concrete types, reveal order, last-column identification, scale enclosure and numerical tail bound specialize the general transition argument. [Concrete theorem](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConcreteTerminal506.lean) |
| Parts 192 and 224 | The current Lean source states $\Pr(\mathrm{terminalHit})<\Pr(Z_1)+\Pr(Z_2)+4.652\,10^{-12}$ unconditionally for its finite design. The source now includes the prefix result that Part 224 described as pending. | Prefix flag coverage and sums, raw and dual exits, draw ranges, terminal geometry and the disjoint event definitions all enter the ledger. Its allowances belong to this design. [Current terminal theorem](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledTerminalUnconditional.lean) · [Part 224 ledger](wall1_budget_ledger.md) |
| Parts 47 and 108 | Part 47 conditions on the reducer history. Part 108 describes the conditional displacement of a fresh column on a finite subgroup. | Changing the number of samples or draws changes the available columns and the terminal dimension. The structural statements and their numerical specializations have different scopes. [Part 47](wall1_decoupled.md) · [Part 108](wall1_first_tour.md) |
| Parts 140 and 141 | At rank 647, Part 140 reports $2^{799.23}$ operations with a real-RAM initial sampler, or $2^{799.81}$ with the literal sampler recursion. Part 141 reports $2^{794.98}$ word operations for the recorded structured basis. | A tour uses multiple calls on projected lattices. Applying a bound per call requires the relevant input representation and sampler hypotheses. A $0.29\,\Delta d$ increment does not follow from either theorem. [Part 140](wall1_adrs_explicit.md) · [Part 141](wall1_sampler_wordram.md) |

The rank sweep above concerns universal lattice inequalities. It supplies neither a certified change in recovery cost nor a minimum successful block width. In particular, eliminating a low-scale event and controlling selected wholly old planes are logically distinct even when their numerical estimates share a determinant input.
