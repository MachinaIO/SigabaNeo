# Isolating the four-circuit obstruction at draw 13

This paper refinement classifies the remaining ten-input term in Part 258.
The rank-three and rank-eight strata are bounded, as are the rank-four through
rank-seven supports with no four-element input circuit. What remains is a
connected ten-input support of rank 4--7 containing a four-element circuit.
The later selected-projection problem remains unchanged. This is not a complete
failure-probability bound.

## Restricting the circuit-anchor sum

Part 256 proves the bound E_(h,r) by choosing a circuit inside every dependent
subset U of an h-input support T, extending its span within U and then within T.
If T has no circuit of size four, neither does any subset U. The same proof is
therefore valid after deleting all terms with anchor size c=4 from E_(h,r).
Every dependent U still has at least one circuit, and all available circuit
choices have sizes different from four. Thus no witness needed for that restricted
stratum is lost.

This restriction is valid only on the no-four-circuit class. It does not justify
removing the c=4 terms for arbitrary supports, even if those supports also contain
other circuits. For example, a dependent subset may itself be a four-circuit.

Let E^not4_(h,r) denote the sum with c=4 omitted. At draw 13, use h=10 and the
exact same radius, Gaussian count bounds and candidate lower count as before.
For the adjusted square H of Part 258, the normalized coefficient of the final
ten-input product satisfies

\[
 \frac{c_{10}}{\rho H(0;\mu)^2}\le\frac1{\rho\mu^{10}}.
\]

The two additional charges are therefore bounded by

\[
 \frac{E_{10,3}+E_{10,8}}{\rho\mu^{10}}<2.197\cdot10^{-18},
\]
\[
 \frac{\sum_{r=4}^{7}E^{\mathrm{not4}}_{10,r}}{\rho\mu^{10}}
                                      <3.981\cdot10^{-14}.       \tag{1}
\]

These sums bound all supports in the indicated rank classes, hence also their
connected subfamilies. Rank two and rank nine have already been handled as
rank-two components and circuits, respectively. A connected support of rank ten
is impossible; an independent support has zero centered distinct-input moment.

## Remaining signed term

Let Delta_4 be the sum of E product_y(J_y-rho_y) over ordered ten-input supports
that are connected, have rank 4--7, and contain a four-element input circuit.
Part 258 and (1) give only

\[
 \Pr(b_{13}>0.280)\le2.432\cdot10^{-12}
                  +\frac{|\Delta_4|}{14400\cdot0.280\,H(0;\mu)^2}.     \tag{2}
\]

The last term is not bounded. The c=4 anchor contribution alone in the old
rank-extension majorant, summed over ranks 4--7 and normalized by rho*mu^10,
exceeds 752. This confirms that its current arbitrary affine-span completion
count is insufficient. It does not imply that the actual signed correction,
or any failure probability, is large.

In particular, identifying the four-circuit stratum does not let us assume that
its other relations are independent. A useful next estimate must retain those
additional constraints, or the cancellations they impose, alongside the
four-circuit. The statement (2) still contains that full obligation and does
not discharge any draw-14--404 selected-history requirement.

## Exact verification

Run `python3 docs/research/scripts/wall1_affine_four_circuit_stratum.py`.
The finite fixture has ten inputs (t,t^2,t^3) over F_11. All 210 four-element
subsets have augmented rank four, while the whole set has rank four. Thus the
fixture has five-element circuits and no four-element circuit. For two choices
of nonuniform output fibers the verifier enumerates all 14641 affine row maps,
computes every subset joint probability, and checks the restricted weighted
rank-extension envelope exactly. It then verifies (1), the constants in (2),
and the >752 majorant limitation using outward interval arithmetic at the
actual draw-13 parameters. These are finite checks of a paper deduction; no
Lean formalization or selected-process simulation is claimed.
