# Sharp MGF and marked-transition checkpoint

The full production BKZ theorem remains unproved. This checkpoint improves
an auxiliary probability remainder and checks finite transition mechanics.

At the unchanged void threshold rho=.280, a sharp two-moment correlation
MGF bound combined with the first moments of the initial eight terms gives
a compensator remainder below8.850e-14 (lambda=3.1724). Outward interval
arithmetic verifies the numerical inequality. The sufficient later-history
exit allowance is5.0075e-12; after the seed, the normalized additive drift
allowance is3.0370491e-12. The actual selected-history exit/drift bound has
not been proved. See [the derivation](wall1_sharp_correlation_mgf.md).

The chronological height checker now uses a determinant-dependent radius
in its finite q=5, width4 model, with interval-certified candidate membership.
The repeated marked-transition checker verifies exact probability and
determinant identities across three transitions and a forced rank-drop case.
Neither finite check establishes the high-dimensional selected-history law.

The axial lens calculation bounds the quadrature error of continuum
transverse volumes by6.4% in its stated central regime. Actual transverse
lattice-slice counts and the selected radial distribution remain uncontrolled.

The accompanying JSON records six reproducible commands, their outputs,
source hashes and log hashes. No Lean source changed and no new Lean theorem
or build is asserted by this checkpoint.
