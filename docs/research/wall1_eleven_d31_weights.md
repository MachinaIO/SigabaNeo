# Weighted norm-four/eight kernel on eleven positions

The explicit eleven-position split diagnostic identifies the one-four
family as the dominant residual, rather than the no-four family treated
in the preceding norm-eight and norm-ten refinements. In the one-four
family the norm-eight witness is unit on seven new coordinates and one
old coordinate j, and the norm-four row is unit on all four old coordinates.
Their Gram determinant is31.

Give coordinate j weight55/72, the other three old coordinates weight11/12,
and the seven new coordinates weight77/72. Their sum is11, so the scalar
beta and Gaussian Markov exponential remain unchanged. In metric diag(1/w),
the squared Gram--Schmidt lengths are

    252/55 and576/77.

The signed inner product is +/-72/55. The weighted coordinate determinant
product is

    prod(w)*(252/55)*(576/77)
      =1941871315289213/60183678025728 >31.

The script `scripts/wall1_eleven_d31_weights.py` verifies these rational
identities for all420 balanced first-row/second-row witnesses before
prescribed-overlap filtering. Therefore the result covers both existing
105-plane strata (overlaps1 and3), irrespective of their affine sign pattern.
Each pair has a unit minor from an old coordinate and a unit new coordinate,
so it generates the saturated integer plane.

Poisson summation changes the prefactor by

    ((55/72)*(11/12)^3*(77/72)^7)^(-1/2).

The short-plane theta product uses the displayed weighted squared lengths.
Since max(w)=77/72, the weighted form dominates72/77 times the unweighted
form. Replace alpha by72*alpha/77 in the complete cutoff-40 tail, and a by
72*a/77 in the periodic-coordinate error. The unweighted short-plane lift
continues to apply to the original norm-below40 set. The weighted tail
domination handles its complement; no vector or periodic layer is removed.

The implementation only changes the determinant31 kernels in the complete
eleven-position norm-eight/norm-ten split and takes their minimum with the
previous kernels. The determinant39 norm-ten cover, height-eleven remainder,
counts and all other families remain. This is a local computer-assisted
estimate, not a completed size17 or adaptive BKZ proof, and is not yet
formalized in Lean.
