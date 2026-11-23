# Rare second lines without fixing the first short line

Part 302 located the unique norm-four line on the prescribed first
circuit, which was justified for c=4,t>=4. For the remaining one-norm-four
classes, let that short line have arbitrary support. There are

    K4=3 choose(H,4),
    K6=10 choose(H,6)+1_(c=3)*3 choose(H,3),
    K8=35 choose(H,8)+20 choose(H,5)

possible projective integer lines of the indicated squared norms. The
girth conditions exclude all other affine shapes at these norms.

An independent norm-four/norm-six pair fixes the two-dimensional code;
so does an independent norm-four/norm-eight pair. Each prescribed proper
circuit support determines at most one projective direction in a
full-support code: vanishing at an omitted coordinate gives a nonzero
linear equation. Therefore K4*K6 and K4*K8 bound the corresponding
normalized coefficient-pair counts. Cap them by the existing one-short-line
coefficient bound.

Split the exactly-one-norm-four class into independent norm six, norm
eight but no norm six, and neither. Their second squared minima are at
least 6, 8, and 10, hence perpendicular heights at least 5, 7, and 9.
Take the maximum with any previously justified height for the same
anchor. Retain cutoff 40 and the same long-vector and positive periodic
terms in every Gaussian factor. The last class keeps the full previous
one-short-line count; the first two get the rare-pair weights. The
positive sum is an upper cover even with overcounted witnesses.

Use this refined one-short-line contribution in the generic anchor and
also in the specialized six- and seven-point substitutions. The old
fixed-first-line refinement remains available where stronger. No
two-norm-four or no-norm-four class is omitted.

The exact regression adds 4,590 arbitrary short-line-pair proper-support
uniqueness checks to the earlier line-shape and fixed-first-support tests.
All full cumulant regressions pass. The full size-fifteen residual weighted
log10 decreases from -5.17651 to -7.04224, about 9.07e-8. The girth-four
rank-seven term is now about 10^(-10.0334), while the girth-three rank-seven
term, about 10^(-7.05024), dominates. The residual budget, larger sizes,
selected histories and complete BKZ proof remain unresolved. This is not
a Lean formalization.
