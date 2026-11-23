# Girth-eight planes on at most ten positions

The size17 rank8/girth8 term has c=8,t=2 and union size ten. The previous
eleven-position refinement does not apply to this smaller union.

At girth eight, every norm-eight integer row has eight unit entries:
the other affine norm-eight shape has support five and is forbidden.
If two independent such rows span a full-support plane on H positions,
their shared support has16-H positions. Split these positions by whether
the coefficient ratios are +1 or -1. One class has at least ceil((16-H)/2)
positions. Cancelling that class yields a nonzero relation supported on
at most H-ceil((16-H)/2) positions. For H<=10 this is at most seven,
contradicting girth eight. Thus two independent norm-eight rows cannot
occur on these supports.

If a Gauss-reduced first row has squared norm eight, the second has
squared norm at least ten (the affine norm is even). Reduction bounds
their inner product in absolute value by four, giving second squared
height at least10-16/8=8. If the first minimum is at least ten, the usual
reduced-plane heights10,15/2 apply. Use the sum of Nth powers of complete
kernels with heights(8,8) and(10,15/2), minimized with the old bound.
Short-span dimensions zero and one are covered as well. Every previous
cutoff14 tail, periodic layer and coefficient count remains unchanged.

The existing norm-eight partner regression now explicitly checks that
none of its independent pairs on8..10 positions has girth eight. It also
retains the eleven-position and mixed-shape checks. The universal proof
is the cancellation argument above, not an inference from finite samples.
This is not a Lean formalization or a completed BKZ proof.

The same stage also excludes the next norm stratum. A norm-ten row at
girth eight must have ten unit entries: any coefficient of absolute value
two would leave at most six other unit entries and support at most seven.
Larger coefficients give even smaller support. An eight/ten unit pair
on H<=11 positions shares18-H>=7 positions; cancelling its larger sign
class leaves support at most H-ceil((18-H)/2)<=7. A ten/ten pair shares
20-H>=9 positions and is excluded in the same way. Neither pair can
occur at girth eight.

Therefore use the stronger three-case cover as an additional candidate:

* First squared minimum8: second squared height>=10 for H<=10; for
  H=11 retain63/8 from the permitted eight/eight case.
* First squared minimum10: the second is at least12, with height at
  least12-25/10=19/2 by Gauss reduction.
* First squared minimum>=12: use heights12,9.

Sum the Nth powers of these three complete kernels and minimize with
the earlier envelopes. All tails and coefficient counts remain. The
regression enumerates full-support unit eight/ten and ten/ten partners
on10 and11 positions and verifies that every such pair has girth below8.

All2519 new pair checks, the prior norm-eight regressions and2106 cumulant
regressions pass. Transfer through sixteen remains below9.583e-13 (about
8.78527626713e-13). Size17's weighted residual log10 is4.6564591455;
rank8/girth8 is no longer among the five largest strata. Rank8/girth5
now leads at4.2006498077. Through24 remains about1.05489e232. Thus the
targeted obstruction improves, but the remaining2.0505e-12 allocation
and adaptive BKZ bridge are unproved. Logs: `/tmp/wall1_girth_eight_ten.log`
and `/tmp/wall1_girth_eight_ten_cumulants.log`. These ineffective upper
envelopes are not actual failure-probability estimates.
