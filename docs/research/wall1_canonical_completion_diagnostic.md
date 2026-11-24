# Canonical completion bottleneck at Part 441

The current size24 leader has rank11, girth4, and an H6 anchor with seven
independent extensions. Its completion has k=24−11−2=11 dependent positions;
the displayed frontier nullity13 includes the two anchor relations.

The actual completion evaluator at q3329,N518 chooses gamma=.75e−6 and
Holder order12 for each D12/D16 family and both free-weight modes. A return
trace of the production evaluator reconstructs its three nonnegative moment
terms. At the selected full-coordinate gamma the rank-deficiency remainder
is much smaller than the power and packing terms. The power term dominates
the packing term, so improving only the rank bound cannot materially improve
this chosen candidate. This does not assert a global optimum over gamma or L.

Run `scripts/wall1_canonical_completion_diagnostic.py`; its output records
intervals for each term and the final cap. These are diagnostic Gaussian
completion caps, not failure probabilities. The free-point/anchor prefactors
must still be included by the complete incidence evaluator. Fine integer
Holder orders and finer gamma candidates are the next bounded experiment.
