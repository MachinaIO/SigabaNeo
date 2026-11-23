# Norm-six splitting inside the girth-four no-norm-four class

Apply Part 300's coefficient stratification inside the no-norm-four term
of each girth-four two-circuit anchor. A norm-six row still has balanced
six-support: the alternative support-three shape contradicts girth four.
The first four-support circuit cannot itself be a norm-six row.

Suppose two independent balanced norm-six rows span the code, with full
union H. Their overlap is 12-H, and their exclusive positions number
2H-12. The proof in Part 300 excludes H<=6 by producing a mixed direction
of weight at most three. For H>=9 every mixed direction has weight at
least six, so the code cannot contain the prescribed four-circuit.

If H=8, a four-support mixed direction must cancel all four overlapping
positions. Its four exclusive coefficients are +/-1, and their sum is
zero because both original rows are balanced. This is a norm-four line,
contradicting the class restriction. Therefore only H=7 remains.

Let K=10 choose(H,6), Q=q^(t+a) with c=4. Fixing the first circuit
(at most q^2 choices) and one norm-six line determines the code and its
second prescribed circuit. Thus the one-line coefficient count is at
most K*q^2, capped by Q; it is zero when t>=6 by the external-support
bound. Two independent lines give at most K^2 coefficient pairs,
capped by Q, and occur only at H=7.

Use the same three theta bounds as Part 300: (8,6) for no norm-six line,
(6,13/2) for exactly one line, and (6,9/2) for two independent lines.
Retain cutoff 14 in the first class and cutoff 36 in the latter classes,
all long-vector tails, and all positive periodic terms. The new positive
sum bounds only the no-norm-four contribution; the one- and two-norm-four
contributions remain separately included. Every specialized six- and
seven-point substitution also retains the refined no-norm-four term.

The exact classification regression now also finds 72 girth-four cases
without a norm-four line, all on seven positions, across the two tested
fields. The proof above applies to q=3329 without a finite-enumeration
assumption. This is a paper refinement, not a Lean theorem or a completed
BKZ proof.

The full size-fifteen residual weighted log10 moves from approximately
1.40954 to 1.40187. This small improvement shows that refining the
no-norm-four class alone does not resolve the current obstruction.
Rank-seven girth-four still dominates. The full residual target and
later selected-history estimates remain open.
