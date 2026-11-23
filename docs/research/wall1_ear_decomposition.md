# General connected witnesses and the loss from discarding overlaps

Part 284 controls selected equal-pair-sum families. To cover all connected
supports, use an ear decomposition instead. This note gives a general witness
enumerator, then records that its simplest Gaussian bound is much too large.
It does not improve the certified numerical frontier or complete BKZ.

## Coverage

Jackson and Jordan, *Connected Rigidity Matroids and Unique Realizations of
Graphs*, [Lemma 5.1](https://webspace.maths.qmul.ac.uk/b.jackson/rigidSUBMITTEDMODIFIED.pdf),
states that any initial partial ear decomposition of a connected matroid
extends to the full ground set, and gives the rank increment of each ear.
Apply this to the augmented input matroid on the h distinct positions.

Start with a shortest circuit C_1 of size c. At each subsequent step choose a
circuit meeting both the previous union and its complement, with
inclusion-minimal nonempty outside part. Write t_i for the size of this new
part, and H for the previous union size. The rank increment is t_i-1.
Thus a rank-r support has exactly ell=h-r ears, with

```
t_1=c, sum_i t_i=h, rank(union of first j ears)=sum_(i<=j) t_i-j.
```

Each normalized circuit relation has nonzero coefficients on its support
and coordinate sum zero. Its length d admits at most q^(d-2) coefficient
choices: fix one coefficient to one and solve the sum condition for another.
For a later ear, its overlap of size a is independent, since it is a proper
subset of a circuit. Consequently

```
max(1,c-t) <= a <= H-j
```

after j ears. Labelled position choices are choose(h,c) initially and
choose(h-H,t) choose(H,a) subsequently. The new positions make these ell
relation rows independent. Counting all such witnesses overcounts supports,
which is valid for an upper bound. We do not assume a common pair sum or
restrict to relations with coefficients in {0,1,-1}.

## A universal but weak Fourier bound

Let f_beta(u) be the positive Fourier transform on F_q of the integer
Gaussian exp(-beta z^2), and let S_t=q^(-1) sum_u f_beta(u)^t.
Order the relation rows by ears and columns by their first appearance.
In the first block of columns, the first row has all nonzero coefficients;
later rows supply arbitrary shifts. Holder and invariance of the uniform
field measure under nonzero scaling give an upper bound S_c when summing
over the first row variable. Repeat on the remaining blocks. Therefore

```
q^(-ell) sum_(u in F_q^ell) product_columns f_beta((A^T u)_column)
  <= product_(i=1)^ell S_(t_i).
```

This argument discards the contribution of an old block to later constraints.
It is not an independence assertion about those constraints.

Use the same positive Poisson majorant as the earlier two-relation notes:
T=sqrt(pi/beta), alpha=pi^2/(beta q^2),
delta=2 exp(-pi^2/(4 beta))/(1-exp(-2 pi^2/beta)). Then

```
S_t <= T^t / q * [theta(t alpha)
        + sum_(j=1)^t choose(t,j) delta^j theta((t-j)alpha)],
```

where the last theta(0) term means q, because that term is a finite field
sum. This convention is essential. The other theta terms are bounded by
positive Gaussian series, including their tails.

For each witness the ball count is at most
exp(h beta R^2) * product_i S_(t_i)^N. Divide by q^(mr) for the rank-r
full-incidence activity. The verifier sums the position and coefficient
counts by dynamic programming in (union size, number of ears), with
beta=rN/(2hR^2). **Only the Gaussian factors are raised to N**, not the
number of coefficient choices or labelled witnesses.

## Actual-parameter result and consequence

At draw fourteen, summing the h=14 envelope over ranks gives a family
transfer upper envelope whose base-ten logarithm lies between
521.57250716297 and 521.57250716298. This is far weaker than the existing
two-relation envelope and is not used in the production cumulant bound.
It is not a lower bound on the actual probability or activity.

The complete witness coverage does remove the combinatorial restriction of
the equal-pair-sum approach. But retaining only the sizes of the newly added
blocks loses too much geometry. A useful continuation must preserve overlaps
between three or more relation rows, or otherwise improve the coefficient
sum; merely adding more independently bounded ears is insufficient here.

Validation: `python3 docs/research/scripts/wall1_ear_decomposition.py` checks
2,592 complete decompositions, 6,106 rank increments and 192 exact rational
triangular Holder inequalities, then evaluates the actual-parameter envelope
with interval arithmetic. These finite checks are regressions, not a formal
proof of the general ear theorem or the analytic argument.

The earlier basis-extension divisor was separately rechecked: all 17,792
no-coloop contraction checks in `wall1_unique_four_circuit.py` pass. Its
justification remains that contraction preserves absence of coloops and a
rank-k matroid without coloops has at least k+1 bases (including k=0).
