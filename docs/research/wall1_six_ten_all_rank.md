# D32 crossing covers through rank twenty-one

This note extends the complete fundamental-circuit cover to every r with
9<=r<=h-3 and h<=24, hence r<=21. It retains all crossing sizes
2<=t<=r-7<=14. The baseline implementation uses only the always-valid
third-height bound t when t>=6; the earlier t<=5 refinements are retained.
No production file is changed.

## Coverage and the safe third-height bound

Choose an independent eight-position basis B of the connected D32 anchor,
and extend it to a basis of the full connected rank-r component. The
fundamental-circuit graph has a nonbasis vertex whose circuit meets both
B and the new basis. The circuit has t new positions (including that
vertex), with 2<=t<=r-7, and a nonempty old part supported on B. Girth six
requires a+t>=6. Normalizing one new coefficient and imposing affine
balance gives at most

    C_t=sum_(a=max(1,6-t))^8 binomial(8,a)*q^(t+a-2)

coefficient charts. In particular a=0 is never included, even for t>=6:
the circuit must connect the old anchor to the new basis.

The old two-dimensional real relation plane has zero new coordinates.
In the lifted three-dimensional relation plane, all new-coordinate
restrictions are proportional to the crossing restriction, which is
nonzero at each of the t new positions. Every integer row independent of
the old plane consequently has a nonzero integer at every new position.
Orthogonal projection off the old plane leaves those coordinates unchanged.
Therefore its squared third projected height is at least t, independently
of any claim about the old projected part. This proves the baseline height
for all t. At t<=5 the earlier girth argument additionally supplies 3/4
from the old projected part, together with the complete counted norm-six
split and no-six complement. No short-line count is required for t>=6.

The full joint kernel J_t uses H=10+t<=24 positions, rank=7+t, and cutoff24.
The lifting inequalities 32*24^4<q^2 and H*24^2<q^2 still hold. The Gaussian
normalization, long-vector theta tail and periodic error use their actual
H and rank. Put W_t=C_t*J_t(t) for t>=6; for t<=5 retain the complete
minimum from the existing counted split.

## Complete formula

There are extra=r-7-t independent points after the anchor and crossing.
Choosing them and bounding the remaining affine-slice completions yields

    D32(h,r)=binomial(h,10)*163800*M_(r-1)^(h-r-3)
      *sum_(t=2)^(r-7) binomial(h-10,t)
         *binomial(h-10-t,r-7-t)*mu^(r-7-t)*W_t.

Each summand exposes exactly r+3 positions. No independence of overlapping
witnesses and no multiplicity division is assumed. As before, the complete
candidate is no32-residual + D27-addback + D32(h,r), minimized against the
currently selected complete stratum envelope. The script captures the
actual current outer evaluator with the private AST return-capture helper,
then compares all strata and also isolates the additional scope r>=13.

## Stronger old-projection argument (independent audit)

The mixed circuit can in fact retain the old contribution 3/4 even at
t>=6. The following argument was independently checked by the adaptive-
bridge worker; it is distinct from the baseline computation above.

Let a,b be the saturated old anchor generators, w the normalized modular
crossing, and v a cutoff-short integer third row in its relation code.
Let L be the saturation of Za+Zb+Zv in its real span. The raw rank-three
covolume is at most sqrt(32)*||v||<=sqrt(32)*24<q. Since an integer lattice
has covolume at least one, the saturation index [L:Za+Zb+Zv] is below q, hence prime
to q=3329. For each x in L, multiplication by this index puts x in
Za+Zb+Zv; inversion of the index modulo q proves L mod q is contained
in the prescribed modular relation code. Also covol(L)<q. If every three-row minor of an integer basis of L
were divisible by q, at least one nonzero minor would have magnitude at
least q, and Cauchy--Binet would give covol(L)>=q. Thus L has modular
rank three. Its reduction is exactly the prescribed three-dimensional
relation code spanned by a,b,w.

The subgroup Za+Zb is primitive in L, so extend a,b to an integer basis
with a third vector z. Its reduction lies outside the old modular plane,
and can be written zbar=lambda*w+c, with lambda nonzero and c old. If the
old orthogonal projection of z vanished, saturation of the old anchor
would imply z_old in Za+Zb. Reducing modulo q then puts lambda*w_old in
the old relation code. This is impossible: w_old is a nonzero vector
supported on the independent anchor basis B. Thus the old projected part
is nonzero, and the known projected integer minimum gives at least 3/4.
The new part still contributes at least t. The same conclusion applies to
the primitive generator of the rank-one quotient used by the theta bound.

This stronger route depends explicitly on the mixed-circuit old support
and the short-lattice saturation-index argument. Merely citing girth six
would not prove it for t>=6.

Reproduce the baseline with
`python3 docs/research/scripts/wall1_six_ten_all_rank.py`.
The log is `/tmp/wall1_six_ten_all_rank.log`.


All geometric bounds are applied first to valid mixed-circuit charts:
the old coefficient vector is nonzero and supported on the independent
basis B, and all prescribed new coefficients are nonzero. Only after this
uniform kernel estimate is established is the number of such charts
relaxed upward to C_t. Invalid zero-old or vanished-new coefficient arrays
included by the q-power upper count are not asserted to satisfy the
projected-height bound; multiplying a valid-chart uniform bound by an upper
count does not require such an assertion.


## Current numerical effect

The baseline all-rank cover was compared with the current full selected
strata, including the already integrated rank-ten and rank-eleven/twelve
D32 covers. The largest remaining higher-rank stratum improvement has
log10 ratio approximately -2.33297626648e-8 (rank thirteen). The all-strata
log10 improvements are approximately -1.45813039583e-48 at size19 and
-1.65668153967e-19 at size24. These are negligible; the D32 family is no
longer the controlling global obstruction in those ranks.

The script's optional `envelopes(s,full_projection_bonus=True)` also
minimizes with the proved t+3/4 bound at every t>=6. The reported global
numbers above use the baseline t bound, not this strengthened option.
Both modes return `(bounds_by_(h,r), terms_by_(h,r,t))`. This is a complete
coverage generalization, not a substantive numerical closure of the
remaining global gap.

## Production integration and validation (2026-11-24)

The production triangular-component bound now uses the dedicated rank11/12
cover and this baseline all-rank cover for r>=13 with r<=h-3. Earlier rank8/9/10
covers remain in place. Each candidate includes the no-D32 residual and D27
addback before minimization. Frontier reconstruction uses the same complete
candidates. The optional full-projection bonus is not enabled in production.

Both full scripts exited successfully:

- `/tmp/wall1_all_rank_cumulants.log`: 240 exact Poisson/cumulant checks and
  1866 connected-support checks passed. The outward interval upper endpoint
  through size17 is below 6.144e-13. Through size24 the envelope is about
  6.57352000301834e212; it is ineffective, not an actual failure probability.
- `/tmp/wall1_all_rank_frontier.log`: return-capture checks and all selected
  complete-cover/remainder interval comparisons passed.

Sizes18–24 and the adaptive selected-history estimate remain open. These are
paper and computational results, with no new Lean formalization claimed.
The independent radial-smoothing attempt and its precise limitations are
recorded in `wall1_smoothed_void_potential.md`.
