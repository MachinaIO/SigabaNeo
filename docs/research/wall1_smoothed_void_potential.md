# Radially smoothed void powers: a shell-free bound and its obstruction

This bounded attempt studies what follows from the actual zero-layer contraction
and the two-layer inequality in `wall1_two_layer_power_drift.md`. It yields a
shell-free finite-horizon inequality, but does not close the initial moment or
actual adaptive-history estimate. The obstruction below is to deductions from
those inequalities alone, not a counterexample to the lattice algorithm.

## Scale-compatible smoothing

Write L=1.10g, t=sqrt(R^2+1), and

    f_i(t)=p_i(sqrt(max(t^2-1,0))),
    Phi_d(i)=d/L_i^d * integral_0^{L_i} t^(d-1) f_i(t)^k dt,

for d>0 and k>=1. The extension on t<1 is constant p_i(0). Monotonicity gives
Phi_d(i)>=p_i(sqrt(L_i^2-1))^k, so this potential dominates the design-radius
bad event with threshold delta^k. The actual update is exactly
L_{i+1}=L_i*s_i^(-1/506), with no approximation of the subtraction by one.

Zero-layer projection and uniform pushforward give branchwise
f_{i+1}(t)<=f_i(t) for all t. A change of variables and monotonicity therefore
prove the exact inequality

    Phi_d(i+1) <= max(1,s_i^(d/506)) Phi_d(i).

If s_i<=S_i with S_i>=1 predictable, dividing by the cumulative product of
S_i^(d/506) gives a nonnegative supermartingale (indeed a branchwise decreasing
process). This uses no shell regularity or fresh-column assumption. It does
not mean that the unnormalized Phi is a supermartingale.

There is a stronger pathwise telescoping version: if all L_i>=L_min>=1 and
L_0<=L_max, repeated physical-radius contraction gives

    Phi_d(i) <= max(1,(L_max/L_min)^d) Phi_d(0),
    Pr[exists i: p_i(sqrt(L_i^2-1))>=delta]
      <= max(1,(L_max/L_min)^d) E[Phi_d(0)]/delta^k.                 (1)

If L_min exceeds L_0, replace the ratio by one. In (1) L_min is deterministic;
a stopped bound applies when it is guaranteed only before an exit. This avoids
a union over histories or times. For randomized L_0, use the stated deterministic
upper envelope, or retain the initial weighted moment explicitly.

However, (1) is weaker than directly controlling the initial void at the fixed
small radius sqrt(L_min^2-1). The normalized radial integral already satisfies

    Phi_d(0) >= (L_min/L_0)^d f_0(L_min)^k

when L_min<=L_0. Thus zero-layer smoothing has not created the missing initial
small-radius moment from a design-radius moment.

## Why the two-layer inequality alone does not cancel scale loss

Consider the exact finite group H of size h. Give all nonidentity marks the
same formal distance D>=1 and the identity distance zero. Below D the miss set
is A=C=H minus {0}. For U=0 its overlap with its translate has fraction
c=(h-1)/h; for U nonzero the fraction is (h-2)/h. Define the outgoing abstract
profile to equal these overlap fractions below D and zero at or above D.
This is a genuine nested-set overlap process. It satisfies the two-layer
inclusion and every power inequality at every B>=1, as well as zero-layer
contraction; it is not claimed to arise from an actual projected lattice.

With T=sqrt(D^2+1) below both L and aL, the incoming potential is
c^k(T/L)^d. The exact outgoing expectation at L'=aL is multiplied by

    a^(-d) F(h,k),
    F(h,k)=1/h+(1-1/h)*((h-2)/(h-1))^k.                    (2)

For any a<1 and d>0, choose h large enough that F(h,k)>a^d. Then the normalized
smoothed potential has strictly positive drift even though T/L can be made
arbitrarily small, making its initial value arbitrarily small. Consequently
an initial-smallness premise by itself cannot repair its conditional drift.

This is stronger than merely substituting r<=1 into the conditional bound:
(2) uses exact overlap moments. At the actual mark-size example h=3329,
k=24, and rational a=987/1000 (illustrative, close to the documented first
cap ratios), the amplification factors for d=1,24,505 are respectively

    1.00589208, 1.35911711, 735.70963584.

The critical d is 0.55103674. This rational a is not substituted for the actual
winner or its cap in a proof. The symbolic obstruction works for every a<1
with suitable h. It disproves a universal shell-free supermartingale claim
based only on the two existing inequalities, not one restricted to additional
reachable-lattice geometry.

A smoothing window whose actual lower support edge is eta*L, with positive
weight arbitrarily close above that edge, does not avoid this information
loss. Put a formal step at T between eta*aL and min(eta*L,aL): the incoming
window sees zero, whereas the outgoing window has positive overlap mass.
This gives zero initial potential and positive outgoing potential whenever
0<eta<1. A uniform shell condition is not the only possible repair, but some
new restriction on the radial profile or projection gains is necessary for
such window potentials.

## Quantitative budget tradeoff

For illustration use the documented g upper envelope 583.27530 and lower
bound 32.42764; their ratio is also the L ratio. For k=24, delta=.18 and a
1e-12 target, sufficient initial E[Phi_d] under (1) has log10 at most:

| d | sufficient initial log10 moment |
|---:|---:|
| 1 | -31.12842 |
| 24 | -59.99246 |
| 505 | -663.62737 |

No such initial moments are proved here. If instead one pays 277 generic
q=3329 winner caps, the scale penalties alone are 1.92822, 46.27736 and
973.75270 decimal orders for these degrees. These are conditional accounting
figures, not numerical failure probabilities. Low d reduces the scale price
but puts substantial weight at small physical radii, precisely where a
small initial void moment is not supplied by the design-radius estimate.

Run `python3 docs/research/scripts/wall1_smoothed_void_potential.py`.
The script uses exact rational overlap moments and high-precision interval
arithmetic for the budget figures. Log: `/tmp/wall1_smoothed_void_potential.log`.
There are no production edits, additional sampling assumptions, or new BKZ
security claims. A useful continuation would need a quantitative initial
integrated profile plus a lattice-specific gain beyond the overlap bound;
this stage does not supply either.
