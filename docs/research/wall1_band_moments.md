# Band moments with first-exit accounting at width 506

Removing all lines below the restart band costs less than \(1.364\cdot10^{-10}\). Nevertheless the rank-one packing recursion, even using the improved minimum on the surviving graphs, already charges more than \(10^{279}\) for **one** ordinary coordinate axis at its first step. Keeping incidence through rank two avoids this charge. The first horizontal term where that strategy forgets incidence is rank three, and its unrestricted Haar count at the uniform gated cap exceeds \(10^{42.91}\). These are losses in two particular certificates. The exact marked failure probability remains open.

Use the unconditioned restart, \(d=505,b=506,q=3329,T=407,D_0=q^{400}\), and put \(G_d=V_d^{-1/d}, c=.954,\alpha=\sqrt3/2,B=.00488848\). The coupling costs less than .00022304. A direct failure bound of \(2B\) on the reduced law suffices. For separate horizontal and positive-height charges the proposed allocation is \(B\) each. [Restart](wall1_idea_round2.md) · [Terminal plane accounting](wall1_plane_count.md) · [Wall 1](../PROOF_GAP.md)

## (a) Kill the process on first exit

Choose lower endpoints \(l_r(D)\) in physical covolume units for the ranks being tracked. Kill a state if it has a saturated rank-\(r\) subgroup below any such endpoint. Let \(K\) be the exact uniform-draw transition on framed marked states, \(g\) the surviving-state indicator and \(\nu_0=g\mu_0\) the restricted restart law. Use subprobabilities:
\[
 \nu_{t+1}(f)=\nu_t K(gf),\qquad
 e_{t+1}=e_t+\nu_t K(1-g),\qquad e_0=1-\nu_0(1).
\]
For any terminal failure test \(f\) valued in \([0,1]\), its probability is bounded by \(e_T+\nu_T(f)\). In particular if the terminal line cutoff is the killing threshold, it suffices to bound exits. The additive coefficient is exactly one at all 407 steps. A single budget spread uniformly over those steps gives only \(1.2011\cdot10^{-5}\) per step before restart cost. An exact killed moment uses \(f=N_r(x)\), the strict cumulative count, with the child survival indicator **inside** the draw average. To estimate an exit by a moment one must count the prospective child *before* killing it.

On survivors there are no atoms below the chosen lower endpoints. Layer cake for a decreasing kernel can use a cumulative band bound up to its upper endpoint. If the required cap exceeds that endpoint one still needs the tail above it. Merely declaring rarer, deeper exceptions leaves the intermediate sub-band interval in the integral. At restart take the line endpoint \(R=cG_dD_0^{1/d}\). The graph cube bound gives \(e_0\le5.803 c^d/(2\zeta(d))\) for line killing alone. Killing planes as well would require a further probability estimate. Zero columns alone cost at most \(105q^{-400}\), but even a collision of two nonzero columns yields a short difference. After projection the coordinate graph count no longer applies. [Moment comparison and audit](wall1_moment_closure.md)

Here is a test on actual surviving input. Each of the first 400 horizontal coordinate lines has primitive generator of length exactly \(q\), because setting the graph input to zero leaves \(q\mathbb Z^{400}\). Test the next normalized endpoint. The global cap for the pullback is \(C=q x,\ x=R/q^{1/d}\), since the actual cap increases as \(s^{1-1/d}\). In Part 124's packing upper bound set the improved minimum to \(R\). Its unit-height weight at the single atom \(a=q\) is
\[
 \left(1+2q\sqrt{x^2-1}/[V_2(R/2)^2]\right)^{504}
 >10^{279.73}.
\]
Even one axis contributes this times the surviving mass, against \(B\). Additional kills affordable within \(2B\) leave mass above .99. The strict band ending at \(q\) does not even see this endpoint atom, which lies inside the *incoming* cap. This is the price of the packing majorant of the pre-kill count, not evidence that an axis generates a witness.

For scale, a propagated normalized line multiplier starting at 5.803 could afford a constant geometric factor only about 1.04367 per step for one budget with no exits charged. For the full untruncated global-cap operator the Haar test of Part 124 gives at least \(q^{504}\) per step and \(10^{722525.18}\) over 407. The latter iteration uses all cutoffs. It is not an iteration on killed states. On the killed comparison the first step already exhausts the budget.

## (b) Keep the selected flag through rank two

For a history and draw let \(p:W\to Q\) be the projection along the winner. A child saturated subgroup \(P\) has full lift \(N=p^{-1}(P)\cap W\), of rank one higher and determinant \(s\det P\). For a marked flag apply this inverse image to every member and prepend the winner line. Thus the exact recursion sums the pulled-back flag indicator over saturated flags containing the selected line, averages with weight \(1/|H|\) over draws and integrates over the old history. Split the top subgroup by height. At height zero it lies in the old lattice. Otherwise its kernel has the old child rank and its generator is \((y,j)\) modulo the kernel, \(j>0, y\in j\tilde U+L\). Retain saturation, all flag incidences and the cap inside that finite draw average. This is precisely the marked recursion of Part 124 with the extra flag tests. At the last step it gives the horizontal hit \(w_0I_0\) and the residual positive-height count \(F_*\) of Part 120. Each old-state indicator can instead use the conditional hit probability, yielding an exact backward probability recursion with sup-norm factor one. Its initial expectation still has to be evaluated.

Quantify the first omitted flag. Follow the horizontal branch twice, write \(u,s\) for the successive selected lengths and \(D\) for the determinant before both steps. The second winner belongs to the first quotient, so \(s\ge\alpha u\). Terminal failure requires \(\alpha s<cG_d(D/(us))^{1/d}\). The horizontal triple on the old lattice has covolume below
\[
 gD^{1/d}(us)^{1-1/d},\qquad g=cG_d .
\]
Indeed the two lifts multiply covolume by \(s\) and \(u\). With \(p=us\), the gate gives \(p s^d<(g/\alpha)^dD\) and \(s^2\ge\alpha p\). Hence the uniform cap is \(Z D^{3/(d+2)}\), where
\[
 S=[\alpha(g/\alpha)^d]^{1/(d+2)},\qquad Z=g(S^2/\alpha)^{1-1/d}.
\]
Dividing by \(D^{3/d}\) gives at least \(z_3=Zq^{-6/(d+2)}\), since the projected axes bound \(D\le q^d\). Even exact Haar input for **all** triples at that uniform cap gives \(a(d,3)z_3^d>10^{42.91}\), over \(10^{45}\) times the horizontal allocation. This is the rank-three counterpart of Part 124's unrestricted plane test. A band covering the cap still pays this cost if it substitutes the unrestricted Haar moment with multiplier one. A smaller band omits required triples. This two-step test eliminates the need to iterate that relaxation 407 times. It gives no lower bound on the marked horizontal term. Sustaining the exact horizontal branch for 407 lifts would require flags up to rank 408. A scalar growth factor for those incidences cannot be read off from unmarked Haar moments.

## (c) Propagate the physical floor

Use the exact \(F=\sqrt{1+1.5d-\sqrt{4.5d/99}}\), between 27.45375 and 27.45377. In the terminal marked recursion replace \(R(s)\) by \(F\), the area cap by \(sF\), and the gate by \(s<F/\alpha<31.701\). The resulting uniform plane cap is below 870.309. The horizontal hit now tests \(a_0<tF\) and the residual positive-height count tests area below \(sF\) through the winner. This directly tests the physical observable. Its Haar line reference at fixed determinant is \((F/(G_dD^{1/d}))^d/(2\zeta(d))\). Even granting a terminal GH of 35.18 gives only about 1.3391 allowable geometric growth per step starting at 5.803 for one budget. That GH is counterfactual, and 5.803 is a restart bound only on the stated GH band. A physical-cutoff comparison would need determinant control or joint bins and an appropriate initialization.

A concrete complementary recursion propagates physical floors \(T_t\). On survivors choose \(R_t\le T_t\), charge the positive-height probability by the sum of Part 110's expected layer counts at radius \(R_t\) capped at one, and set \(T_{t+1}=\alpha R_t\). This follows since no horizontal vector is shorter than \(R_t\) and rounding gives \(\lambda_1(Q)\ge\alpha s\). Its best scalar factor is 0.866026 rounded up. Even granting \(T_0=q\) and free fresh layers, step 33 permits 28.8952 whereas step 34 permits only 25.0240. At step 407 the ceiling is below \(1.252\cdot10^{-22}\). Thus this implication leaves the whole unit probability as a possible terminal charge, over 204 times one budget. Holding the floor fixed instead requires the marked estimates each time. For example at \(m=F,a\downarrow F\) from above, the packing unit-height coefficient at the uniform physical cap \(F^2/\alpha\) approaches a value above \(10^{300.07}\). This is a kernel coefficient, not an expected count or a claim of incoming mass there.

The physical target is a necessary condition for the stated height-zero success. Part 123 reports zero physical failures at the tested sizes from 20 through 36, including runs that fail the ratio test. These data do not estimate conditional flag counts at 506. Neither of the two marked budget inequalities is certified for either terminal target. [Additive recursion](wall1_additive_tour.md) · [Physical observations and audit](wall1_experiments2.md)

## Interval checks

The rank-three coefficient below uses the Haar formula of Part 124. Dropping the two numerator zeta factors and bounding each of the three denominator zeta factors by two gives a strict lower bound. For the growth allowances use \(1<\zeta(d)<1+2^{-d}(1+2/(d-1))\).

```python
from mpmath import iv
iv.dps = 60
I = iv.mpf
d, q, T = 505, 3329, 407
V = lambda n: iv.pi**(I(n)/2) / iv.gamma(1+I(n)/2)
G = V(d)**(-I(1)/d)
A, c, B = iv.sqrt(3)/2, I('.954'), I('.00488848')
g = c*G
R = g*I(q)**(I(400)/d)
F = iv.sqrt(1+I('1.5')*d-iv.sqrt(I('4.5')*d/99))
zmax = 1+I(2)**(-d)*(1+I(2)/(d-1))
def growth(ratio):
    return (2*B/(I('5.803')*ratio**d))**(I(1)/T)
def weight(cap, a, m):
    return 504*iv.log10(1+2*iv.sqrt(cap**2-a**2)/(V(2)*(m/2)**2))
assert I('3221.64') < R < I('3221.65')
assert I('5.803')*c**d/2 < I('1.364e-10')
assert I('1.04366') < growth(c)
assert growth(c)*zmax**(I(1)/T) < I('1.04367')
assert weight(q*R/I(q)**(I(1)/d), I(q), R) > I('279.73')
assert 504*T*iv.log10(q) > I('722525.18')
S = (A*(g/A)**d)**(I(1)/(d+2))
z3 = g*(S**2/A)**(1-I(1)/d)*I(q)**(-I(6)/(d+2))
a3lo = (I((d-1)*(d-2))/6 * V(d)*V(d-1)*V(d-2)
        / (8*V(1)*V(2)*V(3)))
assert iv.log10(a3lo*z3**d) > I('42.91')
assert I('27.45375') < F < I('27.45377')
assert F/A < I('31.701') and F**2/A < I('870.309')
ratio = F/I('35.18')
assert I('1.33909') < growth(ratio)
assert growth(ratio)*zmax**(I(1)/T) < I('1.33910')
assert q*A**34 < F < q*A**33 and q*A**T < I('1.252e-22')
assert weight(F**2/A, F, F) > I('300.07')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES. All three bounds hold:

* (a) Exit mass is < 1.3632·10⁻¹⁰, and the first-update axis weight is 10^{279.7319}.
* (b) The rank-3 Haar mean exceeds 10^{42.915}, which is 10^{45.226} × the budget.
* (c) The physical floor is first crossed at step 34, and at step 407 the ceiling is < 1.25·10⁻²².

**Wording correction for (b).** The flag sum gives w_0 × (number of horizontal witnesses). The existence indicator w_0·I_0
comes from testing whether that number is positive (as in Part 120).

**Scope.** These are losses of the specific relaxations. The exact marked probability remains open.
