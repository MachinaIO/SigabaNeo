# Plant height in the width-506 score and prefix test

**The entire horizontal reduction history preserves the product CBD(3) law.** The score already integrates over that law. Splitting its known first-moment charges by plant height gives less than \(5.28350\cdot10^{-8}\) at height zero and \(6.99809\cdot10^{-8}\) at positive heights. The outstanding \(5.2408\cdot10^{-7}\) is one shared allowance. Neither the fraction needed at height zero nor the fraction of actual rejections caused by height zero is determined by the cited bounds. The lift test has no competitor-height index.

## Which history can be conditioned on?

**Lemma 1.** Let \(D=(A,\omega)\), where the preprocessing coins \(\omega\) are independent of the design and plant. Write \(X\) for the 912 horizontal plant coordinates in the unconditioned Part 117 marginal restart. For any history \(T\) of the stated null-only preprocessing, \(\mathcal L(X\mid T)=\mathrm{CBD}(3)^{\otimes912}\) almost surely. The error and secret subvectors remain mutually independent. The same argument holds in Part 47 at its own dimensions.

Indeed, Part 47 chooses a basis of \(L_0(A)\) and reduces that basis. The direct sum \(L=L_0\oplus\mathbb Zu\) identifies the height slices algebraically. The algorithm's choice of input to the reducer is what gives independence. In the marginal restart each of the 407 appends uses a column of \(A\). Taking a signed shortest vector, freezing it, and projecting the remaining window all preserve measurability with respect to \(D\). Thus \(\sigma(T)\subseteq\sigma(D)\), and \(X\) is independent of \(D\). Conditional on \(D\) the projector \(P\), the lattice \(H=P L_0\), and the prefix GS vectors are fixed. The embedded target first matters in the terminal search. A nonzero last **graph** coordinate during preprocessing is compatible with plant height zero. [Part 47](wall1_decoupled.md) · [Forward pass](wall1_first_tour.md) · [Marginal restart](wall1_score_rejection.md)

This statement ends before conditioning on \(b\) or on the realized terminal answer. For instance, given \(A,s,b\), the congruence fixes each error modulo 3329 and hence fixes the error on its seven-point support. A reducer that inspected the embedded target from the outset would require a separate conditional law. No such inspection occurs in this prefix.

## Three conditional kernels

Write \(Y=PX,\ Z=\|Y\|^2,\ a=959.5,\ B=1+a\) and \(\tau=0.00012938\). All probabilities in this section condition on \(D\). Sum over signed \(v\in H\setminus\{0\}\). Write \(C_k(D)\) for the sum of the following probabilities, with the cap included once in each summand. Then \(C=C_0+C_+\), with \(C_+=\sum_{k=1}^{30}C_k\). Sign reversal of the *embedded* competitor accounts for negative plant heights. At zero height both horizontal signs occur in the score. [Exact score](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockScore.lean)

**Lemma 2.** For \(r=\|v\|\) the exact conditional events are

| Plant height | Event for a signed point \(v\) |
|---|---|
| \(0\) | \(r^2-1\le Z\le a\) |
| \(1\) | \(Z\le a,\quad \langle X,v\rangle\le-r^2/2\) |
| \(2\le k\le30\) | \(Z\le a,\quad \|Y+kv/(k^2-1)\|^2\le r^2/(k^2-1)^2-1\) |

Expand \(\|v+kY\|^2+k^2\le1+Z\), use \(Pv=v\), and complete the square for \(k\ge2\). A negative right-hand side describes an empty ball. In particular a contributor at \(k\ge2\) has \(k^2-1\le r\le k\sqrt a+\sqrt{B-k^2}\). The upper bound is the triangle inequality on the cap. Height 30 only uses \(899\le r<937.053\). For each fixed history these are exact finite product-CBD integrals, including all ties. One can fix \(s\), sum each indicator over \(e\) with its original CBD mass, and finally average over \(s\). Holding \(b\) fixed in that inner sum would change it.

There is also a scalar first-moment upper bound at each positive height. Put \(p=-\langle X,v/r\rangle\). At height one the event requires \(p\ge r/2\). At \(k\ge2\) with \(r\ge k^2-1\), projecting the displayed ball onto \(v/r\) requires
\[
 p\ \ge\ t_k(r)=\frac{kr-\sqrt{r^2-(k^2-1)^2}}{k^2-1}.
\]
Set \(t_1(r)=r/2\). The CBD variance proxy of a unit linear form is \(3/2\), so summing \(\exp[-t_k(r)^2/3]\) over the eligible signed lattice points bounds \(C_k(D)\). This proves a per-history inequality, but evaluating its design mean needs the selected lattice's counting measure. The exact kernels additionally retain the embedding orientation.

**A quantitative obstruction to a uniform small bound.** In the *400-row marginal restart*, take \(A=0\). The initial window contains 400 sample periods and 105 orthogonal secret units. Each append adds a secret unit and freezes one of the 106 unit axes, regardless of how the tie is resolved. The final output still contains 105 secret units. For a retained axis \(i\), exactly one of the two height-one signs counts if \(|X_i|\ge1\) and the cap holds. Since \(\Pr(|X_i|\ge1)=11/16\) and the uniform cap tail is below \(0.00047835048014\), linearity gives \(C_1(0)>72.13727\). This bounds the full positive-height score from below on a reachable history, without assuming independence from the cap. The design has mass \(3329^{-400\cdot512}\). It gives no significant lower bound on the average and makes no claim about the unpaid class alone. [Marginal zero design and cap](wall1_detect_repair.md)

Part 236's translated-ball credit fixes the whole plant and sums **over the uniform design** for a raw graph point. It uses a bounded ambient integer ball. After a width-506 projection, the inverse image is a cylinder with the *selected* frozen space as its axis. Fixing \(D\) fixes that cylinder geometry but also fixes membership in the graph. Fixing \(X\) leaves the cylinder dependent on \(A\). Part 239 recovers the raw membership calculation where a translated raw lift of norm at most 250 exists. Beyond this class neither order of conditioning supplies the raw factor \(3329^{-400}\) for each selected projected point. [Part 236 audit](wall1_selfdual_envelope.md#audit) · [Part 239](wall1_score_rejection.md)

## What can be assigned to each height?

At each height assign a summand to the first applicable Part 239 class in table order. Call the remaining conditional score \(U_0(D)\) or \(U_+(D)\) according to height. This makes the partition disjoint even when an underlying upper bound charges overlaps. The entries below are outward-rounded **upper bounds on means** under the marginal design law.

| Part 239 class | \(k=0\) | \(1\le k\le30\) |
|---|---:|---:|
| Horizontal last win, nonzero last graph coordinate | \(5.26586\cdot10^{-8}\) | \(6.46897\cdot10^{-8}\) |
| A translated raw lift through radius 250 | \(1.76372\cdot10^{-10}\) | \(5.29114\cdot10^{-9}\) |
| Paid terminal-line deficiencies | \(10^{-258}\) | \(10^{-69}+10^{-920}\) |
| Combined, using unrounded entries | \(5.28350\cdot10^{-8}\) | \(6.99809\cdot10^{-8}\) |

The fresh-column row uses the Part 239 prefactor at \(k=0\) and its Gaussian-weighted sum over \(1\le k\le30\). The raw row uses one copy and thirty copies of the same raw-ball bound. The section row includes deficiency through 132 at heights zero and one, and through 131 at all larger heights. In either unpaid class all translated raw lifts are long. On a horizontal last win the surviving terms have last graph coordinate zero. An unpaid height-zero or height-one line has deficiency at least 133, and an unpaid higher-height line has deficiency at least 132. [Part 239 estimates](wall1_score_rejection.md)

Consequently a sufficient condition for the proposed mean proof is
\[
 \mathbb E_D U_0+\mathbb E_D U_+\le5.2408\cdot10^{-7}.
\]
The two charged means amount to less than \(0.000408371\) and \(0.000540895\) in units of rejection probability after division by \(\tau\). The shared allowance contributes \(0.004050704\) rounded up on the same scale, giving a total below \(0.005\) with the unrounded constants. These are additive terms in Markov's inequality. They do not measure observed frequencies. For any prescribed \(0\le f\le1\), proving the two residual means below \(f\) and \(1-f\) times the allowance would suffice. No particular \(f\) follows from these data.

For a disjoint attribution of actual score rejection, assign priority to height zero. Then exactly
\[
 \delta_s=\Pr_D(C_0>\tau)+\Pr_D(C_0\le\tau,\ C_+>\tau-C_0).
\]
The second term includes designs where neither component individually exceeds \(\tau\). Both probabilities are unknown. The analogous plant-by-plant score failure and the design rejection of the *averaged* score are different events.

**Why \(E,Z_1,Z_2\) do not identify the first term.** Lemma 2 gives \(C_0=\mathbb E[\mathbf1_{Z\le a}N_H(\sqrt{1+Z})\mid D]\), where \(N_H\) counts signed nonzero points. Even at height zero the realized counting radius depends on the plant. After averaging, the weight of a fixed point depends on the projected-energy law as well as its length. \(F=\{\lambda_1(H)\le26\}\) tests one radius, while the full count reaches \(\sqrt{960.5}\). Part 239's reachable graph of minimum \(\sqrt{730}\) gives **\(C_0>0.52566\)** from just its two shortest points; \(E\) and \(F\) both fail. Its zero suffix gives raw units, so it also fails the raw-good gate required by \(Z_1,Z_2\). Those residuals concern the first area hit of a reduction history with a terminal hit. Part 240 separately exhibits a *gated*, inherited, long-raw-lift height-zero pair with conditional contribution above 1.98963 on a family of mass exceeding \(10^{-20050}\). In particular \(\mathbb E U_0>1.98963\cdot10^{-20050}\), while that construction gives no comparable upper bound on the whole height-zero mean. High frozen deficiency by itself is typical, with probability exceeding \(1-10^{-1069}\) simultaneously through draw 407. [Part 237](wall1_detect_repair.md) · [Part 239 counterexample](wall1_score_rejection.md) · [Part 240](wall1_high_deficiency.md)

## The prefix acceptance event

Let \(g_i\) and \(w_i\) be the lengths and unit vectors of the 407 frozen GS directions. Every lift of the correctly oriented planted projection differs from the plant by an element of the horizontal prefix lattice. With strict strips, \(|\langle X,w_i\rangle|<g_i/2\) for all \(i\) suffices for correct Babai lifting. The probability of the union of strip violations given \(D\) is at most \(S(D)=\sum_i2e^{-g_i^2/12}\), by the same CBD tail. In particular the *joint* probability of a correct terminal projection and a failed lift is bounded by \(S(D)\) given \(D\). Conditioning further on the terminal answer would change the plant law. Every candidate in this lift fiber already has plant height one, and every difference of two candidates in the fiber has height zero.

The design gate \(S(D)\le\ell\) is deterministic given the prefix. Its additional rejection is exactly \(\Pr_D(C_0+C_+\le\tau,\ S>\ell)\). At \(\ell=0.000623\), if score rejection meets 0.005, the remaining sufficient joint-prefix allowance is 0.003769269 for the marginal block or 0.003546229 after the Part 117 coupling charge. Part 239 bounds a length at most 13 in the first 210 draws by \(4.9300\cdot10^{-18}\), but leaves late, high-deficiency small winners on score-accepted designs open. Its second example has \(C=0\), yet 407 discarded secret coordinates retain their prior even given the indicated terminal outcome. Their joint maximum atom is \((5/16)^{407}<2.535\cdot10^{-206}\). Score acceptance alone therefore gives no uniform lift guarantee. [Part 47 lifting](wall1_decoupled.md) · [Part 239 prefix law](wall1_score_rejection.md)

## Arithmetic check

The checker below runs from `docs/research/scripts/` and imports the same interval primitives as Part 239. Keeping it in this note preserves the single-file change. From the repository root run

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_height_split.md | python -B -)
```

```python
from mpmath import iv
from wall1_score_rejection import log_floors, log_theta, maximum, raw_mass, section_mass

iv.dps = 50
I = iv.mpf
d, a, tau = 505, I('959.5'), I('.00012938')
last = log_floors()[-1]
floor = maximum(last - iv.ln(3329), I(505)/506 * last - iv.ln(I('56.2142'))/2)
t = d/(2*(1+a))
u = (1-3*d/(2*a))/3
z = iv.sqrt(iv.pi/t)
fresh0 = iv.exp(t*(1+a) - u*a - I(d)/2*iv.ln(1-3*u)
                + d*(iv.ln(z)+log_theta(z)) - floor)
freshplus = fresh0 * sum(iv.exp(-t*k*k) for k in range(1, 31))
raw = raw_mass(912, 400, 250)

def sections(radius, deficiency):
    return section_mass(912, 408, iv.ln(radius)-floor, deficiency)

low0 = 4 * sections(31, 132)
low1 = 4 * (sections(50, 132) + iv.exp(-I(2500)/12)*sections(62, 132))
low2up = 120 * sections(938, 131)
assert low0 < I('1e-258') and low1 < I('1e-69') and low2up < I('1e-920')
assert fresh0 < I('5.26586e-8') and freshplus < I('6.46897e-8')
assert raw < I('1.76372e-10') and 30*raw < I('5.29114e-9')
paid0, paidplus = fresh0+raw+low0, freshplus+30*raw+low1+low2up
allowance = I('5.2408e-7')
assert paid0 < I('5.28350e-8') and paidplus < I('6.99809e-8')
assert paid0/tau < I('.000408371') and paidplus/tau < I('.000540895')
assert allowance/tau < I('.004050704')
assert (paid0+paidplus+allowance)/tau < I('.005')
assert 30*iv.sqrt(a)+iv.sqrt(1+a-900) < I('937.053')
assert 105*(I(11)/16-I('.00047835048014')) > I('72.13727')
assert (I(5)/16)**407 < I('2.535e-206')
print('charged means by height:', paid0, paidplus)
print('Markov upper bound if the shared allowance is met:',
      (paid0+paidplus+allowance)/tau)
```

## Audit

**Verdict.** Confirmed for Part 239's unconditioned 400-row marginal restart and its signed forward pass. The embedded interval checker passed every assertion.

**Conditioning.** Each prefix decision uses only \(A\) and independent preprocessing coins, so even observing all 407 choices preserves the joint product law of \((e,s)\). For a completed history fixing \(P,H\), expanding the competitor inequality gives the three kernels in Lemma 2, including equality. For a partial history \(T\), the terminal score at height \(k\) is averaged over the remaining geometry as \(\mathbb E[C_k(D)\mid T]\). For the completed prefix, failure to lift the correctly oriented projection implies at least one strip violation. The conditional union bound is \(S(D)\) for the joint event of correct projection and failed lift.

**Mean charges.** The raw-lift test involves \(\|w+kX\|\). Apply the table's priority to each realized \((D,X,k,v)\) before averaging over \(X\). This gives disjoint contributions and preserves Part 239's bound for each class. The checker enclosed the resulting upper bounds below \(5.283493\cdot10^{-8}\) at height zero and \(6.998082\cdot10^{-8}\) over heights 1–30. Adding the single proposed residual allowance and dividing by \(\tau\) gives less than \(0.004999968\).

**Reachable examples.** In the \((27,1)\) construction the two signed shortest points both count at height zero throughout \(729\le Z\le959.5\). Cantelli's inequality and the cap tail give \(C_0\ge 2(28.5^2/(2272.5+28.5^2)-0.00047835048014)>0.52566620\). The terminal minimum is \(\sqrt{730}>26\). At cut 406, removing that old shortest line leaves transverse spacing \(3329/\sqrt{730}>123\) and an orthogonal factor of minimum \(>938\), so \(E\) also fails. A zero suffix column among the first 511 supplies a raw unit, violating the radius-250 gate common to \(Z_1,Z_2\). On the separate all-zero design, every tie rule retains 105 secret axes. Each such axis contributes one sign on \(\{|X_i|\ge1,\ Z\le a\}\), giving \(C_1>105(11/16-0.00047835048014)=72.1372731995853\).

**Open probabilities.** The two events in the displayed decomposition of \(\delta_s\) are disjoint and exhaust \(C_0+C_+>\tau\), including a rejection caused by two individually subthreshold scores. Their probabilities, the residual mean bound, and the additional prefix rejection on score-accepted designs remain open. For the 511-row transfer the literal prefix charge on coupling agreement is \(S+222e^{-3329^2/12}\). Part 239's sufficient floor \(g_i>13\) leaves room for that increment at \(\ell=0.000623\). The quoted \(0.003546229\) is an allowance after paying the coupling error once.
