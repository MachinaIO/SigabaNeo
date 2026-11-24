# Directional witnesses in the marked projection law

Even the **labelled nearest vector of every mark**, together with the winner line and length, does not determine which side of 0.18 the next void occupies in the abstract Part 108 kernel. An example below has next voids exactly \(600/3329\) and \(598/3329\) on every branch. A previously non-nearest representative accounts for the difference. For all near representatives there is an exact finite directional update. Its linear moment update needs a pooled direction-and-length distribution. Its coverage estimate also needs control of how many witnesses belong to the same mark.

On the actual graph law the two-mark argument gives a conditional tensor identity. A positive history-uniform isotropy lower bound for nearest witnesses fails even on a reachable draw-129 prefix. That prefix is far rarer than the proposed exception and is outside the crossing corridor. The raw counts do not initialize the projected directional estimate on the corridor. The ceiling through draw 405, with total exception at most \(10^{-12}\), remains open.

## 1. What the two marks average

Fix the incoming history, including its tie frame. Use the notation of [Part 108](wall1_first_tour.md), [Part 230](wall1_inductive_typicality.md) and [R101](wall1_drift_recursion.md). The old horizontal dimension is \(d=505\), the appended dimension is \(n=506\), and \(H=K/M\). The independent uniform old marks are \(U,V\). Write the selected unit winner as \(e_u=(a_u,k_u)/s_u\), with \(s_u\) the length of the unnormalized winner, and \(h_u=a_u/s_u\). Put \(Q_u=I-e_ue_u^T\). At \(t=1.10\) the new horizontal test radius is \(b(u)=\sqrt{(tg s_u^{-1/n})^2-1}\) whenever real.

**Conditional angular identity.** Choose a nearest vector \(y(x)\in x+M\) by a deterministic old-frame rule and set \(\theta(x)=y(x)/\|y(x)\|\) at nonzero length. For any old radial shell \(S\subset(0,\infty)\) of positive mark mass let
\[
 T_S=\mathbb E[\theta(V)\theta(V)^T\mid \|y(V)\|\in S],
 \qquad A=\mathbb E_U[h_Uh_U^T].
\]
For each integer \(j\), \(X_j=V+jU\) is uniform and independent of \(U\). Given \(U=u\) and \(\|y(X_j)\|\in S\), the expected squared horizontal directional cosine with the *full unit winner* is \(h_u^TT_Sh_u\). Averaging in \(u\) gives \(\operatorname{tr}(AT_S)\). In particular, if \(\|T_S-I/d\|_{\rm op}\le\delta\), the branch mean differs from \(\|h_u\|^2/d\) by at most \(\delta\|h_u\|^2\). These statements follow by translating the uniform second mark for each fixed first mark and contracting the dyad. Weighting both numerator and mass by \(\|y\|^2\) gives the corresponding energy-weighted identity. For the full offset vector \((y,j)\) the removed squared component is \((h_u^Ty+j k_u/s_u)^2\).

The two labels \((X_0,X_1)\) are independent before the reveal, by the bijection \((u,v)\mapsto(v,v+u)\). Their difference *is* the first mark. Consequently a joint angular test involving the winner cannot be factored into tests on two independent directions. The identity above supplies an exact directional expectation given the history. It gives no small upper bound on \(\delta\).

**Reachable failure of conditional isotropy.** In the width-506 graph with 400 output coordinates, take all 233 old raw columns to be zero at entry 129 (\(505+128-400=233\)). The old graph is the orthogonal sum \(q\mathbb Z^{400}\oplus\mathbb Z^{233}\). Each of the first 128 freezes removes one unit input axis, since those axes are the only shortest lines in each such window. Thus \(M=q\mathbb Z^{400}\oplus\mathbb Z^{105}\), and the marks are the full residue group on the 400 output axes. Since \(q=3329\) is odd, each mark has a unique nearest vector with centered output coordinates and zero input coordinates. On every nonempty positive radial shell, signs and permutations give exactly
\[
 T_S=\operatorname{diag}(I_{400}/400,0_{105}).
\]
Every next winner has length one, since old unit axes survive. Any unit winner with nonzero height is purely vertical. Every winner is therefore perpendicular to **all** these nearest vectors. The mean capture is zero, even conditional on an individual next branch. This prefix has probability \(q^{-93200}<10^{-328279}\) and \(g_{129}=3337.63998\ldots\), above the R101 corridor upper endpoint 583.27530. It disproves a pathwise consequence of mark uniformity. It supplies no lower bound of order \(10^{-12}\) on a corridor exit.

### Averaged isotropy does not remove the shared-history dependence

The conditional identity above averages to `E_S tr(A_S T_S)`, not
`tr((E_S A_S)(E_S T_S))`. Even exact isotropy of both marginal means
would not supply a positive capture lower bound. For any d>=2, choose I
uniformly in{1,...,d}, set A_I=e_I e_I^T and T_I=(Id-A_I)/(d-1).
Both are positive semidefinite of trace1. Direct summation gives

    E A_I = E T_I = Id/d,
    E tr(A_I T_I) = 0,
    tr((E A_I)(E T_I)) = 1/d.

The joint law is invariant under simultaneous signed coordinate permutations.
Thus that symmetry, even if established for a particular tie convention,
does not justify factoring the shared-history product. The missing term is
`E tr((A-E A)(T-E T))`, which equals−1/d in this example. This is an
algebraic obstruction to that inference, not a reachable lattice construction
or a lower bound on production failure. A proof using averaged symmetry
would still need a bound on the joint covariance. Moreover the actual
raw ensemble distinguishes output coordinates from the sequentially exposed
input coordinates, so full retained-space isotropy is not automatic.

## 2. A directional recursion with an explicit coverage term

Keep a separate cloud \(\mathcal C_x(L)=(\tilde x+M)\cap B_L\) for each mark, including zero when present. Its radius is a physical length. For an outgoing query of radius \(b\ge0\) and branch \(u\), set \(L=\sqrt{b^2+s_u^2/4}\). For a label \(v\), form the following finite set:
\[
 \mathcal D_u(v;b)=
 \left\{ Q_uz:
 \begin{array}{l}
 z=(y,j),\quad j\in\mathbb Z,\quad |j|\le L,\quad
 y\in\mathcal C_{v+ju}(\sqrt{L^2-j^2}),\\
 -s_u/2\le z^Te_u<s_u/2,\quad \|Q_uz\|\le b
 \end{array}\right\}.
 \tag{1}
\]
This is exactly the outgoing cloud at \(Q_{u*}v\). All lifts of a particular outgoing vector in the affine appended lattice differ by integer multiples of the primitive winner. Exactly one such lift has parallel coordinate in the half-open strip, and Pythagoras puts it inside \(B_L\). This proves both inclusions and counts each point once, even at the strip boundary. Old labels mapping to the same new mark give the same output cloud. The outgoing uniform-mark average equals the old uniform-\(v\) average by equal fibers.

For \(N_v=|\mathcal D_u(v;b)|\), \(D(z)=zz^T/\|z\|^2\) at nonzero \(z\), and \(D(0)=0\), the following is a branch recursion for the void and directional anisotropy. Work in the 505-dimensional outgoing plane and write \(I'\) for its identity:
\[
 \begin{split}
 p'_u(b)&=\mathbb E_v{\bf1}_{N_v=0},\\
 \Sigma'_u(b)&=\mathbb E_v\sum_{z'\in\mathcal D_u(v;b)}D(z'),\\
 \mathcal A'_u(b)&=\|\Sigma'_u(b)/\operatorname{tr}\Sigma'_u(b)-I'/d\|_{\rm op}
 \qquad (\operatorname{tr}\Sigma'_u(b)>0).
 \end{split} \tag{2}
\]
If a nearest-witness tensor is desired, take one shortest point of each nonempty cloud with a consistent outgoing tie rule. For the all-witness tensor, reindex \(v+ju=x\) separately in each \(j\)-summand of (1). Thus the **linear** sum for \(\Sigma'_u\), and also \(\mu_u=\mathbb E_vN_v\), can be computed from the pooled old counting measure \(\mathbb E_x\sum_{y\in\mathcal C_x(L)}\delta_y\) and the branch geometry. In contrast \(\nu_u=\mathbb E_v N_v^2\) includes pairs from labels differing by \((j'-j)u\). In particular,
\[
 \max(0,1-\mu_u)\ \le\ p'_u(b)\ \le\ 1-\mu_u^2/\nu_u
 \qquad(\mu_u>0). \tag{3}
\]
The lower bound is the union bound and the upper bound is Cauchy–Schwarz applied on \(N_v>0\). If \(\mu_u=0\) the void is one. A sufficient branch test is \(\nu_u\le\mu_u^2/0.82\) with \(\mu_u>0\). No independence of projected witnesses is used. Equations (1)–(3) can be applied at \(b=b(u)\) and iterated as cloud profiles, with the next winner determined by the marked lattice and tie rule. The following example shows why closing (2) on nearest-direction data alone loses information.

**Bounds using only the incoming void and nearest-direction tensors.** There is also a branchwise recursion by inequalities for the compressed pair. Let \(T(r)=\mathbb E_v[D(y(v)){\bf1}_{\|y(v)\|\le r}]\) be unnormalized, and use \(T'_u(b)\) for its outgoing counterpart. For each positive old distance \(\rho\) of mass \(m_\rho\), let \(T_\rho^\circ\) be the normalized tensor on that exact shell. Both shell inputs are jumps of the incoming profiles. Write \(J y=(y,0)\). For \(b>0\), the zero layer gives
\[
 p'_u(b)\le p(b)-
 \sum_{\rho>b}m_\rho
 \left(\frac{h_u^T T_\rho^\circ h_u-\tau_\rho}{1-\tau_\rho}\right)_+,
 \qquad \tau_\rho=1-b^2/\rho^2. \tag{4}
\]
On each shell, \(\|Q_uJy\|\le b\) precisely when the squared directional cosine is at least \(\tau_\rho\). Its mean is \(h_u^TT_\rho^\circ h_u\). Bounding that cosine squared by one on a hit and by \(\tau_\rho\) on a miss proves (4). This bound can be intersected with the two-offset drift of Part 230 after averaging over the first mark.

For the anisotropy update choose \(r=\min(b,s_u/3)\) and \(G=Q_uJT(r)J^TQ_u\) on the outgoing plane. Then
\[
 G\ \preceq\ T'_u(b)\ \preceq\
 G+\big[p(r)+h_u^TT(r)h_u\big]I'. \tag{5}
\]
Every nonzero vector of the outgoing lattice has a lift with parallel component at most \(s_u/2\) in magnitude and total norm at least \(s_u\). Its length after projection is at least \(\sqrt3\,s_u/2\). Thus whenever \(\|y(v)\|\le r\), the projected representative has norm at most \(s_u/3\), strictly below half this minimum, and is the unique nearest vector in its new coset. For a nonzero old unit direction \(\theta\) in this range the summand of \(G\) is \(zz^T\) with \(z=Q_uJ\theta\). Normalizing it to the new nearest dyad adds a positive semidefinite matrix of norm \(1-\|z\|^2=(h_u^T\theta)^2\) when \(z\ne0\). At \(z=0\) both dyads vanish. All remaining labels contribute a positive semidefinite remainder of norm at most \(p(r)\). Equal fibers again justify averaging with old labels. This proves (5).

In particular, setting \(P\) to the right side of (4), the outgoing tensor trace lies between \(\max(\operatorname{tr}G,1-P-1/|H'|)\) and \(1-1/|H'|\), since its exact trace is \(1-p'_u(b)-1/|H'|\). Equations (4) and (5) bound both members of the compressed pair from incoming profiles and branch geometry. They allow unresolved nearest-vector changes outside the certified radius \(r\); the full-cloud update resolves those changes. When the trace is positive, its normalization in (2) converts these matrix bounds to anisotropy bounds. For instance, if \(L_T\le\operatorname{tr}T'_u(b)\le U_T\) with \(L_T>0\), the normalized eigenvalues lie between \(\lambda_{\min}(G)/U_T\) and \(\min(1,(\lambda_{\max}(G)+p(r)+h_u^TT(r)h_u)/L_T)\).

## 3. Identical labelled nearest vectors, different next voids

Use \(B=1/4\) and the dimensionless rational constants
\[
 \ell=2.44,\quad \sigma=0.4,\quad h=0.401,\quad t_0=0.085 .
\]
In the first three coordinates, take generators \(B\sigma e_1,B\ell e_2\) in both lattices. The third generator is \(Bh e_3\) in lattice A and \(B(\sigma e_1/2+t_0 e_2+h e_3)\) in lattice B. Add 502 common orthogonal sides of length \(c\), where
\[
 c^{502}=\frac{V_{506}(\sqrt{1+B^2}/1.10)^{506}}{B^2\ell h}.
\]
Use the same cyclic labels generated by \(B\ell e_2/q\) modulo each lattice. Take \(K\) to be the full preimage of this order-\(q\) group. Both determinants equal \(B\sigma\, V_{506}(\sqrt{1+B^2}/1.10)^{506}\), and \(c>0.1694>B\sigma\). Any vector using the third generator with nonzero coefficient has third component of magnitude at least \(Bh>B\sigma\). Any nonzero appended height has norm at least one. The unique shortest line in both cases is therefore \(e_1\), of winner length \(B\sigma\), for every first mark. The outgoing threshold is exactly \(B\).

Write \(x=\ell v_c/q\) with \(v_c\) the centered label. In both lattices the **unique** nearest vector is \(Bx e_2\). For A this follows coordinatewise. For B, divide lengths by \(B\) and let \(m\) be the coefficient of the third generator. At \(|m|=1\), the best possible squared distance minus \(x^2\) is at least
\[
 \sigma^2/4+h^2+t_0^2-\ell t_0>0 .
\]
Indeed the best second-coordinate distance over the two signs and all periods is \(||x|-t_0|\). For \(|m|\ge2\), the circle-distance triangle inequality gives a decrease in squared second-coordinate distance of at most \(2|x||m|t_0\). The third-coordinate cost alone is \(m^2h^2>\ell |m|t_0\). For \(m=0\) uniqueness follows from the centered odd-modulus label. This proves equality of the entire labelled nearest-vector lists, including their lengths and directions and hence every shell tensor built from them.

After projection off \(e_1\), only appended height zero can hit since \(B<1\). For A the normalized hit interval is \(|x|\le1\). For B, coefficients \(m=\pm1\) extend it to \(|x|\le t_0+\sqrt{1-h^2}\): the intervals meet the old interval, and the extension is below \(\ell/2\). For \(|m|=2\), \(2t_0+\sqrt{1-4h^2}<1\), and \(|m|\ge3\) costs more than one in the third coordinate alone. These interval tests are on the circle of period \(\ell\); none extends past its centered boundary. The extra orthogonal sides cannot improve a hit. It follows that for every branch the two outgoing voids are respectively
\[
 \frac{q-1-2\lfloor q/\ell\rfloor}{q}=\frac{600}{3329}>0.18,\qquad
 \frac{q-1-2\lfloor q(t_0+\sqrt{1-h^2})/\ell\rfloor}{q}
 =\frac{598}{3329}<0.18.
\]
Here \(g=0.93281\ldots\). As with the audited R101 example, this is an obstruction on the abstract state space. It does not assert a bad draw in the reachable scale corridor. It also leaves open recursions using all-witness angular measures with additional overlap information.

## 4. How much capture can isotropy certify?

Take a representative on the old reference sphere of radius \(b_*=\sqrt{(1.10g)^2-1}\) and test its zero layer at the deterministic cap-comparison radius \(B_0\) of R101. It needs squared capture fraction \(\tau=1-(B_0/b_*)^2\). At the two draw-129 endpoints, R101 gives the following values. The last column is an **upper bound** on the angular hit fraction if this shell has \(T_S=I/505\), even granting a fully horizontal winner.

| Draw-129 scale | Required fraction \(\tau\) | Upper bound \(1/(505\tau)\) |
|---|---:|---:|
| Lower endpoint | 0.02554247… | 0.07753 |
| Upper corridor endpoint | 0.0260640… | 0.07598 |

Indeed for \(X=(h_u^T\theta)^2\in[0,1]\) with mean \(m\), the second moment of direction alone gives
\[
 \max(0,(m-\tau)/(1-\tau))\le\Pr(X\ge\tau)\le\min(1,m/\tau)
 \quad(0<\tau<1).
\]
The lower bound at either endpoint is zero. For example, directions uniform on sign vectors divided by \(\sqrt{505}\) have tensor \(I/505\), yet relative to the first axis every squared cosine equals \(1/505\). This illustrates the exact absence of guaranteed cap mass from isotropy alone. The table tests a boundary radius, without an assumption that the actual shell has an atom there. Smaller actual winner lengths can increase the branch radius. Multiplicity and selection among many lifts can also change the result.

Even granting a hypothetical sequence with conditional energy capture exactly \(1/505\) of the residual energy of one tracked vector at each step, the tower property gives mean retained fraction \((504/505)^{276}=0.57863899\ldots\). The mean loss is **42.1361%**. On the R100 corridor, outside its short-lift exception \(<10^{-13.64}\), a qualifying final nonzero-height witness must lose **more than 89.9989%**. To reach the corresponding residual fraction by a constant deterministic rate requires \(1-((1.10\cdot35.0743)/122)^{2/276}=0.00830763\ldots\) per step, about 4.20 times \(1/505\). The energy comparison is for one tracked vector. It neither bounds the best among many candidates by its mean nor assumes isotropy after conditioning on eventual selection.

## 5. Draw 129 and the exception budget

At the deterministic corridor endpoint \(R=641.6028228\ldots\), the R101 sampled-column raw height-one bound is
\[
 J_{129}(R)=2q^{-400}V_{633}(R^2-1+633/4)^{633/2}<1.630\cdot10^{-130}.
\]
This applies on every old raw prefix. If the displacement map has kernel order \(q^e\), crediting each whole fiber containing any such column gives at most \(\min(1,q^eJ_{129}(R))\) distinct-mark coverage. This is below 0.00104 for \(e\le36\). At radius 970 the sampled-column bound is below \(10^{-16.19}\). Outside that event a projected height-one hit at the corridor endpoint must lose more than \(1-(641.60283/970)^2>0.56248\) of its raw squared length over the first 128 freezes. The raw graph bound in [Part 227](wall1_frozen_contraction.md) counts more than \(2.14\cdot10^{52}\) height-one raw vectors through radius 2383 on the stated high-probability event. At the outer sphere of that ball the required capture is greater than 0.9275. Neither that count nor the raw dyad estimate of [Part 225](wall1_raw_graph_winner_cap.md) controls projected multiplicity per mark in (3). For comparison, an exactly isotropic raw shell in dimension 634 has mean capture \(128/634<0.202\) along a fixed 128-plane. That calculation does not assert conditional isotropy for the selected plane.

The missing seed is a lower bound of 0.82 on **projected distinct-mark coverage** at entry 129 outside a charged event. The first missing propagation is \(129\to130\). Even the ideal minimum-eigenvalue estimate in R101 leaves a shell of width 6.65393… at the lower endpoint and 7.78870… at the upper endpoint. Equations (1)–(3) identify the all-witness measurements that would credit this shell. For example, if the seed fails with probability at most \(\varepsilon_{129}\) and (3)'s sufficient branch test fails with conditional probability at most \(\varepsilon_i\) on surviving transitions into entries \(i=130,\ldots,405\), the probability of any exit is at most \(\sum_{i=129}^{405}\varepsilon_i\), by partition at first failure. The test must be evaluated before conditioning on future crossing. Equal allocations would allow \(10^{-12}/277\) per entry. The available counts establish neither this seed nor these branch probabilities. The resulting limitation is on the certificate; the actual exceptional-history probability has not been determined.

## Reproduce the numerical checks

Run the embedded interval script in the research scripts directory. The exact floor comparisons include the two labels on which the counterexample changes the outcome.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_directional_potential.md | python -B -)
```

```python
from fractions import Fraction as F
from mpmath import iv

iv.dps = 70
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
q, d, n = 3329, 505, 506
V = [I(1), I(2)]
for k in range(2, 635):
    V.append(2*iv.pi*V[k-2]/k)

def enclose(value, low, high):
    assert I(low) < value < I(high), (value, low, high)

def interval(f):
    return I(f.numerator)/f.denominator

def smaller(a, b):
    assert a < b or b < a
    return min(a, b)

# Exact rational geometry of the two labelled examples, in units of B.
ell, sig, h, shift = map(F, ('2.44', '.4', '.401', '.085'))
B = F(1, 4)
assert sig < h and 3*h > 1 and B < 1
assert sig**2/4 + h**2 + shift**2 > ell*shift
assert 2*h**2 > ell*shift
assert 4*h**2 < 1 and 1-4*h**2 < (1-2*shift)**2
edge = interval(shift)+sqrt(1-interval(h)**2)
assert 1 < edge < interval(ell)/2
assert q//ell == 1364 and 1365 < q*edge/interval(ell) < 1366
assert q-1-2*1364 == 600 and q-1-2*1365 == 598
assert F(598, q) < F('.18') < F(600, q)
t = I('1.10')
gp = sqrt(1+interval(B)**2)/t
c = exp((log(V[n])+n*log(gp)-log(interval(B**2*ell*h)))/502)
enclose(c, '.16946', '.16947')
enclose(gp*exp(log(interval(B*sig))/n), '.93281', '.93282')

# The raw zero prefix and the two draw-129 cap comparisons.
Q = log(I(q))
H = log(I('56.2142'))/2+log(V[n])/n
x = (400*Q-log(V[n]))/n
enclose(exp(x), '3337.63997', '3337.63999')
assert 400*(505+128-400) == 93200
assert 93200*Q/log(10) > 328279
for i in range(1,129):
    x -= smaller(Q,x+H)/n
u = log(I('34.807'))
for i in range(405,128,-1):
    u = smaller(u+Q/n, (n*u+H)/(n-1))
enclose(exp(x), '509.39214', '509.39215')
enclose(exp(u), '583.27529', '583.27530')
for z, tau_bounds, cap_bounds, gap_bounds in [
    (x, ('.02554247','.02554248'), ('.07752','.07753'), ('6.65393','6.65394')),
    (u, ('.02606398','.02606401'), ('.07597','.07598'), ('7.78870','7.78871')),
]:
    r = t*exp(z)
    old = sqrt(r**2-1)
    comp = sqrt((r*exp(-smaller(Q,z+H)/n))**2-1)
    tau = 1-(comp/old)**2
    enclose(tau, *tau_bounds)
    enclose(1/(d*tau), *cap_bounds)
    enclose(old-comp*sqrt(I(d)/(d-1)), *gap_bounds)

def log_J(R):
    m = 633
    return log(2)-400*Q+log(V[m])+I(m)/2*log(R**2-1+I(m)/4)

R = t*exp(u)
enclose(R, '641.6028228', '641.6028229')
assert exp(log_J(R)) < I('1.630e-130')
assert exp(36*Q+log_J(R)) < I('.00104')
assert log_J(970)/log(10) < I('-16.19')
assert 1-(I('641.60283')/970)**2 > I('.56248')
assert 1-(I('641.60283')/2383)**2 > I('.9275')
assert I(128)/634 < I('.202')

residual = (t*I('35.0743')/122)**2
enclose(1-residual, '.8999899', '.8999900')
enclose((I(504)/505)**276, '.57863899', '.57863900')
rate = 1-exp(log(residual)/276)
enclose(rate, '.00830763', '.00830764')
enclose(d*rate, '4.195', '4.196')
print("Verified labelled voids, raw prefix, angular thresholds, seed and block bounds.")
```

## Audit

**Verdict. Confirmed.** The embedded 70-digit interval verifier passed. An independent enumeration used integer squared distances for all 3,329 centered labels.

1. **Nearest vectors and projected voids.** In units of \(B/(1000q)\), put \(X=2440v_c\) and \(P=2440q\). For a third-generator coefficient \(m\) in lattice B, the least projected squared distance at height zero is \(\operatorname{dist}(X+85qm,P\mathbb Z)^2+(401qm)^2\). Before projection the least squared distance on this layer has the additional term \((200q)^2\) for odd \(m\). Lattice A has zero shift and zero additional term. Enumerating \(-3\le m\le3\) suffices for both tests because \(4\cdot401q>P/2>1000q\). For every label in both lattices the unique incoming minimizer is at \(m=0\), with vector \(Bx e_2\). Both rank-505 lattices have the same unique shortest line and length \(B\sigma=0.1\) on every branch. There are 600 misses in A and 598 in B. The two new hits in B are \(v_c=-1365\) at \(m=1\) and \(v_c=1365\) at \(m=-1\). Their old nearest vectors still miss after projection. Each new hit comes from a previously non-nearest layer. Thus the voids are exactly \(600/3329\) and \(598/3329\). Both examples have \(g=0.93281495\ldots\), while Part 231 gives \(g_i>32.42764\) on every draw from 129 through 405.

2. **Angular expectation and the reachable prefix.** For fixed \(u\), translating \(v\) by \(ju\) permutes the marks and preserves the shell probability. Contracting the shell tensor with \(h_u\) gives \(h_u^TT_Sh_u\) on that branch and \(\operatorname{tr}(AT_S)\) after averaging. The inverse of \((u,v)\mapsto(v,v+u)\) is \((x,y)\mapsto(y-x,x)\), so the pair also determines the winner's first mark. On the all-zero prefix, the first 128 freezes remove input axes. At entry 129 the nearest vectors lie entirely in the 400 output coordinates, while every unit winner lies on a surviving input axis or the appended axis. Thus every branch has zero capture for every horizontal nearest witness, including all nonzero shells. The 233 zero columns have probability \(3329^{-400\cdot233}=10^{-328279.6457086\ldots}\). This prefix is reachable and its \(g_{129}=3337.63998036\ldots\) exceeds the crossing-corridor upper endpoint \(583.27530\).

3. **Block loss.** Conditional mean capture of \(1/505\) of the residual squared norm at each freeze gives a mean loss of \(1-(504/505)^{276}=42.13610044\ldots\%\) for one tracked vector. On the Part 230 corridor, outside its short-lift event of conditional probability \(<10^{-13.64}\) given the incoming draw-129 history, every qualifying final nonzero-height witness has squared-norm loss strictly greater than \(1-(1.10\cdot35.0743/122)^2=89.99899294\ldots\%\). The first figure is an expectation for one vector. The probability of a corridor exit remains open.
