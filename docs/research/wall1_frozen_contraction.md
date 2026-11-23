# Frozen covolume, winner lifts, and the cost of dropping the projection test

**The nearest-plane lift bound gives an overwhelmingly common raw event.**
On a history crossing on draws 397–406, the nearest-plane error bound from the first 54 frozen vectors already exceeds 2383.79. Under the original raw graph law, except on a set of probability below \(3.276\cdot10^{-50}\), **every** draw 55–405 has more than \(2.14\cdot10^{52}\) primitive, height-one raw vectors of length at most 2383. One vector per draw gives an independent family in reveal order. Thus a raw test retaining those norm, primitivity, independence and reveal-order requirements, even on all 351 draws, cannot charge the 36 long winners. The argument below isolates the additional projection test and gives a numerical joint-probability target for it. The crossing probability on 397–406 and the unconditional bound on \(Z_{\rm rem}\) remain open. [R94 and audit](wall1_raw_graph_winner_cap.md#audit)

## What the winner product determines

At draw \(i\), let \(L_i\) be the appended raw graph, \(N=505+i\), \(F\) the frozen span of dimension \(f=i-1\), \(K=L_i\cap F\), and \(P=P_{F^\perp}\). The current window is \(M=PL_i\) of rank \(n=506\). Write \(s_i=\lambda_1(M)\), \(V_j=\pi^{j/2}/\Gamma(1+j/2)\) and \(g_i=(\det M/V_n)^{1/n}\). The determinant of \(L_i\) is \(q^{400}\), \(q=3329\). All frozen vectors extend by zero in later coordinates.

Choose any raw lift \(v_j\) of each previous winner. These lifts form a basis of \(K\). Indeed a shortest vector generates the entire lattice on its line in the projected lattice. Pulling back that line enlarges the previous saturated frozen section by precisely one integral generator. Subsequent appends preserve the old raw section, since membership of a vector with zero new coordinates is unchanged. Consequently
\[
 \det K=\prod_{j<i}s_j=\frac{q^{400}}{V_n g_i^n}.
 \tag{1}
\]
For a consecutive block \(a,\ldots,b\), its lifts projected off the span frozen before \(a\) have covolume \(\prod_{j=a}^b s_j\) by Gram–Schmidt. Their **raw** covolume also includes the components along that earlier span. For a sparse subset of draws in the block, the projected covolume is *at least* the product of the corresponding \(s_j\): when forming each Gram–Schmidt residual fewer previous directions have been removed. Thus bounds \(s_j>1.15g_j\) on 36 draws supply lower bounds on these factors. They supply no upper bound on the raw covolume of these lifts. [Part 222, determinant recursion](wall1_long_winner_handle.md#deterministic-sublattices-and-the-sign-of-feedback)

For an injectively projected rank-\(k\) section \(S\), its Jacobian is \(J_F(S)=\det(PS)/\det S\). If \(s_i>r\), Hermite's theorem gives \(\det(PS)>(r/\sqrt{c_k})^k\) for **every** such \(S\), where \(c_k\ge\gamma_k\). R94's \(J_F(S)<0.16135^k\) is necessary for a section *certifying a short winner* at draw 405 on the corridor and raw minimum gate. A long winner excludes every such certificate. On the same draw-405 corridor and gate, even a long winner satisfies \(J_F(\mathbb Z v)=s_i/\|v\|<h\,35.0743/250<0.192\) for every raw lift \(v\), by the window Hermite cap. This upper bound also holds for ordinary winners. Moreover a bare Jacobian condition can be made to hold on any history with \(f>0\). In a basis of \(S\) replace its first vector \(v\) by \(v+m u\), where \(0\ne u\in K\). The projected basis is fixed and the raw exterior product grows linearly in \(|m|\), since \(u\) is independent of the other basis vectors by injectivity. This also works for lifts of a basis of a saturated projected section. For example, choosing \(k\) projected basis vectors of \(M\) gives primitive lifted sections for every \(m\) by extending them, together with a basis of \(K\), to a basis of \(L_i\). A selected or shortest-lift condition therefore matters even at fixed rank and with primitivity imposed. [Part 206, section and projection indices](wall1_raw_section_compression.md)

## A bound for the actual winner's shortest lift

For any \(w\in M\), take a raw lift \(v\) and put \(p=(I-P)v\). The exact minimum squared raw length over the fiber is
\[
 \ell_F(w)^2=\|w\|^2+\operatorname{dist}(p,K)^2.
 \tag{2}
\]
All lifts differ by \(K\). Backward rounding in its frozen basis leaves each orthogonal Gram–Schmidt coordinate of the error at most \(s_j/2\) in absolute value. Thus the actual winner has a raw lift of length at most \(\sqrt{s_i^2+B_i^2}\), where
\[
 B_i=\tfrac12\sqrt{\sum_{j<i}s_j^2}
 \ \ge\ \tfrac12\sqrt f\,(\det K)^{1/f}\quad(f>0).
 \tag{3}
\]
The inequality is AM–GM. It lower-bounds the *computed upper bound*, not the particular winner's error in (2).

To bound (3) on a crossing path, put \(a=505/506\), \(h=\sqrt{56.2142}\,V_n^{1/n}\), \(u_{406}=\log 34.807\) and iterate R94's backward envelope
\[
 u_i=\min\{u_{i+1}+\log(q)/n,\ (u_{i+1}+\log(h)/n)/a\}.
\]
This follows by inverting the forward lower update from \(s_i\le\min(q,hg_i)\). The backward map is increasing and increases each value above \(\log 34.807\), so the latest permitted crossing also bounds earlier pre-crossing entries. Then \(g_{55}\le e^{u_{55}}<1672.376\). Substitution of \(u_{55}\) in (1)–(3) gives \(B_{55}>2383.79\). Since \(B_i\) is nondecreasing, this lower bound on the lift allowance holds from draw 55 onward on each crossing history, even after an earlier crossing.

At draw 405, for a crossing at or after that entry, the coarser endpoint \(g_{405}<35.0743\) already gives the following facts.

* \(\log_{10}\det K>1001.0959\). Any radius covering **all shifts** in the frozen torus \(F/K\) exceeds 1474.87, by \(V_{404}\rho^{404}\ge\det K\). The normalized torus volume within 250 of \(K\) is at most \(V_{404}250^{404}/\det K<10^{-311.40}\). This is a volume statement. Equation (2) samples a selected fiber whose shift need not be uniform on that torus.
* Even at radius **1474**, the raw graph contains at least 537 independent vectors on the raw minimum gate \(\lambda_1(L_{405})>250\). If \(m\) independent directions are spanned by vectors in that ball, the product of all 910 successive minima is at least \(250^m1474^{910-m}\). Minkowski's second theorem bounds it above by \((2G_{910})^{910}\), where \(G_{910}=(q^{400}/V_{910})^{1/910}\). Hence \(m\ge910\log(1474/(2G_{910}))/\log(1474/250)>536.17\). At least 133 directions survive projection in the sense of dimension. Their projected lengths are unspecified. [Minkowski's second theorem, Theorem 7.9.4](https://ocw.mit.edu/courses/18-225-graph-theory-and-additive-combinatorics-fall-2023/mit18_225_f23_lec22-25.pdf#page=21)

## Many short raw lifts at every required draw

Take \(R=2383\). At each of the 351 draws, keep the first 559 raw coordinates (400 outputs and 159 old inputs), set all intervening coordinates to zero, and set the newest input to 1. Let \(Z_i\) count such raw graph vectors of norm at most \(R\) with all coordinates centered modulo \(q\). This deterministic family is specified before any columns are drawn. The newest coordinate ensures primitivity, distinct projective representatives, and survival of the projection. One choice per draw gives a triangular minor with diagonal 1 on the selected newest coordinates, hence a primitive independent family in the final integer lattice as well.

Set \(d=559\) and \(A=\sqrt{R^2-1}-\sqrt d/2\). The radius-\(A\) ball restricted to \(|x_j|\le1664\) rounds into the allowed old-coordinate integer points. Each rounded point receives volume at most one. Integrating a ball slice above 1664 over a length at most \(A\), for both signs and every coordinate, shows that the discarded fraction is at most
\[
 \delta=2d\,\frac{V_{d-1}}{V_d}
          (1-(1664/A)^2)^{(d-1)/2}.
\]
Each candidate has graph incidence probability \(q^{-400}\). Distinct input vectors in this family are linearly independent over the field: their last coordinates force any proportionality factor to be 1, and centered representatives are unique. Their graph incidence events are independent. Equal inputs with different outputs have incompatible incidences. Therefore, for each draw under the original matrix law,
\[
 \mu_i=\mathbb E Z_i\ge (1-\delta)V_d A^d/q^{400}
 >4.2858\cdot10^{52},\qquad \operatorname{Var}Z_i\le\mu_i .
\]
Chebyshev and a union bound give
\[
 \Pr\{\exists i\in[55,405]:Z_i\le 2.14\cdot10^{52}\}
 \le\sum_{i=55}^{405}4/\mu_i<3.276\cdot10^{-50}.
 \tag{4}
\]
No independence across draws or conditional-on-history incidence law is used. Equation (4) charges a bad set under the original law. It also bounds its intersection with any crossing or gate; dividing by the probability of a crossing would give a different, conditional quantity.

## The remaining probability

Let \(D_i\) mean that **every** incident vector in the height-one family above has projected norm greater than \(1.15g_i\), using the actual frozen space. A long winner implies \(D_i\). Thus (4) still leaves a concrete joint event: at 36 or more draws the selected projections miss the target ball for *all* of these vectors. With \(G\) the simultaneous abundance event in (4), one sufficient, unproved estimate is
\[
 \max_{|I|=36,\ I\subseteq\{55,\dots,405\}}
 \Pr\!\left(G\cap\bigcap_{i\in I}D_i\right)\le 1.5204\cdot10^{-60}.
\]
Indeed multiplying by \(\binom{351}{36}\) and adding (4) and R94's \(4.659\cdot10^{-15}\) draw-55 exception fits the full \(2.72513\cdot10^{-11}\) crossing allowance. R94's count implication already covers draw 396 in this accounting. This target uses a union bound, and sufficiency allows sharper ways to aggregate the misses. The raw count estimates only \(G\). Controlling the projected misses, or the phases of the selected fibers in (2), is the missing probabilistic step.

## Interval verification

Run the embedded verifier from the existing scripts directory. It uses outward-rounded intervals at 70 decimal digits.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_frozen_contraction.md | python -B -)
```

```python
from math import comb
from mpmath import iv

iv.dps = 70
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
n, q = 506, 3329
V = [I(1), I(2)]
for j in range(2, 911):
    V.append(2 * iv.pi * V[j-2] / j)

log_det_raw = 400 * log(q)
a = I(505) / n
H = log(I('56.2142')) / 2 + log(V[n]) / n
u = log(I('34.807'))
for i in range(405, 54, -1):
    period, hermite = u + log(q)/n, (u + H/n)/a
    assert period < hermite or hermite < period
    u = min(period, hermite)
assert I('1672.375') < exp(u) < I('1672.376')
log_K55 = log_det_raw - log(V[n]) - n*u
assert sqrt(54)/2 * exp(log_K55/54) > I('2383.79')

log_K405 = log_det_raw - log(V[n]) - n*log(I('35.0743'))
assert log_K405/log(10) > I('1001.0959')
assert exp((log_K405-log(V[404]))/404) > I('1474.87')
assert (log(V[404])+404*log(250)-log_K405)/log(10) < I('-311.40')
assert exp(H)*I('35.0743')/250 < I('.192')
G910 = exp((log_det_raw-log(V[910]))/910)
rank_floor = 910*log(1474/(2*G910))/log(I(1474)/250)
assert I('536.17') < rank_floor < 537

d, R = 559, 2383
A = sqrt(R**2-1) - sqrt(d)/2
assert A > 1664
delta = 2*d*V[d-1]/V[d] * (1-(1664/A)**2)**(I(d-1)/2)
mu = (1-delta)*V[d]*A**d / q**400
assert delta < I('7.04e-79') and mu > I('4.2858e52')
assert mu/2 > I('2.14e52')
assert 351*4/mu < I('3.276e-50')
assert (comb(351,36)*I('1.5204e-60') + I('3.276e-50')
        + I('4.659e-15') < I('2.72513e-11'))
print('Verified frozen radii, independent directions, raw counts and crossing budget.')
```

## Audit

**Confirmed, with two scope clarifications.** The embedded interval verifiers for this note and Parts 222 and 225 all passed on rerun. An independent 90-digit calculation using log-gamma ball volumes and iterating the backward recurrence in the length scale reproduced the following values.

1. **Lift allowance.** The draw-406 endpoint gives the draw-55 upper scale \(1672.3752339148\ldots\) and the AM–GM lower bound \(2383.7956348654\ldots\) on \(B_{55}\). An earlier crossing in the stated range uses fewer iterations of the increasing backward map from the same endpoint, so the draw-406 estimate covers it as well. The lower bound concerns the nearest-plane allowance. The distance of the selected fiber from \(K\) in (2) can be smaller.
2. **Raw abundance and independence.** At draw 55 there are exactly 559 old coordinates. Keeping those coordinates at every later draw gives the same mean lower bound \(4.2858440308\ldots\times10^{52}\). Incidence independence here is **pairwise** for candidates with distinct inputs. Candidates with the same input and different centered outputs have nonpositive covariance. These facts suffice for the variance bound. The resulting upper bound on the 351-draw exceptional probability is \(3.2759008258\ldots\times10^{-50}\) under the original graph law. On its complement, choosing one vector per draw yields an identity minor on the 351 newest-coordinate rows, since each vector vanishes on all the other selected rows. This proves primitivity and linear independence for every such choice.
3. **Frozen covolume.** At each freeze, the shortest projected vector generates the lattice on its line. Its lift therefore generates the quotient of the enlarged frozen section by the old one. Zero extension preserves that section on the next append. Induction gives a basis with Gram–Schmidt lengths \(s_1,\ldots,s_{i-1}\), proving the exact covolume identity (1).
4. **Projection test.** The rank-\(k\) necessity applies specifically to a section certifying the short winner **by the projected Hermite determinant test**. Dividing its determinant threshold by the strict raw determinant floor gives \(J_F(S)<(1.15\cdot35.0743/250)^k=(0.16134178)^k\) on the stated draw-405 corridor and gate. Adding a frozen vector to a lift can decrease this ratio arbitrarily while preserving its projected section. Neither the ratio nor the raw abundance estimate supplies a probability bound for simultaneous projected misses. The proposed joint estimate would suffice, with total charge \(2.7249312981\ldots\times10^{-11}\) at the stated rounded allowances. That estimate and the crossing bound on draws 397–406 remain open.
