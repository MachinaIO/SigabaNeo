# Dual cusp escape (C1) and direction spread (DS) for the first pass

This note attacks the two one-step statements left open by [wall1_lyapunov](wall1_lyapunov.md) §7: (C1), dual cusp escape behind
the probabilistic GH cap κ = 1.05, and (DS), direction spread of the vertical winner. The setting is plain LWE
$(m,n,q)=(511,512,3329)$, CBD(3), the exact no-lookahead first pass of [Part 108](wall1_first_tour.md), width $b=506$, retained
rank $r=505$. By [Part 117](wall1_idea_round2.md) we work in the **restart experiment**: 400 horizontal and $105+t$ vertical
coordinates, all columns iid uniform in $(\mathbb Z/q)^{400}$ (coupling cost 0.00022304, paid once there). Write $N=505+t$ for the
ambient dimension after $t$ suffix appends.

**Verdict.** (C1) is **not** proved, and the note shows that the route suggested in wall1_lyapunov ("only inherited short dual
vectors matter, and the dual is monotone") cannot prove it. Results:

1. **Exact dual and mark structure (Theorem A, rigorous).** The preimage of the marked subgroup is $L_H=P_E\mathbb Z^N$. Its dual,
   $H^\perp=\mathbb Z^N\cap E$, is an integral lattice with minimum ≥ 1. The retained dual is $\Lambda^*=M^*\cap E$, where $M^*$ is the
   dual of the full q-ary lattice. Cosets of $\Lambda^*/H^\perp$ are labelled by $z\in(\mathbb Z/q)^{400}$. Characters are carried
   along the pass with their order. The vertical coordinate that a dual vector gains at an append is congruent to
   $-\langle z,a\rangle/q$ mod 1 (the **kick**). For $k\ge1$ the lift is unique and only lengthens. Every dual vector of norm < 1 is the
   lift-lineage of a unique restart dual vector. $\theta_{H_t^\perp}\le\theta_{\mathbb Z}^{\,r+h_t}$, where $h_t$ counts the horizontal winners.
2. **Exact one-step laws (Theorem B, rigorous).**
   * The shortest coset representative $\sigma(U)$ is uniform on a set $S$ of Voronoi-reduced representatives of $L_H/\Lambda$.
   * The k = 1 cap-failure probability is exactly $\#\{y\in S:|y|\ge\rho\}/|H|$.
   * The Theorem-5 ratio of wall1_lyapunov has an exact finite primal form, with no smoothing needed.
   * Its Haar-torus analogue equals $\sum_{\xi\in\Lambda^*\setminus0}\Lambda_{r/2}(2\pi\rho|\xi|)^2$ exactly (Parseval).
3. **Rigorous partial (C1): a path-uniform dual floor (Theorem C).** For **every** reducer that retains orthogonal projections,
   simultaneously for all $t\le407$ and outside probability $10^{-3}$, $\lambda_1(\Lambda_t^*)\ge R_0(t)$. Here $R_0(407)=0.2018$, which is
   about $0.25\,\mathrm{GH}(\Lambda_T^*)$. So the literal dual cusp (dual vectors below a quarter of the dual GH) is empty on a good set
   with explicit exit $10^{-3}$, and its share of the Fourier ratio vanishes there.
4. **Where the Fourier ratio actually lives (Proposition D, rigorous computation for Haar).** At the end of the pass,
   $\mathrm{GH}(\Lambda_T^*)\approx0.88<1$. So "inherited" (norm < 1) dual vectors are the Gaussian-heuristic bulk, not a cusp. In the
   Haar mean, dual vectors of norm < 1 carry $e^{-47.7}$ of a total $e^{-23.11}$. The whole ratio sits at norms 1–6, a range that
   inheritance does not control.
5. **Obstruction (Theorem E, rigorous).** Inheritance and kicks give exactly the bound $\Lambda_t^*\subseteq M_t^*$, and nothing more.
   For the Theorem-5 weight the expected $M_t^*$ sum is $+\infty$. For Gaussian majorants it exceeds the rank-505 Haar value by
   $e^{2320.8-203.5\log s}$, which is at least $e^{1628}$ on the relevant scale $s\le30$. The entire excess has to be removed by the
   **sections** $E_t=S_t^\perp$, whose directions are the selected SVP vectors. So (C1) is a statement about the selection law, the
   same wall as Parts 120–126.
6. **(DS) (Theorem F).**
   * Exact law: the winner's horizontal part, on k = 1, is uniform on the Voronoi-reduced representatives.
   * Rigorous anti-concentration against every dual hyperplane: $\Pr[|\langle\xi,v_h\rangle|<a]\le2a+1/o(\xi)$.
   * The density route to DS (a bound on the sup of the direction density) needs $M\ge\theta_{\rm cov}(\Lambda)$. By Coxeter–Few–Rogers,
     $\theta_{\rm cov}\gtrsim r/e^{3/2}\approx113$ on every lattice, so this route can never reach the $M<3.86$ that Proposition 6 needs.
   * DS reduces to a non-alignment statement between deep holes and near-minimal vectors (Conjecture DS′), again a statement about
     the law.

What remains is stated in §7 as Conjectures C1′ and DS′.

## 0. Setting and notation

All of the following is re-derived from Part 108 and wall1_lyapunov.

**Lattices and subspaces.**
* $F_t$ is the real span of the processed columns.
* $M_t=\{(x,y)\in\mathbb Z^{400}\times\mathbb Z^{105+t}:\ x\equiv Ay\pmod q\}$, with $A=(a_1,\dots,a_{105+t})$ uniform.
* $S_t$ is the span of the frozen (selected) vectors, and $E_t=F_t\cap S_t^\perp$, with $\dim E_t=r$.
* $\Lambda_t=P_{E_t}M_t$, with determinant $D_t$.

**The mark.** $H_t$ is the image of $(\mathbb Z/q)^{400}\to E_t/\Lambda_t$, $z\mapsto[P(z,0)]$. The next displacement $U$ is uniform on
$H_t$ given the past.

**The window.**
* $W=\Lambda+\mathbb Z(\tilde U+e)$.
* The winner is $v=\lambda+k(\tilde U+e)$ with $k\ge0$ and $v_h=\lambda+k\tilde U$.
* $s=|v|$, $\Lambda'=Q_vW$ and $H'=(Q_v)_*H$.

**Constants.**
* $G_j=V_j^{-1/j}$, so $G_{505}=5.47744$ and $G_{506}=5.48279$.
* The cap is $s\le\kappa G_bD^{1/b}$, and $\rho^2=\kappa^2G_b^2D^{2/b}-1$.
* At the end of the κ = 1.05 trajectory ($h_T=34.0992$): $\rho=35.696=1.04682\,\mathrm{GH}(\Lambda)$ and $(\rho/\mathrm{GH})^r=e^{23.109}$.
* $\Lambda_\nu(z)=\Gamma(\nu+1)(2/z)^\nu J_\nu(z)$ is the normalized Fourier transform of the unit ball in dimension $2\nu$. Here
  $\nu=r/2$.

(C1) asks for a bound on $\sum_t\mathbb E\min(1,\varepsilon_t)$, where $\varepsilon_t$ bounds $\Pr_U[s_t>\kappa G_bD_{t-1}^{1/b}]$ and is
taken to be 0 when $\lambda_1(\Lambda_{t-1})$ is below the cap.

## 1. Exact dual and mark structure

**Theorem A.** At every time $t$ of the restart experiment, on every history:

* **(A1)** $L_H:=\Lambda+\sum_{h\in H}\mathbb Z\tilde h=P_E(\mathbb Z^N)$. Hence $|H|=[L_H:\Lambda]$, and $\operatorname{covol}L_H=D/|H|\le1$.
* **(A2)** $H^\perp:=\{\xi\in\Lambda^*:\langle\xi,h\rangle\in\mathbb Z\ \forall h\in H\}=L_H^*=\mathbb Z^N\cap E$. It is an integral lattice
  that is saturated in $\mathbb Z^N$, and $\lambda_1(H^\perp)\ge1$. In particular **every nonzero dual vector of norm < 1 induces a
  nontrivial character of H.**
* **(A3)** $\Lambda^*=M^*\cap E$, where $M^*=\mathbb Z^N+q^{-1}\{(z,-A^{\top}z):z\in\mathbb Z^{400}\}$, i.e.
  $qM^*=\{(u,w)\in\mathbb Z^N: w\equiv-A^{\top}u\bmod q\}$.
  * The **label** $\ell(\xi)=q\cdot(\text{horizontal part of }\xi)\bmod q\in(\mathbb Z/q)^{400}$ is a homomorphism on $\Lambda^*$ with
    kernel $H^\perp$. So $\Lambda^*/H^\perp\hookrightarrow(\mathbb Z/q)^{400}$ and $[\Lambda^*:H^\perp]=|H|$.
  * The character of ξ is $\chi_\xi(P(a,0))=\langle\ell(\xi),a\rangle/q\bmod1$.
* **(A4) Lift formula.** $\Lambda'^*=W^*\cap v^\perp$ with $W^*=\{(\xi,\,j-\langle\xi,\tilde U\rangle):\xi\in\Lambda^*,j\in\mathbb Z\}$.
  Explicitly:
  * if $k\ge1$: $\Lambda'^*=\{(\xi,-\langle\xi,v_h\rangle/k):\ \xi\in\Lambda^*,\ k\mid\langle\xi,\lambda\rangle\}$, and $(\xi,t)\mapsto\xi$ is
    injective;
  * if $k=0$: $\Lambda'^*=\{(\xi,j-\langle\xi,\tilde U\rangle):\ \xi\in\Lambda^*\cap x_0^\perp,\ j\in\mathbb Z\}$.
* **(A5) Kick.** Every $(\xi,t)\in\Lambda'^*$ has $t\equiv-\chi_\xi(U)\pmod1$. Hence $|(\xi,t)|^2\ge|\xi|^2+\|\chi_\xi(U)\|_{\mathbb R/\mathbb Z}^2$.
  This holds whatever vector the reducer selects.
* **(A6) Character transport.** If $\xi'=(\xi,t)\in\Lambda'^*$, then $\chi_{\xi'}\circ Q_*=\chi_\xi$ on $H$, and $\ell(\xi')=\ell(\xi)$. Since
  $Q_*:H\to H'$ is onto, $\xi'$ has the same order $o(\xi)$ as ξ.
* **(A7) Lineage.** Every $\xi_t\in\Lambda_t^*$ with $|\xi_t|<1$ determines a unique chain $\xi_0,\xi_1,\dots,\xi_t$ with
  $\xi_i\in\Lambda_i^*$, $\xi_{i}=(\xi_{i-1},t_i)$, all with the same label. Along it
  $$|\xi_t|^2=|\xi_0|^2+\sum_{i\le t}t_i^2,\qquad t_i\equiv-\langle\ell,a_{105+i}\rangle/q\pmod 1 .$$
  So every dual vector shorter than 1 at any time is inherited from the restart dual $\Lambda_0^*$.
* **(A8) Theta monotonicity of $H^\perp$.** For every $s>0$, $\theta_{H'^\perp}(s)\le\theta_{H^\perp}(s)$ after a step with $k\ge1$, and
  $\theta_{H'^\perp}(s)\le\theta_{H^\perp}(s)\theta_{\mathbb Z}(s)$ after a step with $k=0$. Since $H_0^\perp=\mathbb Z^{505}$,
  $$\theta_{H_t^\perp}(s)\le\theta_{\mathbb Z}(s)^{\,505+h_t},\qquad h_t=\#\{i\le t:\ k_i=0\}.$$
  For counts in balls the same argument gives $N_x(H'^\perp)\le N_x(H^\perp)$ when $k\ge1$, and
  $N_x(H'^\perp)\le\sum_{|j|\le x}N_{\sqrt{x^2-j^2}}(H^\perp\cup\{0\})$ when $k=0$.

*Proof.*

(A1) $H$ is generated by the classes of $P(e_i,0)$ for $i\le400$, so $L_H=P(M_t+\mathbb Z^{400}\oplus0)$. Now
$M_t+\mathbb Z^{400}\oplus0=\mathbb Z^N$, because the graph columns $(a_j,e_j)$ together with $\mathbb Z^{400}$ generate the vertical unit
vectors. The covolume of a projection of $\mathbb Z^N$ onto a rational subspace is $1/\det(\mathbb Z^N\cap E)\le1$.

(A2) For any lattice $L$ and any subspace $E$ with $P_EL$ discrete, $(P_EL)^*=L^*\cap E$: for ξ ∈ E,
$\langle\xi,P_Ex\rangle=\langle\xi,x\rangle$. Apply this with $L=\mathbb Z^N$. Nonzero integer vectors have norm ≥ 1. The equality
$H^\perp=L_H^*$ holds because pairing integrally with Λ and with every $\tilde h$ is the same as pairing integrally with $L_H$.
Saturation: $\mathbb Z^N\cap E$ is the full intersection.

(A3) $\Lambda^*=(P_EM)^*=M^*\cap E$, by the same identity. $M^*$ is computed directly: $(u,w)$ pairs integrally with
$\{x\equiv Ay\}$ exactly when $(u,w)\in\mathbb Z^N+q^{-1}(z,-A^{\top}z)$. The label is well defined because the horizontal part is
$z/q+\mathbb Z^{400}$. It vanishes iff $z\equiv0$, iff ξ is an integer vector, iff $\xi\in\mathbb Z^N\cap E=H^\perp$. Finally,
$\langle\xi,P(a,0)\rangle=\langle\xi,(a,0)\rangle\equiv\langle z,a\rangle/q$, because ξ ∈ E and its vertical part pairs with 0.

(A4) $v$ is primitive in $W$, so $(Q_vW)^*=W^*\cap v^\perp$. The description of $W^*$ is wall1_lyapunov Theorem 4(d), re-derived:
$(\xi,\tau)$ pairs integrally with Λ and with $\tilde U+e$ iff ξ ∈ Λ* and $\tau+\langle\xi,\tilde U\rangle\in\mathbb Z$.
* For $v=(\lambda+k\tilde U,k)$, orthogonality reads $\langle\xi,\lambda\rangle+k\langle\xi,\tilde U\rangle+k\tau=0$. With
  $\tau=j-\langle\xi,\tilde U\rangle$ this is $\langle\xi,\lambda\rangle+kj=0$. For $k\ge1$ it forces $j=-\langle\xi,\lambda\rangle/k\in\mathbb Z$ and
  $\tau=-\langle\xi,v_h\rangle/k$, unique given ξ.
* For $k=0$, $v=x_0\in\Lambda$, the condition is $\langle\xi,x_0\rangle=0$, and $j$ is free.

(A5) This is immediate from $\tau=j-\langle\xi,\tilde U\rangle$. Note that $\langle\xi,\tilde U\rangle\equiv\chi_\xi(U)$.

(A6) For $h\in H$ with representative $\tilde h\in E$, $Q_v\tilde h=\tilde h-(\langle\tilde h,v\rangle/s^2)v$. Since $\xi'\perp v$,
$\langle\xi',Q_v\tilde h\rangle=\langle\xi',\tilde h\rangle=\langle\xi,\tilde h\rangle$, because $\tilde h$ has zero $e$-component. The
horizontal coordinates of ξ′ and ξ agree, so the labels agree.

(A7) By (A4), every $\xi_i\in\Lambda_i^*$ is $(\xi_{i-1},t_i)$ with $\xi_{i-1}\in\Lambda_{i-1}^*$: delete the last coordinate. So the chain
exists and is unique. Norms do not increase backwards, labels are constant by (A6), and the congruence for $t_i$ is (A5) combined
with (A3). A chain whose final norm is < 1 has all norms < 1, so in particular $\xi_0\in\Lambda_0^*$ has norm < 1.

(A8) By (A6), $\chi_{\xi'}$ is trivial iff $\chi_\xi$ is, so $H'^\perp$ consists of the lifts of $H^\perp$.
* For $k\ge1$ the lift map is injective and does not decrease norms. Summing $e^{-\pi s|\cdot|^2}$ gives the first inequality.
* For $k=0$ and $\xi\in H^\perp$, $\langle\xi,\tilde U\rangle\in\mathbb Z$, so the lifts are $(\xi,j)$ with $j\in\mathbb Z$. Then
  $H'^\perp=(H^\perp\cap x_0^\perp)\oplus\mathbb Ze$, and $\theta\le\theta_{H^\perp}\theta_{\mathbb Z}$.
* At the restart, $E_0=\mathbb R^{505}$ and $H_0^\perp=\mathbb Z^{505}$. ∎

*Remarks.*
* (A2)+(A3) make precise what wall1_lyapunov calls "short dual vectors". The cosets $c\ne0$ in Theorem 5 are exactly the nonzero
  labels. The zero coset $H^\perp$ is integral, and its count is controlled pathwise by (A8).
* (A5)/(A7) say that the kicks a dual lineage receives are its $M^*$ coordinates. As §5 shows, this is the entire content of
  "inheritance".

## 2. Exact one-step laws

For $u\in H$ let $\sigma(u)$ be the shortest element of $\tilde u+\Lambda$, ties broken by the fixed rule. Put $S=\sigma(H)$.

**Theorem B.** Fix a reachable state $(\Lambda,H)$.

* **(B1) Voronoi-uniform law.** σ is injective, and $S\subset L_H\cap\bar{\mathcal V}(\Lambda)$ contains exactly one point of every coset of
  Λ in $L_H$. Here $\mathcal V$ is the Voronoi cell. So **$\sigma(U)$ is uniform on S.** On $\{k=1\}$ the winner is
  $v=(\sigma(U),1)$, so $v_h$ is uniform on $S\cap\{k=1\}$.
* **(B2) Cap failure.** For $\rho^2=\kappa^2G_b^2D^{2/b}-1$:
  $$\Pr_U\big[s>\kappa G_bD^{1/b}\big]\ \le\ \mathbf 1\{\lambda_1(\Lambda)>\kappa G_bD^{1/b}\}\cdot\frac{\#\{y\in S:\ |y|\ge\rho\}}{|H|}.$$
  The k = 1 part is an equality: the event "$s>\sqrt{1+\rho^2}$ via layer 1" is exactly $\{|\sigma(U)|\ge\rho\}$.
* **(B3) Exact primal form of the Theorem-5 ratio.** Take $\varphi=\mathbf 1_{B_\rho}$ (open ball) and $P(u)=\#\{\mu\in\Lambda:|\tilde u+\mu|<\rho\}$.
  All sums are finite, so no smoothing is needed:
  $$\mathbb E_HP=\frac{\#(L_H\cap B_\rho)}{|H|},\qquad
  \varepsilon_H:=\frac{\operatorname{Var}_HP}{(\mathbb E_HP)^2}=\frac{|H|\sum_{\mu\in\Lambda}\#\{y\in L_H:\ |y|<\rho,\ |y+\mu|<\rho\}}{\#(L_H\cap B_\rho)^2}-1 .$$
  By Chebyshev, $\Pr_U[|\sigma(U)|\ge\rho]\le\varepsilon_H$.
* **(B4) Torus analogue (Parseval).** For $U$ Haar on $E/\Lambda$:
  $$\varepsilon_T(\Lambda):=\frac{\operatorname{Var}_TP}{(\mathbb E_TP)^2}=\sum_{\xi\in\Lambda^*\setminus0}\Lambda_{r/2}(2\pi\rho|\xi|)^2
  =\frac{D}{\operatorname{vol}B_\rho^2}\sum_{\mu\in\Lambda}\operatorname{vol}\big(B_\rho\cap(B_\rho-\mu)\big)-1 .$$
  For a Haar-random Λ of covolume D, $\mathbb E\,\varepsilon_T=D/\operatorname{vol}B_\rho=(\mathrm{GH}/\rho)^r$, which is $e^{-23.109}$ at the end
  of the κ = 1.05 trajectory.

*Proof.*

(B1) Distinct cosets have distinct shortest elements. The shortest element $y$ of a coset satisfies $|y|\le|y-\mu|$ for all
$\mu\in\Lambda$, i.e. $y\in\bar{\mathcal V}$. Uniformity of $U$ on $H$ transfers through the bijection $H\to S$. On $k=1$ the winner is
$\lambda+\tilde U+e$ with $\lambda+\tilde U$ shortest in its coset; a shorter element would give a shorter layer-one vector.

(B2) If $\lambda_1(\Lambda)\le$ cap, then $s\le\lambda_1(\Lambda)\le$ cap. Otherwise the layer-one vector $(\sigma(U),1)$ has length
$\sqrt{1+|\sigma(U)|^2}$, which is below the cap iff $|\sigma(U)|<\rho$.

(B3) $\sum_{u\in H}P(u)=\#(L_H\cap B_\rho)$, because $\{\tilde u+\mu\}$ runs over $L_H$ exactly once. Likewise
$\sum_uP(u)^2=\sum_{y\in L_H\cap B}\#\{\mu:|y+\mu|<\rho\}$. If $P(U)=0$ the coset misses the ball, so $|\sigma(U)|\ge\rho$;
Chebyshev bounds $\Pr[P=0]$.

(B4) $P\in L^2(E/\Lambda)$ has Fourier coefficients $D^{-1}\hat{\mathbf 1}_B(\xi)$, $\xi\in\Lambda^*$, and Parseval holds for every
$L^2$ function. The primal form is $\mathbb E_TP^2=D^{-1}\int\mathbf 1_B(x)\sum_\mu\mathbf 1_B(x+\mu)\,dx$. For Haar Λ, Λ* is Haar of
covolume $1/D$. Siegel's mean value theorem and Plancherel give
$\mathbb E\sum_{\xi\ne0}|\hat{\mathbf 1}_B(\xi)|^2=D\int|\hat{\mathbf 1}_B|^2=D\operatorname{vol}B$. ∎

*Comparison with wall1_lyapunov Theorem 5.*
* The variance formula there, $D^{-2}\sum_{c\ne0}|\sum_{\xi\in c}\hat\varphi(\xi)|^2$, is correct (re-derived by character
  orthogonality). By (A3), $c$ runs over nonzero labels.
* (B3) is the same quantity in primal form. It shows that Theorem 5 is a statement about **primal** short vectors μ of Λ with
  $|\mu|<2\rho$ and about counts of the fine lattice $L_H$ in lenses. Dual vectors enter only through Poisson summation.
* (B1)–(B2) give the **exact** cap-failure probability as a lattice-point count in the Voronoi cell. The Chebyshev step is then
  only a convenient upper bound.

## 3. Rigorous partial (C1): a path-uniform dual floor

**Theorem C.** Let $n'=105+t$ and $N=400+n'$. For $0<R<1$,
$$\mathbb E_A\,\#\{\xi\in M_t^*:\ 0<|\xi|<R\}\ \le\ q^{-n'}\,\#\big(\mathbb Z^{N}\cap B_{qR}\big)\ \le\ q^{-n'}V_N\big(qR+\sqrt N/2\big)^N=:\beta_t(R).$$
Define $R_0(t)$ by $\beta_t(R_0(t))=10^{-3}/408$. Then, for **any** reducer whose retained lattice is $P_{E_t}M_t$ for some
subspaces $E_t$ (in particular for the Part 108 pass, with any tie rule):
$$\Pr\big[\exists\,t\le407:\ \lambda_1(\Lambda_t^*)<R_0(t)\big]\le10^{-3}.$$

| $t$ | 0 | 50 | 100 | 200 | 300 | 407 |
|---|---:|---:|---:|---:|---:|---:|
| $R_0(t)$ | 0.005285 | 0.01268 | 0.02380 | 0.05966 | 0.1164 | 0.2018 |
| $\mathrm{GH}(M_t^*)$ | 0.008884 | 0.01660 | 0.02809 | 0.06483 | 0.1226 | 0.2093 |
| $\mathrm{GH}(\Lambda_t^*)$ on the κ = 1.05 path | 0.008884 | 0.01919 | 0.03855 | 0.1286 | 0.3454 | 0.8176 |
| $R_0/\mathrm{GH}(\Lambda_t^*)$ | 0.595 | 0.661 | 0.617 | 0.464 | 0.337 | 0.247 |

The orientation row uses the restart trajectory $s_t=\min(q,\kappa G_bD_{t-1}^{1/b})$ from $D_0=q^{400}$, which ends at
$\mathrm{GH}(\Lambda_T)\approx36.7$. Sections 4, 5 and 7 use instead wall1_lyapunov's worst-case floor $h_T=34.0992$, i.e.
$\mathrm{GH}(\Lambda_T^*)=0.8799$. The difference does not affect any conclusion.

*Proof.* By (A3), $\Lambda_t^*=M_t^*\cap E_t\subseteq M_t^*$ on every history. $M_t^*$ is a function of $A$ alone.

A vector $\xi=q^{-1}(u,w)\in M_t^*$ with $u\equiv0\pmod q$ has $w\equiv0$ too, so it is an integer vector of norm ≥ 1 or zero. For a
fixed $(u,w)\in\mathbb Z^N$ with $u\not\equiv0$, the event $w\equiv-A^{\top}u$ has probability exactly $q^{-n'}$: the columns $a_j$ are
independent and uniform, and $\langle a_j,u\rangle$ is uniform mod the prime q. Summing over $|(u,w)|<qR$ gives the first bound.
The second bound puts a unit cube around each lattice point; every such cube lies in $B_{qR+\sqrt N/2}$.

Markov's inequality and a union bound over the 408 times finish the proof. In the restart experiment all $105+407$ columns are iid
uniform (Part 117). ∎

*Consequences.*
* On the good set of Theorem C, every nonzero coset c of $\Lambda_t^*/H_t^\perp$ has minimal norm ≥ $R_0(t)$. So in Theorem 5 and
  (B4), the terms with $|\xi|<R_0$ are absent, and the exit is charged $10^{-3}$, as in wall1_lyapunov Theorem 1(b).
* Together with wall1_lyapunov Theorem 4(d) (normalized dual minima shrink by at most $s^{-1/r}$ per step), this is the full
  rigorous content of "dual cusp escape": **no dual vector below ≈ ¼ of the dual GH at any time of the pass, outside $10^{-3}$.**
* The bound does not depend on the reducer, so it is equally valid for the zero-draw kernel of wall1_lyapunov Theorem 3. This is
  consistent with that theorem: a dual floor alone cannot bound δ.

## 4. Where the Fourier ratio lives

**Proposition D.** At the end of the κ = 1.05 trajectory ($\rho=35.696$, $\mathrm{GH}(\Lambda^*)=0.8799$ in the cap-floor
normalization), the Haar mean $\mathbb E\,\varepsilon_T=e^{-23.109}$ of (B4) splits by dual norm as follows (computed by quadrature
of $D\int\Lambda_{r/2}(2\pi\rho|x|)^2dx$ over shells):

| $|\xi|$ | (0.01, 0.5) | (0.5, 1) | (1, 1.5) | (1.5, 2) | (2, 2.5) | (2.5, 3) | (3, 4) | (4, 6) | (6, ∞) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| log contribution | −310.8 | −47.7 | −23.9 | −24.9 | −25.6 | −26.1 | −25.9 | −25.9 | rest |

The total up to norm 6 is $e^{-23.24}$. The remainder up to $e^{-23.11}$ is the slowly decaying sharp-boundary tail
($\Lambda_\nu^2\sim z^{-(r+1)}$ on average).

*Reading.*
1. A typical dual vector of $\Lambda_T^*$ has norm about 0.88 < 1. So by (A7), the inherited class (norm < 1) is **the bulk of the
   dual**, about $e^{65}$ vectors, not a cusp. The statement "the danger is only inherited short dual vectors" (wall1_lyapunov §5,
   §7) is true but vacuous.
2. In the Haar mean, norms below 1 contribute $e^{-47.7}$. Even an excess of $e^{30}$ over Haar in that range would be harmless at the per-step target $e^{-14}$ of §7.
   The ratio is carried by norms 1–6 and beyond (equivalently, by primal lens counts at $|\mu|\approx\sqrt2\rho$; see (B4)). For
   those, (A5)/(A7) say nothing, because vectors of norm ≥ 1 can be newly created by horizontal steps ($e$ itself) and are not
   inherited.
3. Per vector, $|\Lambda_\nu(2\pi\rho)|=e^{-56.6}$ at norm 1. So wall1_lyapunov's "less than $e^{-37}$ each" is correct as stated,
   but at norms 1–2 such vectors number between $e^{150}$ and $e^{400}$, and together they make up the whole ratio.

## 5. Obstruction: inheritance is the q-ary dual, and the gap is at least $e^{1600}$

**Theorem E.**
* **(E1)** For every radial $w\ge0$ and every history, $\sum_{\xi\in\Lambda_t^*\setminus0}w(\xi)\le\sum_{\xi\in M_t^*\setminus0}w(\xi)$. The
  inheritance and kick facts (A4)–(A7) carry no further information (interpretation, made precise by the next sentence): by (A7) the kick sequence of a lineage with label ℓ is exactly
  the vertical coordinate sequence of the $M_t^*$ vectors with that label. Together with the horizontal part $\ell/q+\mathbb Z^{400}$
  (fixed at the restart), these sequences enumerate $M_t^*$. What separates $\Lambda_t^*$ from $M_t^*$ is only the section
  $E_t=F_t\cap S_t^\perp$, i.e. the orthogonality conditions $\langle\xi,f\rangle=0$ for the frozen SVP vectors f.
* **(E2)** For $w=\Lambda_{r/2}(2\pi\rho|\cdot|)^2$ (the Theorem-5/(B4) weight), $\sum_{\xi\in M_t^*}w(\xi)=+\infty$ for every A and every
  $t\ge2$. In contrast, $\sum_{\Lambda_t^*}w<\infty$ on every history.
* **(E3)** For Gaussian weights $w_s=e^{-\pi s|\xi|^2}$, in restart coordinates ($N=400+105+407=912$ at $T=407$):
  $$\frac{\mathbb E_A\sum_{M_T^*\setminus\mathbb Z^N}w_s}{D_T\,s^{-r/2}}=(1+o(1))\,\frac{q^{400}}{D_T}\,s^{-(N-r)/2}=e^{2320.8-203.5\log s}$$
  (with $D_T$ from the κ-cap floor $h_T=34.0992$). This is at least $e^{1628}$ for $s\le30$ and at least $e^{1383}$ for $s\le100$. The
  denominator is the rank-505 Haar value with the same covolume.
* **(E4) The sections carry exactly the gap.** $\det(\Lambda_t^*)=\det(M_t^*)\cdot\det(M_t\cap S_t)=q^{-400}\cdot q^{400}/D_t$. So the
  frozen lattice $M_t\cap S_t$, spanned by the selected vectors and with covolume $q^{400}/D_t\approx e^{2320.8}$ at T on the κ-path,
  is what turns the q-ary dual into the retained dual. It is determined by the selections.

*Proof.*
* (E1) Inclusion is (A3). The identification of kicks with $M^*$ coordinates is (A3)+(A7).
* (E2) $M_t^*$ has full rank $N>r+1$ in $\mathbb R^N$. $\Lambda_\nu(z)^2$ has mean order $z^{-(r+1)}$ along $z\to\infty$, because
  $J_\nu(z)^2$ averages to $1/(\pi z)$ over each period. Lattice-point counts in annuli of width ≪ $1/\rho$ at radius x are
  $\asymp$ volume with error $O(x^{N-2})$ ($N\ge5$), so the oscillation averages out, and the sum behaves like $\int^\infty x^{N-1}x^{-(r+1)}dx=\infty$. On the rank-r lattice
  $\Lambda_t^*$ the analogous integral converges.
* (E3) By the computation in Theorem C,
  $\mathbb E_A\sum=q^{-n'}\sum_{(u,w)\in\mathbb Z^N,u\not\equiv0}e^{-\pi s|(u,w)|^2/q^2}=q^{-n'}(q^2/s)^{N/2}(1+O(e^{-\pi q^2/s}))$
  by Poisson. Numerics as stated.
* (E4) For a primitive sublattice $K=M\cap S$, $(M^*\cap S^\perp)$ is the dual of $P_{S^\perp}M$, and
  $\det P_{S^\perp}M=\det M/\det K$. Here $\det M_t=q^{400}$. ∎

*Consequence.* Any proof of (C1) must show that the selected directions $S_t$ cut the q-ary dual down to a Haar-like rank-505
section, within a factor of about $e^{9}$ on the weighted count at norms 1–6 (Proposition D, together with the per-step target
$\varepsilon\le e^{-14}$ of §7). This is a statement about the joint law of the SVP selections, of exactly the type that Parts 120–126
and wall1_lyapunov Theorem 3 identify as open. Dual monotonicity (wall1_lyapunov 4(d)) gives only that normalized dual lengths
shrink by at most $s^{-1/r}$ per step. On the weight $w$, that allows growth by $e^{3.4}$ per step from the radius normalization
alone (heuristic scaling: $505\log(1/0.99329)$), or about $e^{1380}$ over 407 steps.

## 6. Direction spread (DS)

Recall (DS$_M$) from wall1_lyapunov Proposition 6. For each near-minimal rank-i sublattice Δ,
$\mathbb E[g_\Delta(\hat v_h)\mid x,k=1]\le M\,\mathbb E_{\rm unif}[g_\Delta]$, where $g_\Delta=(1-|P_\Delta\hat v|^2)^{-p/2}$. The vertical-branch
contraction there is $\le0.259M$ at θ = 1/2, s = 30, so the branch contracts iff $M<3.86$.

**Theorem F.** Fix a reachable state, and let $p_1=\Pr_U[k=1]$.

* **(F1) Exact law.** Conditional on $k=1$, $v_h$ is uniform on $S_1:=\{\sigma(u):k(u)=1\}\subseteq L_H\cap\bar{\mathcal V}(\Lambda)$. So, exactly,
  $$\mathbb E[g(\hat v_h)\mid k=1]=\frac1{|S_1|}\sum_{y\in S_1}g(\hat y).$$
* **(F2) Anti-concentration against dual hyperplanes (pathwise, every reachable state).** For every $\xi\in\Lambda^*\setminus H^\perp$ of
  order $o=o(\xi)$ and every $0<a\le1/2$:
  $$\Pr_U\big[|\langle\xi,\sigma(U)\rangle|<a\big]\le\frac{2\lceil ao\rceil-1}{o}\le2a+\frac1o,\qquad
  \Pr\big[|\langle\xi,v_h\rangle|<a\ \big|\ k=1\big]\le\frac{2a+1/o}{p_1}.$$
  By (A2), this applies to **every** ξ with $|\xi|<1$.
* **(F3) The density route is impossible.** Replace $\sigma(U)$ by a uniform point of $\mathcal V(\Lambda)$ (the continuous model). Its
  direction has density $f(\theta)=V_rR(\theta)^r/D$ with respect to the isotropic law, where R is the radial function of $\mathcal V$, and
  $\sup f=\theta_{\rm cov}(\Lambda):=V_r\mu(\Lambda)^r/D$. So DS$_M$ for **all** test functions holds iff $M\ge\theta_{\rm cov}$ (before
  conditioning on k = 1, which can only raise the requirement). By Coxeter–Few–Rogers, $\theta_{\rm cov}\ge\tau_r\sim r/e^{3/2}$, which
  is ≈ 113 at r = 505. That exceeds 3.86 by a factor of about 29, so the uniform version of DS fails for **every** lattice.
  * In the exact discrete model, the law (F1) is atomic, so it has no density at all. This matches wall1_lyapunov Theorem 3.
  * DS can therefore hold only for the specific weights $g_\Delta$.
* **(F4) Reduction for i = 1.** Let $\Delta=\mathbb Zx$ and $c=\cos^2\angle(\theta,x)$. In the continuous model,
  $\mathbb E[g_\Delta]=\mathbb E_{\rm unif}[g_\Delta f]$, with $\mathbb E_{\rm unif}f=1$ and the Voronoi constraint
  $$f(\theta)\le\min\Big(\theta_{\rm cov},\ \big(|x|/(2\sqrt c\,\mathrm{GH}(\Lambda))\big)^r\Big).$$
  Hence, in the continuous model and before conditioning on k = 1, DS$_M$ for this Δ is equivalent to $\mathbb E_{\tilde\nu}[f]\le M$, where $\tilde\nu$ is the $g_\Delta$-tilted direction law, under which
  $c\sim\mathrm{Beta}(\tfrac12,\tfrac{r-1-p}2)$. The Voronoi constraint settles the range $c\ge(|x|/2\mathrm{GH})^2\approx1/4$, which has
  tilted mass below $e^{-30}$ at p = r/2. The range $c\in[c_0,1/4]$, with $c_0\approx(r-p)^{-1}$, is not controlled by any pathwise
  fact. There the bound $f\le\theta_{\rm cov}$ loses the factor ≥ 113.

*Proof.*
* (F1) This is (B1).
* (F2) By (A5)/(B1), $\langle\xi,\sigma(U)\rangle\equiv\chi_\xi(U)\pmod1$. Moreover $\chi_\xi:H\to o^{-1}\mathbb Z/\mathbb Z$ is onto, so
  $\chi_\xi(U)$ is uniform there. Then $|\langle\xi,\sigma(U)\rangle|\ge\|\chi_\xi(U)\|$, and $\#\{j\in\mathbb Z/o:\|j/o\|<a\}=2\lceil ao\rceil-1$
  for $a\le1/2$. Conditioning on an event of probability $p_1$ multiplies probabilities by at most $1/p_1$.
* (F3) For x uniform on the star-shaped body $\mathcal V$, the direction density is
  $r\int_0^{R(\theta)}\rho^{r-1}d\rho/\operatorname{vol}\mathcal V$ times the normalized surface measure, which is $V_rR^r/D$. The sup of R is the
  covering radius μ. The Coxeter–Few–Rogers lower bound on the density of any covering of $\mathbb R^r$ by equal balls applies to the
  lattice covering by $B_\mu$; we use the asymptotic form from the literature, not re-verified here.
* (F4) If $x\in\Lambda$, the Voronoi inequality $\langle y,x\rangle\le|x|^2/2$ gives $R(\theta)\sqrt c\le|x|/2$. The tilted law follows from
  $c\sim\mathrm{Beta}(\tfrac12,\tfrac{r-1}2)$ under the uniform law and $g=(1-c)^{-p/2}$. ∎

So (F2) is the strongest **pathwise** direction statement, and it is a statement about dual hyperplanes. But g_Δ concerns
closeness to **primal** sublattices, and (F2) does not reach it. DS needs Conjecture DS′ (§7).

## 7. The remaining gap, stated exactly

Put $c_t=\kappa G_bD_{t-1}^{1/b}$ and $\rho_t^2=c_t^2-1$. By (B2) and wall1_lyapunov Corollary 5.1, the GH floor 34.0992 (κ = 1.05,
ratio target 0.8052) fails with probability at most
$$10^{-3}\ (\text{Theorem C exit})\ +\ \sum_{t=1}^{407}\mathbb E\Big[\mathbf 1_{G_{t-1}}\,\mathbf 1\{\lambda_1(\Lambda_{t-1})>c_t\}\,
\frac{\#\{y\in S_{t-1}:|y|\ge\rho_t\}}{|H_{t-1}|}\Big],$$
where $G_t$ is "cap held so far and Theorem C's floor holds". Every quantity here is exact. What is missing is the following.

**Conjecture C1′ (Haar comparison of the retained lattice at the cap scale).** On reachable states in $G_{t-1}$ with
$\lambda_1(\Lambda_{t-1})>c_t$:

* (a) $\varepsilon_T(\Lambda_{t-1})\le e^{-14}$, i.e. within $e^{9.1}$ of its Haar mean $(\mathrm{GH}/\rho_t)^r\approx e^{-23.1}$. Equivalently,
  the weighted dual count $\sum_{\xi\in\Lambda^*\setminus0}\Lambda_{r/2}(2\pi\rho|\xi|)^2$, in which the terms with $|\xi|<R_0$ are absent on
  $G_{t-1}$, is at most $e^{-14}$. Equivalently again, by (B4), the lens-weighted primal count $\sum_{\mu\ne0}\operatorname{vol}(B\cap(B-\mu))$
  exceeds $\operatorname{vol}B^2/D$ by a relative error of at most $e^{-14}$.
* (b) $\big|\#\{y\in S:|y|\ge\rho\}/|H|-\Pr_T[\operatorname{dist}(U,\Lambda)\ge\rho]\big|\le e^{-14}$. That is, the fine lattice $L_H=P_E\mathbb Z^N$
  is equidistributed in $\mathcal V(\Lambda)\setminus B_\rho$ relative to $\mathcal V(\Lambda)$, to that precision.

**Proposition (C1′ ⇒ C1).** Under C1′, Chebyshev on the torus gives $\Pr_T[\text{miss}]\le\varepsilon_T\le e^{-14}$, and (b) transfers this
to the true law. Hence the displayed sum is at most $407\cdot2e^{-14}=6.8\cdot10^{-4}$, and the GH floor 34.0992 fails with
probability at most $1.7\cdot10^{-3}$ (plus Part 117's 0.00022304). This is (C1) with $\eta_1\le1.7\cdot10^{-3}$.

Unlike a quantile statement, (a) is a one-sided bound on a positive weighted count, with an $e^{9}$ margin over the Haar mean.

**Why (b) is not closed by (A8).** Counting $L_H$ in a sharp ball of radius ≈ 35 in dimension 505 by Poisson summation requires a
mollifier. With only the pathwise bound $\theta_{H^\perp}\le\theta_{\mathbb Z}^{505+h_t}$ on the dual side, the shell counts of
$H^\perp$ grow like those of $\mathbb Z^{505+h_t}$, i.e. $x^{505+h_t}$. The ball transform decays only like $x^{-253}$. The mollifier must
take over from $|\eta|\approx35$, which forces its radius to be ε ≳ 2.3. That costs a factor $(1-\varepsilon/\rho)^{505}\approx e^{-33}$ in
the mean, more than the $e^{23}$ margin. So (b) needs a non-Fourier count, or more than integrality of $H^\perp$.

**Conjecture DS′ (non-alignment).** On reachable states, for every near-minimal $x\in\Lambda$, the Voronoi direction density f
satisfies $\mathbb E_{\tilde\nu}[f]\le3$ under the $g_{\mathbb Zx}$-tilted law ($c\sim\mathrm{Beta}(\tfrac12,\tfrac{r-1-p}2)$). The analogue
should also hold for near-minimal Δ of rank ≤ 21, beyond which wall1_lyapunov Proposition 7 gives protection. In words: deep holes
of the retained lattice are not concentrated at angles $\cos^2\in[1/r,1/4]$ to its short vectors.

**Status.**

| Item | Status |
|---|---|
| Theorem A (dual/mark structure, kick, lineage, $H^\perp$ theta) | rigorous, all histories |
| Theorem B (Voronoi-uniform law, exact cap-failure count, primal ε, Parseval) | rigorous |
| Theorem C (dual floor $R_0(t)$, exit $10^{-3}$, any projection reducer) | rigorous |
| Proposition D (Haar split of the ratio) | rigorous numerical quadrature for the Haar mean |
| Theorem E (inheritance = q-ary dual; gap ≥ $e^{1628}$; sections carry it) | rigorous |
| Theorem F (exact DS law; dual-hyperplane anti-concentration; density route impossible) | rigorous; (F3) cites Coxeter–Few–Rogers asymptotics |
| (C1) at κ = 1.05 | **open**: reduced to C1′, a selection-law statement |
| (DS) with M ≤ 3.86 | **open**: reduced to DS′ |

**Conclusion.** Neither (C1) nor (DS) is easier than the primal problem in the way wall1_lyapunov suggested.
* Their pathwise content is exhausted by Theorems C and F2. Theorem E shows that the dual "inheritance" is literally the q-ary
  dual $M_t^*$.
* What remains in both is the geometry of the sections $S_t$ cut by the selected vectors, i.e. the selection law of Parts 105–126.
* The one genuine gain is quantitative. In the dual/Parseval form (C1′a), Haar-likeness is needed only up to a factor $e^{9}$ on a
  positive weighted count, rather than to Haar precision at a fixed quantile. Part (b), the discrete-versus-torus comparison, is
  also open, because the only pathwise control of $H^\perp$ (A8) is too weak for sharp-ball counting in dimension 505.

## 8. Sanity computations

The scripts live in the scratch directory and are not committed. Each one is summarized enough below to rerun.

**Exact small first pass (Theorems A, B1).** The script runs a restart-type pass in exact rational arithmetic: 3 horizontal
coordinates, 1 initial vertical coordinate, 6 appended uniform columns, q = 5, r = 4, |H| = 125. Each window is LLL-reduced, and the
SVP and coset minima are found by exhaustive enumeration. At each step it checks:
* (A1) the two generating sets of $L_H$ give the same lattice;
* (A2) $L_H^*$ is integral and saturated (gcd of maximal minors = 1);
* (A3) $[\Lambda^*:L_H^*]=|H|$, with |H| enumerated explicitly;
* (A4/A5) every vector of a basis of $\Lambda'^*$ has the form $(\xi,t)$, with ξ pairing integrally with Λ and $t+\langle\xi,\tilde U\rangle\in\mathbb Z$;
* (B1) all |H| shortest coset representatives are distinct and Voronoi-reduced ($|\langle y,\mu\rangle|\le|\mu|^2/2$);
* (A8) shell counts of $H^\perp$ up to norm² 6: $N_x(H'^\perp)\le N_x(H^\perp)$ for k ≥ 1, and the k = 0 bound.

Results: **all checks pass** for seeds 1–4 at q = 5 and seed 5 at q = 7 (|H| = 343). The runs include k = 0, k = 1 and one
k = 2 step, with $s^2\in\{1,4,7,12/7,19/6,128/51,\dots\}$.
Before LLL reduction was added, a run reported spurious failures from a too-small enumeration box; these disappear once the
bases are reduced.

**Identities (B3), (B4) in rank 2.**
* For a random rank-2 lattice with ρ = 1.3, the primal lens formula gives $\varepsilon_T=0.010655$. The dual Bessel sum, truncated
  at 250 shells with the averaged $4/(\pi z^3)$ tail added, gives 0.010675. The difference is the truncation estimate.
* For an explicit order-5 subgroup H, $\operatorname{Var}_HP/(\mathbb E_HP)^2$ computed directly agrees with the primal formula of (B3) to
  $10^{-16}$.

**Numerics of Theorems C, D, E** (mpmath, 30 digits):

```python
from mpmath import mp, mpf, log, exp, pi, loggamma, besselj, quad, sqrt
mp.dps = 30
logV = lambda j: (j/mpf(2))*log(pi) - loggamma(1 + mpf(j)/2)
G = lambda j: exp(-logV(j)/j)
q, r, b = 3329, 505, 506
# Theorem C: beta_t(R) = q^{-n'} V_N (qR + sqrt(N)/2)^N, n' = 105+t, N = 400+n'
def logbeta(R, t):
    n1 = 105 + t; N = 400 + n1
    return -n1*log(q) + logV(N) + N*log(q*R + sqrt(N)/2)
def R0(t, tgt=mpf('1e-3')/408):
    lo, hi = mpf('1e-4'), mpf(1)
    for _ in range(100):
        mid = (lo + hi)/2
        lo, hi = (mid, hi) if logbeta(mid, t) < log(tgt) else (lo, mid)
    return lo
print([float(R0(t)) for t in (0, 50, 100, 200, 300, 407)])
# Proposition D: end of kappa = 1.05 path
GH = mpf('34.0992'); logD = r*log(GH/G(r))
rho = sqrt((mpf('1.05')*G(b)*exp(logD/b))**2 - 1); GHd = G(r)**2/GH
nu = mpf(r)/2
Lam = lambda z: exp(loggamma(nu+1) + nu*log(2/z))*besselj(nu, z)
dens = lambda x: exp(log(r) + (r-1)*log(x/GHd) - log(GHd) + 2*log(abs(Lam(2*pi*rho*x))))
print(float(rho), float(GHd), float(r*log(rho/GH)))
print([float(log(quad(dens, [a, c]))) for a, c in [(0.5,1),(1,1.5),(1.5,2),(2,2.5),(3,4),(4,6)]])
# Theorem E: log ratio = 400 log q - log D_T - (912-505)/2 log s
print([float(400*log(q) - logD - mpf(407)/2*log(s)) for s in (1, 30, 100)])
```

Output: $R_0=$ 0.005285, 0.01268, 0.02380, 0.05966, 0.1164, 0.2018; ρ = 35.696, GH* = 0.8799, $\log(\rho/\mathrm{GH})^r=23.109$; shell
logs −47.7, −23.9, −24.9, −25.6, −25.9, −25.9; Theorem E logs 2320.8, 1628.6, 1383.6. The tilted Beta mass in (F4) is
$\Pr[c\ge1/4]=e^{-38.5}$ for $c\sim\mathrm{Beta}(1/2,125.75)$.

[Wall 1](../PROOF_GAP.md) · [Lyapunov](wall1_lyapunov.md) · [First tour](wall1_first_tour.md) ·
[Restart (Part 117)](wall1_idea_round2.md) · [Plane count](wall1_plane_count.md) · [Band moments](wall1_band_moments.md)

## Audit

Independent audit (Claude, review sub-agent). The audit read the note against PROOF_GAP Wall 1 (Parts 108, 114, 117, 120–126, 139),
[wall1_lyapunov](wall1_lyapunov.md) (with its Audit) and [first_tour](wall1_first_tour.md). Every proof was re-derived by hand.
All numerics were recomputed with fresh mpmath scripts (40 digits). The scripts are in the audit's scratch directory and are not
committed. No attack parameters were optimized or searched.

**Verdict: MINOR CAVEATS, with one substantive correction (Theorem F3 and the DS conclusions built on it).** Theorems A, B, C and
E, Proposition D, and the conditional claim C1′ ⇒ failure ≤ 1.7·10⁻³ are sound. The C1 verdict ("not proved; reduced to a
selection-law statement") stands. The claim that the density route to DS is impossible does not hold for the law DS actually
concerns.

### Confirmed

* **Theorem A.**
  * (A1) $M_t+\mathbb Z^{400}\oplus0=\mathbb Z^N$, and $\operatorname{covol}P_E\mathbb Z^N=1/\det(\mathbb Z^N\cap E)\le1$.
  * (A2) $(P_EL)^*=L^*\cap E$. $H^\perp=L_H^*$ is integral with minimum ≥ 1.
  * (A3) $M^*$ is correct. The label is a homomorphism with kernel $H^\perp$, $[\Lambda^*:H^\perp]=[L_H:\Lambda]=|H|$, and the
    character formula holds.
  * (A4) Orthogonality reduces to $\langle\xi,\lambda\rangle+kj=0$. The k ≥ 1 and k = 0 forms follow.
  * (A5)–(A6) The kick and character transport are correct. The image of $\chi_{\xi'}$ equals that of $\chi_\xi$ because $Q_*$ is
    onto.
  * (A7) The lineage is correct. A final norm below 1 forces a nonzero label, hence $\xi_0\ne0$.
  * (A8) For k = 0, $H'^\perp=(H^\perp\cap x_0^\perp)\oplus\mathbb Ze$. This holds because $\langle\xi,\tilde U\rangle\in\mathbb Z$ for
    $\xi\in H^\perp$. Also $H_0^\perp=\mathbb Z^{505}$.
* **Theorem B.**
  * (B1) Bijection $H\to S$; Voronoi reduction holds.
  * (B3) The primal count identity is exact. Since the ball is open, $P(U)=0\iff|\sigma(U)|\ge\rho$.
  * (B4) The Fourier coefficients are $D^{-1}\hat{\mathbf 1}_B(\xi)$. Parseval and the lens form are exact. The Siegel and Plancherel
    mean is $D/\operatorname{vol}B_\rho=(\mathrm{GH}/\rho)^r$.
  * The Theorem 5 variance formula of wall1_lyapunov agrees, with cosets equal to nonzero labels.
* **Theorem C, including the probability bound and its scope.**
  * $\Lambda_t^*=M_t^*\cap E_t\subseteq M_t^*$ for every choice of rational $E_t$, including choices that depend on A.
  * For $u\not\equiv0$, $\Pr[w\equiv-A^\top u]=q^{-n'}$. This uses that q = 3329 is prime and that the columns are iid.
  * If $u\equiv0$, ξ is an integer vector, so its norm is ≥ 1 > R.
  * Markov at $10^{-3}/408$ with a union bound over t = 0..407 gives total $10^{-3}$.
  * The first-moment identity was checked **exactly** by enumerating all $5^4$ matrices A (q = 5, 2+2 coordinates, four radii).
    The mean count equals $q^{-n'}\#\{(u,w):u\not\equiv0,\ 0<|(u,w)|<qR\}$ in every case.
  * Recomputed $R_0$ = 0.0052847, 0.012684, 0.023802, 0.059662, 0.11641, 0.20183. $\mathrm{GH}(M_t^*)$ and the κ-path
    $\mathrm{GH}(\Lambda_t^*)$ rows match; the path ends at $\mathrm{GH}(\Lambda_T)=36.694$. The ratios 0.595 … 0.247 match.
  * Scope: "any reducer whose retained lattice is $P_{E_t}M_t$" is correct. The theorem lives in the restart experiment. For the
    Part 108 pass it transfers only through Part 117's coupling, at an extra cost of 0.00022304, which §7 charges.
* **Proposition D.**
  * Constants: ρ = 35.6959, ρ/GH = 1.046824, $r\log(\rho/\mathrm{GH})=23.1091$, GH* = 0.879855.
  * Shell logs: −310.74, −47.72, −23.89, −24.95, −25.59, −26.06, −25.87, −25.90. The sum over (0.5, 6) is $e^{-23.237}$. The
    $x^{-2}$ tail beyond 6 gives about $e^{-25.2}$, which accounts for the remainder to $e^{-23.109}$.
  * Haar count of dual vectors of norm < 1: $e^{64.6}$. Per-vector $|\Lambda_\nu|$: $e^{-56.55}$ at norm 1.
* **Theorem E.**
  * (E1) and (E4) are correct: $\det(M^*\cap S^\perp)=\det(M\cap S)/\det M$, and $M\cap S_t$ is primitive of rank t.
  * (E3) The Poisson computation is correct. The $u\equiv0$ terms are relatively negligible, and $N-r=407$.
  * Recomputed logs: 2320.71, 1628.57, 1383.56.
* **Theorem F.**
  * (F1) is correct.
  * (F2) is correct: $\#\{j:\|j/o\|<a\}=2\lceil ao\rceil-1$ for $0<a\le1/2$, including integer ao.
  * (F3), unconditioned: the direction density is $V_rR(\theta)^r/D$ with sup equal to $\theta_{\rm cov}$.
  * Coxeter–Few–Rogers (1959) bound the density of *any* covering of $\mathbb R^n$ by equal balls below by $\tau_n\sim n/e^{3/2}$.
    The citation and the asymptotic are right. $505/e^{1.5}=112.68$, and the ratio to 3.86 is 29.2. The finite-r value of
    $\tau_{505}$ was not certified, as the note says.
  * (F4): the Voronoi constraint and the tilted law $\mathrm{Beta}(1/2,125.75)$ are correct, with $\Pr[c\ge1/4]=e^{-38.48}$.
* **§7.** $407\cdot2e^{-14}=6.77\cdot10^{-4}$. Adding $10^{-3}$ gives $1.68\cdot10^{-3}\le1.7\cdot10^{-3}$; with Part 117, about
  $1.90\cdot10^{-3}$.
  * The torus Chebyshev step $\Pr_T[\operatorname{dist}\ge\rho]=\Pr_T[P=0]\le\varepsilon_T$ is valid.
  * Steps before the restart need no charge: in the cubic phase $\lambda_1=q\le$ cap, so $\varepsilon_t=0$ there.
  * Mollifier figure: $505\log(1-2.3/\rho)=-33.6$.
* **Labels.** C1′(a), C1′(b) (both under "Conjecture C1′") and DS′ are labelled as conjectures. (C1) and (DS) are listed as open.
* **Exact small first pass.** Fresh rational-arithmetic code (LLL, then exhaustive enumeration in a box rigorously bounded by the
  dual-basis norms). Parameters: 3 horizontal coordinates, 1 initial vertical, r = 4; seeds 1–2 at q = 3 with 5 appends, seed 3 at
  q = 5 with 3 appends.
  * k sequences: (0,0,1,1,1), (0,0,0,1,0), (0,1,1). There was no k = 2 step.
  * Checked: (A1) by equal HNF of the two generating sets; $[L_H:\Lambda]^2=\det$ ratio $=|H|^2$; (A2) integrality; (A3) the
    $M^*$ congruence, the label subgroup of size |H|, and the character formula; (A4)/(A5) truncation in Λ*, the integral kick and
    $\perp v$; (A8) shell bounds to norm² 6; (B1) distinctness and Voronoi reduction; (B3) the primal ε formula equals the direct
    variance ratio exactly; Chebyshev; (F2).
  * **No failures.** The note's own q = 5/7 runs were not reproduced; this independent run is smaller.

### Issues and corrections

1. **(Substantive) F3 is wrong for the law that DS concerns, so "the density route can never reach M < 3.86" is not established.**
   * DS$_M$ (wall1_lyapunov Prop 6, restated in §6) is about the law of $\hat v_h$ **conditional on k = 1**.
   * The parenthetical "before conditioning on k = 1, which can only raise the requirement" is false. On {k = 1} the layer-one
     vector beats the horizontal minimum, so $|\sigma(U)|<\lambda_1(\Lambda)$. Points near deep holes, which have norm ≈ μ ≫ λ1,
     are removed.
   * In the continuous model the conditional direction density satisfies, rigorously,
     $f_1(\theta)\le V_r\min(R(\theta),\lambda_1)^r/(p_1D)\le(\lambda_1(\Lambda)/\mathrm{GH}(\Lambda))^r/p_1$.
   * $(\lambda_1/\mathrm{GH})^r$ is O(1) on Haar-like states: it is distributed as about 2·Exp(1), with median ≈ 1.39. With
     $p_1\approx0.5$ (heuristic) this is ≈ 2.6 < 3.86.
   * So the covering-density obstruction (≈ 113) applies only to the unconditioned law. For DS$_M$, the continuous-model density
     route reduces to an **upper-tail bound on $\lambda_1(\Lambda)/\mathrm{GH}(\Lambda)$** on reachable states, namely
     $(\lambda_1/\mathrm{GH})^r\lesssim3.86\,p_1$, i.e. $\lambda_1\lesssim1.0014\,\mathrm{GH}$. This is not tiny even for Haar
     (Pr ≈ e^{-2} at level 4). It also needs a continuous-to-discrete transfer like C1′(b), because the exact law (F1) is atomic.
   * Corrections:
     * Summary item 6, third bullet: replace with "the unconditioned density route needs M ≥ θ_cov ≳ 113 (CFR); after conditioning
       on k = 1 it needs $(\lambda_1/\mathrm{GH})^r/p_1\le M$ (continuous model)".
     * F3: delete "which can only raise the requirement".
     * F4's "loses the factor ≥ 113": applies only before conditioning.
     * Status row "density route impossible": change to "impossible unconditioned; conditioned, reduces to a λ1 upper-tail plus
       equidistribution statement".
2. **DS′ ⇒ DS is not shown.**
   * DS′ bounds the *unconditioned* continuous-model f.
   * Since $f_1\le f/p_1$, DS′ with constant 3 gives DS$_M$ only with $M=3/p_1$, which is below 3.86 only if $p_1\ge0.78$.
   * It also needs the discrete-to-continuous transfer.
   * The phrase "DS reduces to … Conjecture DS′" should read "DS′, together with $p_1\ge0.78$ and an equidistribution statement,
     implies DS". Alternatively, restate DS′ for $f_1$.
3. **Summary item 6, second bullet, misstates F2.**
   * F2 bounds $\Pr[|\langle\xi,\sigma(U)\rangle|<a]$. For $v_h$ the bound holds only conditional on k = 1, with the factor $1/p_1$.
   * Unconditionally it fails on k = 0, where $v_h=x_0\in\Lambda$ and $\langle\xi,x_0\rangle\in\mathbb Z$ can be 0.
4. **E2: "t ≥ 2" understates the claim, and the proof is a sketch.**
   * For N = r + 1 (t = 1) the integral $\int x^{N-1}x^{-(r+1)}dx$ already diverges logarithmically, so the claim holds for t ≥ 1.
   * The equidistribution step is a sketch, not a full proof. It is plausible: $M_t^*$ is rational and N ≥ 5, so the
     $O(x^{N-2})$ lattice-point error is classical. "Rigorous" in the status table should read "rigorous modulo a standard
     lattice-point estimate". No conclusion depends on E2.
5. **Numerical nits.**
   * E3's exponent is **2320.7**, not 2320.8: 400 log q − log D_T = 2320.71. The values at s = 30 and 100 (1628.6, 1383.6) are
     right.
   * Proposition D is mpmath quadrature, not interval-certified. "Rigorous numerical quadrature" should read "numerical
     quadrature (reproduced)".
   * D-reading 3, "at norms 1–2 such vectors number between e^{150} and e^{400}": the cumulative Haar counts are $e^{64.6}$ below
     1, $e^{156.7}$ below 1.2 and $e^{414.7}$ below 2.
   * The §8 script omits the (0.01, 0.5) and (2.5, 3) shells. They were recomputed here and agree.
6. **Wording.**
   * B2's "the k = 1 part is an equality" holds only up to the boundary $\{|\sigma(U)|=\rho\}$. On that boundary the layer-one vector
     equals the cap and does not fail.
   * A7's lineage exists for *every* dual vector (truncation); the norm < 1 hypothesis only guarantees $\xi_0\ne0$.
   * "Why (b) is not closed by (A8)" is a heuristic explanation and should be labelled as such.
   * "Full rigorous content of dual cusp escape" (§3) is a judgment, not a theorem.
