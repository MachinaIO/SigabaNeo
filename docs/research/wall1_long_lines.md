# Long marked lines and old witness planes at the width-506 restart

A long marked line misses **every** old plane witnessing the horizontal charge, even after allowing all lattice translates of the plane. On a reachable family with old minimum $t/h\in(0.934297,0.934298)$, more than $0.99999688$ of the fresh draws contribute to the long-line charge. Both facts hold under the exact selector. The family has too little design mass to decide the terminal budget. The unconditional upper bound obtained below is $1-2^{-1447.324}$.

## The conditional event

Use the marginal restart with 400 horizontal coordinates, 105 initial columns and 406 subsequent selections before the fresh terminal column. Put $q=3329$, $d=505$, $c=0.954$. Given the old history $S$, let $E,L,D,H,x_0,t$ be the retained space, old lattice, its covolume, mark in $E/L$, signed old winner and its length. Write $h=G_dD^{1/d}$, $G_d=V_d^{-1/d}$, $u=ch$, $R=u t^{-1/d}$, and $I=\mathbf1_{\{\lambda_1(\pi_{x_0^\perp}L)<R\}}$. All probabilities here are for the uniform design. The independent CBD(3) plant does not enter them. [Part 108](wall1_first_tour.md) · [Part 117](wall1_idea_round2.md) · [Part 120](wall1_plane_count.md)

Let $U$ be the uniform fresh point of $H$. A nonzero point is *long* if every nonzero class on its projective line has all representatives longer than $u$. Write $b=1$ when the signed winner is horizontal. Part 146 gives the following conditional contribution and its design average.
$$
 A(S)=I\mathbf1_{\{t>1\}}\Pr(U\text{ long},\ b=1\mid S),
 \qquad A=\mathbb E A(S).
$$
At a long $U$, a beating height $k$ in the reduced list $1\le k\le(q-1)/2$ must satisfy $k^2<t^2-u^2$, including at a winner tie. Indeed $kU\ne0$ and the old component of any lift has length strictly greater than $u$. Part 146 handles the height-$q$ endpoint with the inherited signed tie rule. [Exact projective count and audit](wall1_subspace_void.md) · [Short-line bound and audit](wall1_uncovered_lines.md)

## 1. Separation from every old witness plane

**Proposition.** Suppose $I=1,t>1$. Let $W\subset E$ be any old witness plane through $x_0$, and let $b_W=\det(L\cap W)/t<R$. Every long point $U$ satisfies, for every $a\in\mathbb F_q^\times$ and every representative $y$ of $aU$,
$$
 \operatorname{dist}(y,W)>\sqrt{u^2-b_W^2/2}>u/\sqrt2 .
 \tag{1}
$$
In particular even a single incident nonzero class would make the line short. The horizontal charge uses the existence of $W$ in the old lattice and the absence of a beating lift on the fresh line.

*Proof.* Extend the primitive $x_0$ to a basis of $L\cap W$. In orthonormal coordinates on the plane the basis can be written $(t,0),(a_0t,b_W)$ with $0\le a_0\le1/2$, by size reduction and choice of axes. Shortestness gives $b_W^2\ge(1-a_0^2)t^2$. The diagonal joining the two basis vectors triangulates their fundamental parallelogram into congruent triangles. Every point of a triangle lies within its circumradius of some vertex. For example the barycentric weighted mean of the three squared distances is the squared circumradius minus the squared distance to the circumcenter. Thus the plane covering radius $\mu_W$ satisfies
$$
 \frac{\mu_W^2}{b_W^2}
 \le \frac14\left(1+\frac{a_0^2t^2}{b_W^2}\right)
              \left(1+\frac{(1-a_0)^2t^2}{b_W^2}\right)
 \le\frac1{2(1-a_0)(1+a_0)^2}\le\frac12 .
$$
The first bound is the squared circumradius formula using area $tb_W/2$. The last follows from $a_0(1-a_0-a_0^2)\ge0$. Subtract a vector of $L\cap W$ nearest to the $W$-component of $y$. The resulting representative has squared length at most $\operatorname{dist}(y,W)^2+b_W^2/2$. Longness and $b_W<R<u$ give (1). This proof also gives $b_W\ge\sqrt3\,t/2$, hence $t<(2u/\sqrt3)^{d/(d+1)}$ wherever $I=1,t>1$. ∎

**Transverse count for a fixed old plane.** Choose any witnessing $W$ from the history before drawing $U$. Conditional on this history, the probability that *any* nonzero scalar of $U$ has a representative at distance at most the full radius $u$ from $W$ is below $0.000289087$. Thus imposing even this enlarged incidence condition can discard almost all of the charge on a history in §3.

To prove the bound, project the lattice and mark to $W^\perp$ inside $E$. The projected lattice has rank $d-2$ and determinant $D'=D/(tb_W)$ by a basis of the saturated plane extended to $L$. Its mark extension is the projection of the ambient integer lattice, so its dual is integral. The projected zero fiber has mass at most $1/D'$. Every other incidence is on a projected short line at radius $u$. For these apply Part 147, equation (3), in rank $d-2$, with the same $z=u\sqrt{2\pi/d}$ used for the old rank $d$. The ratio of the two Gaussian majorants is $tb_W/(z^2\theta(z)^2)\le d/(\pi\sqrt3)$ by $t\le 2b_W/\sqrt3$ and $b_W<u$. Uniformity passes to the projected mark. Finally
$$
 D'>\frac{(h/G_d)^d}{2(ch)^2/\sqrt3}>2^{1274}
$$
using monotonicity in $h>31.9321$. The sum $2^{-1274}+(3.114918\cdot10^{-6})d/(\pi\sqrt3)$ is below the claimed bound. The choice of $W$ may depend on the entire old design. A choice depending on $U$ would require a joint estimate. [Part 147, projected Gaussian bounds](wall1_uncovered_lines.md)

## 2. How much of the old-plane event passes to the charge?

Put $\epsilon=3.114918\cdot10^{-6}+2^{-1284}$ and
$$
 B=\{I=1,\ 1<t\le\sqrt{u^2+1}\},\qquad
 C=\{I=1,\ \sqrt{u^2+1}<t\le0.977h\}.
$$
Then
$$
 A\ \ge\ (1-\epsilon)\Pr(B)+0.94167296\Pr(C).                 \tag{2}
$$
On $B$ **every long line is empty** in the terminology of Part 146. Consequently $A\le0.009$ requires $\Pr(B)<0.009000029$. Even spending the entire combined allowance on $A$ requires $\Pr(B)<0.009773875$.

*Proof.* On $B$ there is no admissible positive beating height on a long line. The total conditional mass of all short lines is below $3.114918\cdot10^{-6}$ by Part 147, equation (3). The zero fiber has mass $1/|H|\le1/D<2^{-1284}$. Indeed the extension $K=L+H$ given by the preimage of $H$ in $E$ has integral dual, so $\det K\le1$ and $|H|=D/\det K\ge D$. The restart floor $h>31.9321$ gives $\log_2 D>d\log_2(31.9321/G_d)>1284$.

For $C$, put $v=\min(q,0.977h)$, $z=v\sqrt{2\pi/d}$, and $\theta(z)=\sum_{j\in\mathbb Z}e^{-\pi z^2j^2}$. A beater has length at most $t\le v$. Each nonzero reduced height permutes the mark. Counting all beating candidates by positive height, Part 147, equation (2), and $\sum_{k\ge1}e^{-\pi k^2/z^2}\le z/2$ bound their probability by
$$
 \frac{e^{\pi v^2/z^2}z^{d+1}\theta(z)^d}{2D}
 =\frac{J_d}{2}(v/h)^d z\theta(z)^d,qquad
 J_d=e^{d/2}(2\pi/d)^{d/2}/V_d .
$$
Use $v/h\le0.977$, $z\le q\sqrt{2\pi/d}$ and $z\ge0.977(31.9321)\sqrt{2\pi/d}$. The bound is below $0.058323917$. Removing the zero, short, and beaten draws proves (2), without a factorization of history and winner probabilities. [Part 147 and audit](wall1_uncovered_lines.md) · [Dependence counterexample and audit](wall1_averaged_charge.md) ∎

The last-used-coordinate count also controls histories near the unit threshold.
$$
 \Pr(1<t\le2/\sqrt3)<2^{-30.5955}.
 \tag{3}
$$
For completeness, scale the terminal minimum cutoff in Part 147, §3, from one to $s=2/\sqrt3$. All its tail length caps $B_l$ scale by $s$, by the same homogeneous Hermite argument. At indices $(i,j)$ the old determinant lower bound scales by $s^{-j}$. Evaluate the Gaussian bound at $s$ times its original scale, so its exponential is unchanged and its dual theta factor can only decrease. Its remaining power is $s^{d-j+1+j}=s^{506}$. Every tested cap is still below $1385s<q$, as required for nonzero height permutations. The initial-graph cube count scales by at most $s^{505}$, since $sB+\sqrt d/2\le s(B+\sqrt d/2)$. This scales the actual upper **sum** certified in Part 147 by at most $s^{506}$. Its base-two logarithm is below $-135.60+506\log_2s<-30.5955$. The special endpoint tie argument used for $t=1$ is unnecessary in the last-used-coordinate count. ∎

## 3. A reachable family close to the length cutoff

**Proposition.** Set $Q=q^{400}$. There is a penultimate family of probability between $(1-2^{-47.92})Q^{-408}$ and $Q^{-408}$ on which the only shortest lines are two orthogonal lines of length $t=\sqrt{9954701}$. At every such history $I=1$, $t/h\in(0.934297,0.934298)$, and $A(S)>0.99999688$.

*Proof.* In the first restart column put $116,117,\ldots,315$ in rows 1–200 and zero elsewhere. Use the same entries in rows 201–400 of the second column. The remaining 103 restart columns are independent uniform. Require the next 406 columns to vanish. These prescriptions cost $Q^{-408}$ before the 103-column test below.

First restrict to the two prescribed input coordinates. The lattice splits into orthogonal blocks, each consisting of the graph of one column on its 200 rows. For a nonzero input residue of least absolute value $k$, the least squared length is
$$
 k^2+\sum_{i=116}^{315}[ki]_q^2,
$$
where brackets denote the centered residue. Minimization in the input and in each output coordinate is independent once the residue is given. At $k=1$ the squared length is $9954701$, and its minimum for $2\le k\le1664$ is $39818804$, by the finite integer check below. A nonzero vector at input residue zero has length at least $q>t$. This gives the two indicated lines.

Exclude every vector of length at most $t$ using any of the 103 free inputs nontrivially. Such an input tuple is nonzero modulo $q$, because $t<q$. For each fixed integer candidate its graph condition costs $1/Q$ over the free columns. Counting sign pairs by enclosing disjoint unit cubes gives failure probability at most $V_d(t+\sqrt d/2)^d/(2Q)<2^{-47.92}$. This proves the family probability and leaves exactly the stated old shortest lines. Each zero append has a unique fresh unit line and deletes its own coordinate, so this same lattice is present at the terminal draw. Its covolume is $Q$ and its raw mark map is injective. Whichever shortest line the signed tie rule selects, the other projects to length $t$. Here $3170.652<R<3170.654$, so $t<R$. Also $3221.643<u<3221.644$, so $u>t$. The histories are in $B$ and the conditional version of (2) applies. ∎

There are also histories with conditional charge even closer to one. In Part 146's repeated-column family take the common column to be $e_1+e_2$ and the 406 appends zero. The audited two-difference argument gives $I=1,t=\sqrt2,D=Q$. For a raw marked point, the last 398 horizontal coordinates of any representative are fixed modulo $q$. At a nonzero scalar of a uniform point these residues are uniform. Thus the chance that *some* nonzero scalar has a representative within $u$, including the zero point, is at most
$$
 (q-1)V_{398}(u+\sqrt{398}/2)^{398}/q^{398}<2^{-914.435}.
$$
This is the unit-cube count on just those coordinates and a union bound over scalars. Every remaining point contributes. The exact history probability for this fixed common column is $Q^{-511}$. These examples locate a conditional obstruction. Neither supplies percent-level mass in the design average. [Part 146 and audit](wall1_subspace_void.md) · [Unit-history distinction and audit](wall1_horizontal_core.md)

## 4. A design-averaged upper bound

The following bound uses a Gaussian on the mark extension to force some raw draws outside the long-line event. It averages over the 511 old columns before the terminal append.

**Proposition.** $A<1-2^{-1447.324}$.

*Proof.* Write $N=911$, $M=\{(x,y)\in\mathbb Z^{400+511}:x\equiv A_{\rm old}y\pmod q\}$, $L=P_EM$, and $K=P_E\mathbb Z^N$. Let $\rho_s(X)=\sum_{y\in X}e^{-\pi\|y\|^2/s^2}$, $T_M(s)=\rho_{1/s}(M^*)$, and $s=q^{400/N}$. Below we count classes having a representative in the fixed ball of radius $r=30.46<u$, including the zero class. Denote their fraction in $K/L$ by $p(S)$. Each such point is excluded from $A(S)$.

For every class $y+L$, shifted Poisson summation and $L^*=M^*\cap E$ give
$$
 \rho_s(y+L)\le(s^d/D)T_M(s).
$$
The triangle inequality removes the dual character. For any $a>0$ the zero dual term and the coordinate injection of Part 147, §2 give
$$
 1\le \frac{\det K}{a^d}\rho_a(K)\le\theta(a)^d .
$$
Indeed $K^*=\mathbb Z^N\cap E$ injects by restriction to some $d$ coordinates and restriction only shortens vectors. [Gaussian Poisson formula](https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/transference.pdf) · [Mark extension and audit](wall1_uncovered_lines.md)

Put $v_0=0.94$, $l=0.86$, $a=v_0r\sqrt{2\pi/d}$, and define
$$
 f(x)=\theta(ax)^d\exp[-d(x^2-1-2\log x)/2],\qquad
 W_0=1-f(l/v_0)-f(1/v_0).
$$
The $\rho_a$-mass of $K$ in the shell $lr\le\|y\|\le r$ is at least $W_0a^d/\det K$. To see this, for $x<1$ compare the inner tail $\|y\|\le xv_0r$ with the Gaussian at scale $ax$. For $x>1$ use the same comparison on $\|y\|\ge xv_0r$. In both cases the ratio of the weights at admissible $y$ is at most $e^{d(1-x^2)/2}$. The upper bound on $\rho_{ax}(K)$ then gives $f(x)a^d/\det K$.

As $s>a$, changing from scale $a$ to $s$ multiplies every shell weight by at least $e^{\pi(lr)^2(a^{-2}-s^{-2})}$. Divide the shell mass by the maximum mass of one class and by $|H|=D/\det K$. This proves
$$
 p(S)\ge W_0(a/s)^d e^{\pi(lr)^2(a^{-2}-s^{-2})}/T_M(s).
$$
For the unselected raw graph,
$$
 \mathbb E T_M(s)=\theta(s)^N+
 [\theta(s/q)^{400}-\theta(s)^{400}](\theta(s/q)/q)^{511}
 \le\theta(s)^N+\theta(q/s)^N .
$$
Indeed a dual horizontal coordinate tuple has the form $p/q$. If $p\equiv0$ the graph-input part is integral. Otherwise each of its 511 required residues is uniform modulo $q$, independently over columns. Sum those one-coordinate Gaussians, then use $\theta(s/q)=(q/s)\theta(q/s)$ and $s^N=q^{400}$. This calculation uses the **old** ambient graph. No distribution on the selected subspace $E$ is substituted. Jensen's inequality gives $\mathbb E[1/T_M]\ge1/\mathbb E T_M$. Using the elementary upper enclosure for each theta in the two subtractions in $W_0$ and in the denominator gives
$$
 \log_2\mathbb E p(S)\ \ge\ \log_2\!
 \frac{W_0(a/s)^d e^{\pi(lr)^2(a^{-2}-s^{-2})}}
      {\theta(s)^N+\theta(q/s)^N}>-1447.324.
$$
Since $A(S)\le1-p(S)$, the result follows. ∎

This improves the evaluated complement in Part 147 but cannot approach the required allowance by itself. Even **all** short-line draws and the zero fiber together have conditional mass below $\epsilon$ on every history. A percent-level upper bound must control the joint old-plane and winner event.

## Verification and remaining gap

- The modular minimum in §3 is an exhaustive finite certificate. With exact integers set `ctr(n) = (n + 1664) mod 3329 - 1664`. Evaluate `k*k + sum(ctr(k*i)**2 for i in range(116,316))` for each integer `k` from 1 through 1664. The minimum is $9954701$, attained only at 1. The minimum of the other 1663 entries is $39818804$.
- For an exact small check take $L=2\mathbb Z\oplus2\mathbb Z\oplus28\mathbb Z$, $H=(L/7)/L$ where $L/7=\tfrac17 L$, $u=5/2$ and old-plane cutoff $R=9/4$. The first two axes give a witnessing plane. For each of the $7^3$ points compare $4\sum_j(b_j[ka_j]_7)^2$ with $49\cdot25$ at every nonzero scalar, with $b_j=2,2,28$. Exactly 294 points on 49 lines are long. All miss the plane and all 294 win horizontally. Independently minimizing signed lengths in the appended window gives the same 294 horizontal wins in total. For this last check only heights $-2,\ldots,2$ can tie or beat the old minimum.
- Scratch interval arithmetic used 65 decimal digits, $V_0=1,V_1=2,V_j=2\pi V_{j-2}/j$, and $1\le\theta(z)\le1+2v/(1-v^3)$ with $v=e^{-\pi z^2}$. The §3 cube-count log lies in $(-47.92356,-47.92354)$. In §4 the lower enclosure used for $W_0$ lies in $(0.8436907,0.8436908)$ and the log of the evaluated lower bound lies in $(-1447.32304,-1447.32302)$. The examples use the recorded restart unchanged.

**Conjecture (open).** The suggested allocation is $A\le0.009$. The combined inequality $A+F_{\rm nh}\le0.0097738441$ is also open, where $F_{\rm nh}$ is Part 147’s positive-height first moment on nonhorizontal wins. Inequality (2) identifies an old-plane stratum whose probability passes almost undiminished to $A$. Above that stratum the surviving scalar counts also matter. The examples prove conditional dominance by empty long lines on their stated families. The frequency of those configurations across the selected terminal histories, and which stratum dominates the actual design average, remain unknown. Part 105 concerns Haar input, whereas the history probabilities in (2) are for the selected finite graph law. [Part 105](wall1_selection_law.md) · [Part 147 terminal budget](wall1_uncovered_lines.md)

## Audit

**Verdict — SOUND.** All four claims hold for Part 117’s marginal width-506 restart with Part 108’s signed selector. The old-plane probability bound is necessary only. The audit found no numerical corrections.

**Unconditional bound.** Projecting the raw graph gives $L^*=M^*\cap E$, so the shifted Poisson upper bound for one class holds simultaneously for every selected history and every class. The two Gaussian comparisons bound the mass on opposite sides of the shell. Since $s>a$, the conversion from $a$ to $s$ uses the inner shell radius $lr$ for its lower bound. Dividing by $|H|$ cancels $D/\det K$. The dual average uses the 511 independent raw columns before selection, and Jensen applies to the positive variable $T_M$. At 85 decimal digits with outward rounding, the shell coefficient used as a lower bound lies in $(0.84369072118,0.84369072119)$, and the base-two logarithm of the resulting complement bound lies in $(-1447.3230300,-1447.3230299)$. This proves the strict $A<1-2^{-1447.324}$.

**Plane incidence.** The triangle circumradius bound gives $\mu_W^2\le b_W^2/2$ because $(1-a_0)(1+a_0)^2\ge1$ on $[0,1/2]$. For any $\lambda\in L$, subtracting $\lambda$ leaves the marked class unchanged. Rounding the plane component of $y-\lambda$ therefore proves (1) for $\operatorname{dist}(y,W+\lambda)$, simultaneously for every nonzero scalar, representative, translate and witnessing plane. An incidence test at distance $u/\sqrt2$ misses every charged long draw. At the larger radius $u$ the probabilistic estimate has a different quantifier. It applies to each plane chosen before the draw. The projected determinant floor has base-two logarithm above $1274.3686$, and the projected short-line bound plus zero-fiber bound is below $0.00028908630$.

**Reachability and exact counts.** Exhaustive centered-residue arithmetic gave the unique minimum $9954701$ at $k=1$ and the next minimum $39818804$ at $k=2$ among the 1664 positive residues. The orthogonal blocks and $t<q$ rule out any additional shortest line using only the two prescribed inputs. Every remaining candidate uses a nonzero free input modulo $q$, so its membership probability is $1/Q$. The sign-pair cube bound has base-two logarithm in $(-47.923551,-47.923550)$. The two fixed columns and 406 zero appends give the family upper probability $Q^{-408}=3329^{-163200}$, with the stated factor $1-2^{-47.92}$ for its lower bound. The interval checks give $t/h\in(0.93429717,0.93429719)$ and $t<R<u$. Both choices of old shortest line pass the test, and $A(S)>0.99999688$ on the family. For the fixed repeated-column example the 398-coordinate bound has base-two logarithm in $(-914.43566,-914.43565)$ and the 511 fixed columns cost $Q^{-511}$. In the separate $q=7$ check, direct signed window minimization and the scalar-orbit test gave identical sets of 294 draws out of 343, on exactly 49 long lines.

**Sharpness and the remaining budget.** For a marked line $P$, let $m(P)$ be the least representative length over its nonzero classes. Part 146’s height-one test gives an empty line for $m(P)>\sqrt{t^2-1}$ and a nonempty line for $m(P)<\sqrt{t^2-1}$. The inherited signed tie decides equality. On $B$, longness gives $m(P)>u\ge\sqrt{t^2-1}$, including the endpoint $t^2=u^2+1$. This is the exact length comparison available from longness alone. A larger cutoff for the actual finite history law would need additional information. On $B$ the conditional charge is exactly one minus the zero-fiber mass and the mass of short lines. Consequently
$$
 (1-\epsilon)\Pr(B)\le \mathbb E[\mathbf1_B A(S)]\le\Pr(B).
$$
The quotient $0.009/(1-\epsilon)$ lies in $(0.0090000280343,0.0090000280344)$. Its outward rounding to $0.009000029$ is a necessary bound on $\Pr(B)$, with no claim of numerical optimality. Even the sharper quotient gives no sufficient condition for $A\le0.009$ because it leaves $\mathbb E[\mathbf1_{B^c}A(S)]$ uncontrolled. The beater majorant on $C$ is below $0.05832391649$, confirming the $0.94167296$ coefficient in (2). The combined allowance separately gives $0.0097738441/(1-\epsilon)<0.009773875$. Part 148 still leaves the nonhorizontal first moment above its required budget in the proved upper estimate.

**Unit-threshold estimate.** An independent 65-decimal-digit interval sum over all 83,027 index pairs, including the separate initial-graph term, put the log of Part 147’s base upper sum in $(-135.600381,-135.600380)$. Scaling the lengths and the Gaussian scale by $2/\sqrt3$ multiplies each upper term by at most $(2/\sqrt3)^{506}$, including the determinant loss from the $j$ prior directions. The largest allowed cap stays below $q$. Even the rounded base exponent $-135.60$ gives a scaled exponent below $-30.59551$, verifying (3).
