# Reachable terminal prefixes modulo a prime

Fix the planting $u=(e,s,1)$ and take the probability over the uniform matrix $A$, as in the [registered slide target](../../SigabaNeo/Lib/Lattices/Research/Wall1/SelectedSlide.lean). For odd $q$, the factor-two failure of Part 9 is deterministic for a fixed **real prefix plane**, even when that plane is tested on a different input matrix. For this failure, a union bound over the support of the selected plane is either zero or vacuous. Counting residue classes instead gives an exact expression in terms of their *selection masses*.

## Fixed-plane calculation

Write $L_A$ for the embedded lattice, $d=m+n+1$, and $r=d-β$. For a rational $r$-plane $W$ let $S=W\cap\mathbb Z^d$, $G=\mathbb Z^d/S$, and $H_A=(L_A+S)/S$. Orthogonal projection identifies $H_A$ with the projected lattice. Since $S$ is saturated, $G$ is free of rank $β$. We have $qG\subset H_A\subset G$ because $q\mathbb Z^d\subset L_A$. Denote the image of $u$ by $g$.

For every prime $p\ne q$ the following equivalences hold, including at $g=0$:
$$
 g\in pH_A\quad\Longleftrightarrow\quad g\in pG
 \quad\Longleftrightarrow\quad \bar u\in S\bmod p .
$$
Indeed if $g=ph$ in $G$ then $ph,qh\in H_A$, whence Bézout gives $h\in H_A$. The last equivalence is reduction modulo $S+p\mathbb Z^d$. In fact for $g\ne0$ write $g=c h_0$ with $h_0$ primitive in $G$ and $c>0$. The projected multiplicity is exactly $c/j$, where $j$ is the order of $h_0+H_A$ in $G/H_A$. This follows by intersecting the two groups with the line of $h_0$. The order divides both $q$ and $c$. Thus only one factor of the prime $q$ can distinguish ambient and lattice multiplicities.

## Support count and its limit

Fix the selector, including all choices, and let $W_A$ be its output plane. For the verified loop the number of blocks must be integral, $β\mid d$. Its pass is defined by classical choice from a specification, so an enumeration using a particular lexicographic implementation would require a correspondence proof. The following bounds apply to every fixed choice. There are at most $q^{mn}$ distinct output planes, one per possible input matrix. For the $p$-divisibility test their distinct observable values $T_A=(W_A\cap\mathbb Z^d)\bmod p$ number at most
$$
 \min\{q^{mn},{d\brack r}_p\},\qquad
 {d\brack r}_p=\prod_{i=0}^{r-1}\frac{p^d-p^i}{p^r-p^i}.
$$
Here each $T_A$ has dimension $r$ by saturation. The formula counts ordered independent tuples and divides by the number of bases per plane. Exactly ${d-1\brack r-1}_p$ ambient planes contain $\bar u$ when $r>0$, by quotienting by its line (the last coordinate is one). Their fraction is $(p^r-1)/(p^d-1)<p^{-β}$ for $β>0$, by double counting incident pairs of a plane and a nonzero point. This is a fraction of the Grassmannian, not an input probability.

For each residue plane let $N_T=\#\{A:T_A=T\}$. Including a vanished plant as failure, the probability of vanishing or multiplicity divisible by $p\ne q$ is exactly
$$
 q^{-mn}\sum_{T\ni\bar u}N_T.
$$
In contrast, summing *fixed-plane* failure probabilities over reachable real planes gives at least one as soon as a single reachable plane has $T\ni\bar u$. Its summand is one by the fixed-plane calculation. If none has that incidence the sum for this test is zero. The same dichotomy holds for the simultaneous event over this support. This sharpens the selection-bias objection for this particular observable: even a support-size bound of two would not give a nontrivial positive upper bound by that method. An upper bound on the mass of incident outputs, or a proof excluding them all, would.

For example, take $m=n=1,q=3,e=s=0$, so $u=(0,0,1)$. On input $A=1$ the plant generates the unique shortest line since neither horizontal coordinate unit belongs to the lattice. Put $b=(-1,1,0)$ and $W=\mathbb R(2b+u)$. The vectors $(3,0,0),b,u$ form a lattice basis, and replacing $u$ by $2b+u$ preserves it. Modulo this plane the plant equals $-2[b]$. On the different input $A=0$, $b$ is absent, but $3b$ belongs and $[3b+2u]=-[b]$ still halves the plant. The projected plant is nonzero on both inputs because $u\notin W$. This illustrates the cross-input obstruction for a candidate plane; it does not assert a slide trajectory reaches it.

Every [Part 9 witness](wall1_planted_prob.md) satisfies the same mod-two incidence because its integral generator reduces to the plant modulo two. Thus even one such plane in the selector's global support would defeat the unweighted union, regardless of how infrequently it was selected. Part 9 proves existence among primitive prefixes under a determinant cutoff and gives no such reachability result. The horizontal concentration estimate there averages over the planting, whereas the slide target fixes it. The [Part 5 count](wall1_sublattice.md) averages over Haar lattices. Neither gives the incident selection mass above. The verified loop also has no equal-block instance at $β=406$ for the three Part 9 dimensions. At the registered $d=1024,β=512$ shape the exact mass identity applies directly. A bound on this mass for $p=2$ remains open, as do the other multiplicities and the competing-line condition. No improved recovery probability or certified block size follows.


## Independent audit (Nov 2026)

Verdict: **correct** (mod-p reduction of the Part 9 obstruction, exact failure probability with Gaussian binomials, and the
3-dimensional example checked line by line). Not checked: that the verified loop requires β | d and chooses by classical choice.
