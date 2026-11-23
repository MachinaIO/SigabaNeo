# First moments over unselected terminal spaces

**The existential terminal-covolume relaxation fails on every design.** In the 400-row marginal restart, for every matrix there is a rank-407 rational space satisfying the actual terminal covolume cap for which a primitive old line has spacing below $7.077\cdot10^{-107}$. On this one space the exact height-zero score exceeds $1.99904\cdot10^{106}$, and the exact height-one score exceeds $0.23100\cdot10^{106}$. Its line has full-lift deficiency at least 140. Removing every term with a translated raw lift through radius 250 at these two heights still leaves a combined **mean above $2.2300\cdot10^{106}$**. This already accounts for distinct projected points and uses only one alternative space per design. Summing over alternative spaces introduces a further loss.

For a narrower relaxation that enforces chronological supports and all 407 pathwise length caps, an explicit family gives a **height-zero incidence sum above $10^{355.83}$** before raw-lift and global selection tests. The two statements have different quantifiers. The first is pointwise over designs. The second bounds a sum with multiplicity. Neither determines the mean at the selected prefix.

## The finite first moment

Let $q=3329$, $L=L(A)=\{(x,y):x=Ay\bmod q\}\subset\mathbb Z^{912}$, and $p(F)=\det(L\cap F)$ for a rational space $F$. Write $P_F$ for projection off $F$. Set $L_0=400\log q$ and
\[
 L_{i+1}=\max\{L_i-\log q,\ (505/506)L_i-\tfrac12\log 56.2142\},
 \qquad B=q^{400}e^{-L_{407}}.
\]
Every selected terminal space $F_*$ has $p(F_*)\le B$. For any rank-407 space $F$, apply the Part 241 kernel $K_h(F,v)$ at height $h$ to a nonzero signed point $v\in P_F L$. It integrates the cap and the competitor inequality against the independent 912-coordinate product CBD(3) plant $X$. Denote its sum by $C_h(A,F)$. Height one alone gives a lower bound for the entire positive-height score. [Score and floor](wall1_score_rejection.md) · [Kernels](wall1_height_split.md)

An exact first moment sums $K_h(F,v)\Pr(F_*=F,\ v\in P_F L)$ over deterministic pairs $F,v$. One can index $v\in P_F\mathbb Z^{912}$ by an integer representative modulo $S_F=F\cap\mathbb Z^{912}$. For a representative $w$, membership is equivalent to $\sigma_A(w)\in\sigma_A(S_F)$, where $\sigma_A(x,y)=x-Ay\bmod q$. Summing over all raw lifts of a single projected point counts its entire infinite fiber. Even an existential prefix test on *raw vectors* leaves this multiplicity unless representatives are identified.

The deterministic list is finite. The primitive integer Plücker vector of $F$, up to sign, has norm $\det S_F\le p(F)\le B$. For $T=F+\mathbb Rw$ with $P_F w\ne0$, the primitive projected ambient spacing is $\det S_T/\det S_F\ge1/B$. Packing therefore bounds the number of signed points through radius $R$ by $(1+2RB)^{505}$ per space. $R=938$ covers all heights here. These arguments justify exchanging sums and expectations. Dropping $F_*=F$ then counts all qualifying incidences. Taking a maximum over $F$ first avoids adding different prefixes on the same design. The following result rules out even that smaller relaxation for the terminal cap. [Integral section identities](wall1_integrality_bound.md) · [Finite-window expected-count identity](../../SigabaNeo/Lib/Lattices/Research/Wall1/CoordinateListMoment.lean)

## A short primitive spacing on every design

**Lemma 1 (a small old section).** In the old coordinate hyperplane, with the last graph coordinate zero, there are nested saturated sections of the graph of ranks 406, 407 and 408. Their covolumes at ranks 406 and 408 are respectively below $10^{913.068}$ and $10^{916.817}$.

The old graph has rank 911 and determinant $q^{400}$, for every $A$. Successively project off a primitive shortest vector in this *full old graph*. These auxiliary choices need only establish existence. At rank $n$ the length is at most $\sqrt{\gamma_n}D^{1/n}$ for quotient determinant $D$, using $\gamma_n=(2/\pi)\Gamma(n/2+2)^{2/n}$ as an upper bound. Hence a lower bound $b$ on $\log D$ updates to $(1-1/n)b-\tfrac12\log\gamma_n$. Start at $400\log q$ with $n=911$ and decrement $n$ after each projection. Primitivity gives the removed section covolume exactly as $q^{400}/D$. The checker evaluates this recursion. A proof of the Hermite bound integrates the translates of $(1-2\|x\|^2)_+$ at unit minimum. For $j$ contributing points the sum of squared distances from the center is at least $(j-1)/2$ by the pairwise-distance identity, so the sum of translates is at most one. [Blichfeldt bound and proof](wall1_terminal_mixing.md)

**Lemma 2 (vary the last generator).** There are nested spaces $F\subset T$ of ranks 407 and 408 in the old coordinates with
\[
 B/2 < p(F)\le B,\qquad
 r=\frac{p(T)}{p(F)}<7.077\cdot10^{-107}.
\]
Here $r$ is the primitive spacing in $P_F L\cap P_F T$.

Take the rank-406 space $E$ and rank-408 space $T$ from Lemma 1. In their rank-two quotient lattice choose a basis $u,v$ coming from the last two projections. Write $s=\|u\|$ and $t=\operatorname{dist}(v,\mathbb Ru)$. Each is at most $q$, since projected coordinate periods span every remaining real quotient of the old graph. Reduce $v$ modulo $u$ so $\|v\|^2\le t^2+s^2/4$. In particular $p(T)=p(E)st$.

Put $M=B/p(E)$. The terminal recursion gives $1023.26795<\log_{10} B<1023.26796$, so $M>2q$ and $\|v\|<M$. Take the largest nonnegative integer $j$ for which $\|v+ju\|\le M$. The next length exceeds $M$ and differs by at most $s$, hence $M/2<\|v+ju\|\le M$. This generator is primitive because its $v$-coefficient is one. Adjoin its lift to $E$ to obtain $F$, with $p(F)=p(E)\|v+ju\|$. Dividing section covolumes gives the spacing bound. Saturation in the full graph follows because all vectors in these spaces have last coordinate zero. Every lift of every point on the indicated line belongs to $T$, also with last coordinate zero.

With $d_T=400-\dim\sigma_A(S_T)$, the identity $p(T)=q^{400-d_T}\det S_T$ and $\det S_T\ge1$ give $d_T\ge140$. Also $d_F\ge d_T$, so $\det S_F\ge p(F)/q^{260}>10^{107.16}$. In particular the large integral Gram denominator discussed in Part 212 is compatible with this spacing. The construction supplies an alternative prefix under the *terminal* cap. It does not enforce each individual freeze or its length cap.

**Lemma 3 (weights and the raw-lift exclusion).** Choose one such $F,T$ per design before drawing $X$. This is measurable since the design set is finite. Take $m=1,\ldots,10^{106}$ multiples of the primitive point and both signs. All these lengths are at most one. At height zero both signs count whenever $Z=\|P_F X\|^2\le959.5$. The cap tail is at most $\epsilon=0.00047835048014$ for every rank-505 orthogonal projector.

At height one let $e$ be the line's unit direction and $W=\langle X,e\rangle$. Its variance is $3/2$, and $\mathbb E W^4\le3(3/2)^2$. Indeed each CBD coordinate is the sum of six independent half-Rademachers, so the fourth moment of the linear form is three times its variance squared minus twice the sum of fourth powers of the individual coefficients. Paley–Zygmund on $W^2$ gives $\Pr(|W|\ge1/2)\ge25/108$. On this event and the cap, at least one sign of each multiple satisfies the exact height-one test. Thus the two conditional score bounds are $2(1-\epsilon)10^{106}$ and $(25/108-\epsilon)10^{106}$. This argument uses the actual cap and direction on the same projector.

For each height $h=0,1$, at fixed design and plant a point admitting a lift with $\|w+hX\|\le250$ injects into the finite translated raw ball at that height, since this construction uses just one space per design. The ball has a design-independent center. Each nonzero feasible raw vector has nonzero input residue and membership probability $q^{-400}$. Thus removing the entire raw-lift class costs at most $1.76372\cdot10^{-10}$ in mean *per height*, exactly as in Part 239. All the remaining points are old and their full-lift deficiency exceeds 132. Their combined relaxed mean exceeds the shared allowance by a factor greater than $4.255\cdot10^{112}$. This subtraction is valid even with arbitrary dependence between the chosen space and the raw graph. It would require a multiplicity correction if performed after summing over all spaces. [Raw-lift estimate](wall1_score_rejection.md) · [Uniform cap tail](wall1_detect_repair.md)

## Keeping chronological supports and individual length caps

**Lemma 4 (a chronological incidence sum).** Count proposed flags that respect the coordinate support on each draw, obey the period and Hermite length caps, and have full graph membership. Sum the exact height-zero weight of their terminal signed witnesses. The sum of their mean incidences exceeds $10^{355.83}$, even when the early caps of the modified Part 226 family are imposed.

Use that family's 405 private suffix pivots and the three old anchors $v,x,y$. Distinct full rational 408-spaces have unit input pivot minors. Their individual membership probabilities are $q^{-400\cdot408}$, unaffected by the two unrestricted final columns. The audited membership sum exceeds $10^{356.13715}$. This is the version with the extra raw-scale caps through draw 67 and $1.10g_i$ caps through draw 220. Append old $v$ as the proposed draw-406 freeze and old $x$ as the draw-407 freeze, always projecting off predecessors. Keep the image of $y$ as witness. Their private pivots ensure both freezes are primitive and the witness is nonzero. The norms of the proposed freezes are respectively below 30 and 32. Before active-grid perturbations their squared raw anchor norms are 842 and 981, and each orthogonal perturbation has norm at most $1/2$ in the quotient by the first 405 pivots. Projection can only shorten them. The incoming $g_{406}>33.92816$ and $g_{407}=g_{406}/s_{406}^{1/506}$ put both Hermite length caps above 40. [Family and membership certificate](wall1_high_codim_sections.md#a-family-below-the-draw-21-threshold) · [Anchor coordinates and uniqueness of spaces](wall1_wholly_old_mass.md#how-large-the-wholly-old-membership-sum-can-be)

Projecting $y$ off $v$ alone gives squared norm at most $307428/421+9/16<731$ by the representative $y-(406/842)v$ in Part 223. Projecting off $x$ can only shorten it further. Both signs therefore count throughout $730\le Z\le959.5$. The fixed-projector mean $757.5$, variance bound $2272.5$, Cantelli and the cap give a signed weight above $0.49842$. The full inverse image of the surviving line recovers the original 408-space, so distinct spaces still give distinct incidences. Multiplying the membership sum by this weight proves the claim. The allowance divided by this certificate is below $10^{-362.11}$.

The chronological sum omits global shortestness comparisons and the long-raw-lift requirement. Its size alone cannot bound the probability of the corresponding existential chronological event from below. Parts 222 and 225 count short raw points with a fresh nonzero coordinate to upper-bound long *selected* winners. Part 226 uses precisely such a comparison to suppress the original annulus family on draw 21. The modified family survives that numerical cutoff. Part 230's two-mark identity keeps the norm removed by the selected projection. Discarding that norm would require a raw-short representative, which the terminal-covolume relaxation demonstrably need not supply. [Raw counts](wall1_long_winner_handle.md) · [Raw determinant bounds](wall1_raw_graph_winner_cap.md) · [Two-mark transition](wall1_inductive_typicality.md)

**Scope.** The selected mean still has the Part 241 partial charges below $5.283493\cdot10^{-8}$ at height zero and $6.998082\cdot10^{-8}$ at positive heights. The $5.2408\cdot10^{-7}$ residual for the actual output remains open. The negative results apply to the two specified relaxations. They leave room for a count incorporating stronger necessary conditions on reachable spaces, even if those conditions do not specify the entire history. [Height-split audit](wall1_height_split.md#audit)

## Interval verification

Run from the repository root. The checker is embedded to keep this a one-file change and imports the existing interval routines from the research scripts directory. The $356.13715$ input is the separately certified lower endpoint in Part 226.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_score_first_moment.md | python -B -)
```

```python
from mpmath import iv
from wall1_hermite_budget import log_blichfeldt, log_floors, maximum
from wall1_score_rejection import raw_mass

iv.dps = 60
I, log, exp = iv.mpf, iv.ln, iv.exp
q = 3329
start = 400 * log(q)
last = log_floors()[-1]
terminal = maximum(last-log(q), I(505)/506*last-log(I('56.2142'))/2)
log_B = start-terminal
assert I('1023.26795') < log_B/log(10) < I('1023.26796')

lower = start
for rank in range(911, 503, -1):
    lower = I(rank-1)/rank*lower - log_blichfeldt(rank)/2
    if rank == 506:  # just removed the 406th direction
        assert (start-lower)/log(10) < I('913.068')
log_pT_upper = start-lower
assert log_pT_upper/log(10) < I('916.817')
assert 2*exp(log_pT_upper-log_B) < I('7.077e-107')
assert log_pT_upper < 261*log(q)
assert (log_B-log(2)-260*log(q))/log(10) > I('107.16')

epsilon = I('.00047835048014')
zero, one = 2*(1-epsilon), I(25)/108-epsilon
raw = raw_mass(912, 400, 250)
assert raw < I('1.76372e-10')
assert zero > I('1.99904') and one > I('.23100')
residual = I('1e106')*(zero+one)-2*raw
allowance = I('5.2408e-7')
assert residual > I('2.2300e106') and residual/allowance > I('4.255e112')

volume = iv.pi**253/iv.factorial(253)
cap_ratio = iv.sqrt(I('56.2142'))*volume**(I(1)/506)
assert cap_ratio*I('33.92816')/I(30)**(I(1)/506) > 40
assert I(307428)/421+I(9)/16 < 731
gap = I('757.5')-730
weight = 2*(gap**2/(I('2272.5')+gap**2)-epsilon)
log_incidence = I('356.13715')+iv.log10(weight)
assert weight > I('.49842') and log_incidence > I('355.83')
assert iv.log10(allowance)-log_incidence < I('-362.11')
print('log10 terminal cap and old section upper bound:', log_B/log(10),
      log_pT_upper/log(10))
print('relaxed residual lower bound:', residual)
print('chronological log10 incidence lower bound:', log_incidence)
```

## Audit

**Verdict.** Both lower bounds hold for the stated 400-row marginal restart. The embedded interval checker passed. A separate calculation in determinant units gave $7.07629294451632\cdot10^{-107}$ as an outward-rounded upper bound on the primitive spacing.

For every design, the rank-406 and rank-408 sections give $B/p(E)>2q$ and $p(T)<q^{261}$. The coefficient one on $v$ makes the new generator primitive in the rank-two quotient, so $p(F)>B/2$. The entire inverse image of the projected line is $T$, hence its primitive graph spacing is exactly $p(T)/p(F)$ and its full-lift deficiency is at least 140. This existence statement and the two score bounds before raw-lift removal hold for each design.

The raw-lift subtraction uses the joint mean. Fix the plant first. At each of the two heights every candidate raw vector has coordinates of magnitude at most $250+3<q$. A nonzero candidate with zero input residue cannot lie in the graph. Each candidate with nonzero input residue has graph membership probability $q^{-400}$ over the design. Choosing one $F$ per design lets the raw count bound the number of removed signed points even though $F$ depends on the design. The resulting lower bound exceeds $2.23004643\cdot10^{106}$, or $4.25516\cdot10^{112}$ times the shared allowance.

The Part 226 checker also passed. Its modified family gives a log-membership certificate of $356.13715951948\ldots$ in base ten for the first 405 proposals and three anchors. The two final proposed freezes have lengths below 30 and 32, within both their period and Hermite caps. The private input pivots distinguish the full spaces, and each terminal prefix together with its signed witness determines the full space. Using the certified lower endpoint $356.13715$ and counting both signs on the common interval $730\le Z\le959.5$ gives a base-ten log-incidence lower bound above $355.83474914$.

This last bound counts incidences with multiplicity before global shortestness and raw-lift tests. To turn it into a quantitative lower bound on occurrence would require controlling that multiplicity, and selection imposes further conditions. For the first-moment estimate considered here, the open question is whether the residual at the actually selected prefix fits the single $5.2408\cdot10^{-7}$ allowance. The separate rejection and lifting questions in Parts 239–241 also remain open.
