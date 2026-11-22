# Three selected averages on finite q-ary restarts

We exhaustively counted 156,049,323 terminal designs across 39 toy restarts of retained ranks three through five, plus separate penultimate enumerations. The inherited event can be traced to a few short flags in the incoming graph. The vertical event can have many eligible draws followed by very few plane hits. The terminal count can be appreciable even when virtually every contributing design has just one witness. The nonhorizontal-lift contribution is $10688/1953125=0.005472256$ at retained rank four with three outputs and $q=5$. This uses 56.0% of the numerical value of the shared terminal allowance. On the largest full row, $(m,j,T,q)=(1,3,2,23)$, the 148,035,889 designs produce 261142 residual quotient-line incidences. Every one has only horizontal rounded lifts. Here $m$ counts outputs, $j$ initial inputs, and $T$ selections through the penultimate draw.

## Law and observables

Let $m$ be the number of output coordinates, $j$ the initial number of graph inputs, $d=m+j$ the retained rank, $b=d+1$ the window rank, and $T$ the number of suffix selections through the penultimate draw. The terminal draw is $T+1$, in raw dimension $N=d+T+1$. Write $Q=q^m$. Start with the unconditioned graph $x\equiv A y\pmod q$ for uniform $A\in\mathbb F_q^{m\times j}$. Append independent uniform columns, always at height one. At every step minimize the squared length, then the signed projected ambient coordinate tuple, over the whole window. Project orthogonally off the winner. Past projections apply to all subsequently read columns. Original output coordinates come first and inputs retain chronological order. The restart law is marginal throughout. [Part 108](wall1_first_tour.md) · [Part 117](wall1_idea_round2.md)

Put $V_i=\pi^{i/2}/\Gamma(1+i/2)$ and $c=477/500$. In the penultimate window let $D_-$ be its covolume, $g=(D_-/V_b)^{1/b}$, $v$ its signed winner, $s=\|v\|$, and $k$ its absolute fresh height. In its projected quotient $L$, write $D=D_-/s$, $h=(D/V_d)^{1/d}$, $x$ for the signed minimum of length $t$, and $R_t=ch t^{-1/d}$. Use the following three observables.

1. $A_0$ requires a horizontal $v$, horizontal $x$, $1<t\le\sqrt{1+c^2 h^2}$, and an **old** nonzero witness below $R_t$ after projecting off $x$. Existence of any such witness suffices, including in a tie with a fresh witness. $A$ adds that the shortest raw lift of the designated $x$ has length strictly greater than $6t/5$. All these lifts have zero penultimate input. The tables give both probabilities. [Inherited witnesses, §§1 and 3](wall1_inherited_witness.md)
2. $B$ requires $k>0$, $0.954<s/g<1.097193$, the same $t$ gate, and any nonzero witness in $P_{x^\perp}L$ strictly below $R_t$. Write $G$ for the same event before the final witness test. The unconditional contribution is $\Pr(B)$. The selected plane-hit rate given the vertical band and length gate is $\Pr(B)/\Pr(G)$ when $\Pr(G)>0$. Both refer to one mark. [Part 151](wall1_penultimate_tail.md) · [Part 153 and audit](wall1_neargh_vertical.md)
3. On the **following** draw, reuse $s,k$ for the new winner. Set $R=c(D/(sV_d))^{1/d}$ and $R_*=q^{m/N}\sqrt{d/(2\pi)}$. This substitutes the toy number of outputs and the final raw dimension in the audited radius split. Use $k>0$, $R<R_*$ and $\sqrt3/2<R/s<8$. Count primitive quotient sign pairs of length $p<R$, removing exactly the marked incidences of Part 150, Theorem 4. Their total is $Z$. Count in $C$ those pairs admitting a rounded lift of nonzero fresh height, assigning a horizontal/nonhorizontal rounding tie to $C$. Set both counts to zero outside the gates. The requested contribution is $\mathbb E C$. The expectation $\mathbb E Z$ is the full toy $F_{\rm rem}$. [Part 150 and audit](wall1_shortened_lines.md) · [Part 152 and audit](wall1_cylinder_average.md) · [Part 154 and audit](wall1_winner_exchange.md)

## Exact design counts

Each row below is a full enumeration. The $A_0,A$, vertical band, $G$ and $B$ columns have denominator $P=Q^{j+T}$. The columns $I_*,C,Z$ have denominator $F=QP$, where $I_*$ counts terminal draws passing the vertical-winner and radius gates. In particular, dividing the $B$ column by the $G$ column gives the conditional hit rate. $C$ and $Z$ are sums of multiplicities. A zero is exact.

| $(m,j,T)$ | $q$ | $P$ | $A_0$ | $A$ | Vertical band | $G$ | $B$ | $F$ | $I_*$ | $C$ | $Z$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| (1,2,1) | 2 | 8 | 0 | 0 | 0 | 0 | 0 | 16 | 0 | 0 | 0 |
| (1,2,1) | 3 | 27 | 0 | 0 | 0 | 0 | 0 | 81 | 0 | 0 | 0 |
| (1,2,1) | 5 | 125 | 0 | 0 | 16 | 16 | 0 | 625 | 64 | 0 | 0 |
| (1,2,1) | 7 | 343 | 0 | 0 | 0 | 0 | 0 | 2401 | 216 | 0 | 0 |
| (1,2,1) | 11 | 1331 | 0 | 0 | 0 | 0 | 0 | 14641 | 1736 | 0 | 0 |
| (1,2,1) | 17 | 4913 | 0 | 0 | 1150 | 430 | 2 | 83521 | 8976 | 0 | 0 |
| (1,2,1) | 23 | 12167 | 0 | 0 | 2362 | 1018 | 2 | 279841 | 43200 | 0 | 0 |
| (1,2,2) | 5 | 625 | 0 | 0 | 112 | 88 | 0 | 3125 | 256 | 0 | 0 |
| (1,2,2) | 11 | 14641 | 0 | 0 | 1544 | 392 | 0 | 161051 | 4224 | 0 | 0 |
| (1,2,3) | 7 | 16807 | 0 | 0 | 2160 | 752 | 0 | 117649 | 5024 | 0 | 0 |
| (1,3,1) | 7 | 2401 | 0 | 0 | 0 | 0 | 0 | 16807 | 2160 | 0 | 0 |
| (1,3,1) | 11 | 14641 | 0 | 0 | 0 | 0 | 0 | 161051 | 14000 | 0 | 0 |
| (1,3,2) | 3 | 243 | 0 | 0 | 0 | 0 | 0 | 729 | 0 | 0 | 0 |
| (1,3,2) | 7 | 16807 | 0 | 0 | 1296 | 688 | 0 | 117649 | 16416 | 0 | 0 |
| (1,3,2) | 23 | 6436343 | 1518 | 330 | 997938 | 372402 | 1458 | 148035889 | 20087778 | 0 | 261142 |
| (2,1,1) | 3 | 81 | 0 | 0 | 0 | 0 | 0 | 729 | 8 | 0 | 0 |
| (2,1,1) | 5 | 625 | 0 | 0 | 0 | 0 | 0 | 15625 | 1184 | 0 | 0 |
| (2,1,1) | 7 | 2401 | 0 | 0 | 448 | 88 | 0 | 117649 | 18600 | 0 | 0 |
| (2,1,1) | 11 | 14641 | 0 | 0 | 1128 | 280 | 0 | 1771561 | 271616 | 576 | 576 |
| (2,1,2) | 3 | 729 | 0 | 0 | 8 | 0 | 0 | 6561 | 352 | 0 | 0 |
| (2,1,2) | 5 | 15625 | 0 | 0 | 3160 | 664 | 0 | 390625 | 57952 | 0 | 0 |
| (2,1,3) | 3 | 6561 | 0 | 0 | 536 | 64 | 0 | 59049 | 3872 | 0 | 0 |
| (2,2,1) | 2 | 64 | 0 | 0 | 9 | 0 | 0 | 256 | 27 | 0 | 0 |
| (2,2,1) | 3 | 729 | 0 | 0 | 0 | 0 | 0 | 6561 | 704 | 0 | 0 |
| (2,2,1) | 5 | 15625 | 0 | 0 | 3420 | 1980 | 4 | 390625 | 73888 | 648 | 2172 |
| (2,2,2) | 3 | 6561 | 0 | 0 | 512 | 368 | 0 | 59049 | 6144 | 0 | 0 |
| (2,3,1) | 3 | 6561 | 0 | 0 | 0 | 0 | 0 | 59049 | 6144 | 0 | 0 |
| (2,3,2) | 3 | 59049 | 0 | 0 | 4096 | 1760 | 0 | 531441 | 58368 | 0 | 0 |
| (3,1,1) | 2 | 64 | 0 | 0 | 0 | 0 | 0 | 512 | 63 | 0 | 0 |
| (3,1,1) | 3 | 729 | 0 | 0 | 178 | 90 | 0 | 19683 | 5554 | 36 | 66 |
| (3,1,1) | 5 | 15625 | 0 | 0 | 2536 | 472 | 0 | 1953125 | 715768 | 10688 | 16656 |
| (3,1,2) | 2 | 512 | 0 | 0 | 49 | 3 | 0 | 4096 | 608 | 0 | 0 |
| (3,1,2) | 3 | 19683 | 0 | 0 | 4252 | 1772 | 0 | 531441 | 96368 | 72 | 312 |
| (3,1,3) | 2 | 4096 | 0 | 0 | 608 | 100 | 0 | 32768 | 3094 | 0 | 0 |
| (3,2,1) | 2 | 512 | 0 | 0 | 0 | 0 | 0 | 4096 | 490 | 0 | 0 |
| (3,2,1) | 3 | 19683 | 0 | 0 | 4670 | 4046 | 6 | 531441 | 91346 | 948 | 3224 |
| (3,2,2) | 2 | 4096 | 0 | 0 | 343 | 52 | 0 | 32768 | 5354 | 0 | 0 |
| (4,1,1) | 2 | 256 | 0 | 0 | 0 | 0 | 0 | 4096 | 378 | 0 | 0 |
| (4,1,1) | 3 | 6561 | 0 | 0 | 2056 | 520 | 0 | 531441 | 109624 | 1024 | 1400 |

The separate enumerations below stop after the penultimate draw. The columns give exact numerators over $P$. A dash indicates an observable omitted by the forced-horizontal recursion. These rows have no terminal measurement.

| $m$ | $j$ | $T$ | $q$ | $P$ | $A_0$ | $A$ | $G$ | $B$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 2 | 17 | 1419857 | 0 | 0 | 32714 | 0 |
| 1 | 3 | 2 | 19 | 2476099 | 1230 | 266 | — | — |
| 1 | 3 | 2 | 29 | 20511149 | 1950 | 426 | — | — |
| 1 | 3 | 2 | 31 | 28629151 | 2094 | 458 | — | — |
| 1 | 3 | 2 | 37 | 69343957 | 2526 | 554 | — | — |
| 1 | 3 | 3 | 11 | 1771561 | 0 | 0 | 32800 | 0 |
| 1 | 3 | 3 | 13 | 4826809 | 0 | 0 | — | — |
| 1 | 4 | 1 | 29 | 20511149 | 73918 | 0 | — | — |
| 1 | 4 | 1 | 31 | 28629151 | 85422 | 0 | — | — |
| 1 | 4 | 2 | 11 | 1771561 | 0 | 0 | 0 | 0 |
| 2 | 2 | 2 | 7 | 5764801 | 0 | 0 | 327852 | 204 |
| 2 | 2 | 2 | 11 | 214358881 | 0 | 0 | — | — |
| 2 | 2 | 3 | 5 | 9765625 | 0 | 0 | 399832 | 88 |
| 2 | 2 | 3 | 7 | 282475249 | 0 | 0 | — | — |
| 2 | 3 | 1 | 7 | 5764801 | 2944 | 0 | — | — |
| 2 | 3 | 2 | 5 | 9765625 | 2132 | 724 | 555716 | 2708 |
| 3 | 1 | 2 | 5 | 1953125 | 0 | 0 | 78392 | 0 |
| 3 | 1 | 3 | 5 | 244140625 | 0 | 0 | — | — |
| 3 | 2 | 2 | 3 | 531441 | 0 | 0 | 32142 | 42 |
| 3 | 2 | 2 | 5 | 244140625 | 0 | 0 | — | — |
| 3 | 3 | 1 | 3 | 531441 | 0 | 0 | 0 | 0 |
| 4 | 1 | 2 | 3 | 531441 | 0 | 0 | 14752 | 0 |

## What controls the counts?

**Inherited flags.** For $(m,j,T,q)=(2,3,2,5)$, only 96 of 390625 histories pass the forced old three-direction test before the penultimate column. Of these, 32 have all raw lifts longer than $6t/5$. Two horizontal comparisons on the *same* last column leave $724/(32\cdot25)=181/200$ of their mass. Thus the unconditional probability is $724/9765625$. The rarity already resides in the 32 incoming histories. Among the 724 hits, 636 follow a first horizontal selection and 88 a first height-one selection. All have $(s^2,t^2,\min\|z_{\rm raw}\|^2)=(3/2,4/3,2)$. The other 1408 inherited hits have $(2,3/2,2)$ and a lift inside the $6t/5$ cutoff. For an explicit shrunken instance, take the four columns before the penultimate draw all equal to $(1,0)$ and draw $(1,0)$ again. The squared raw-to-projected length ratio is $3/2$.

An entire modulus dependence is visible at $(m,j,T)=(1,3,2)$. For $q=19,23,29,31,37$ the exact shrunken numerators are $266,330,426,458,554$ over $q^5$. In each case there are 16 passing long-lift prefixes. At 19 and 23, listing them gives exactly $(a_1,a_2,a_3,a_4)\in\{-1,1\}^4$.

**A persistent subfamily.** For every prime $q\ge19$, those 16 signed-unit prefixes alone contribute $(16q-38)/q^5$. To check this finite calculation, enumerate the 16 sign tuples and raw vectors of squared norm at most two. The consecutive squared lengths for the first selection, forced horizontal selection, designated inherited minimum and old witness are $2,3/2,4/3,5/4$ in all 16 cases. Reverse rounding for the fourth minimum requires raw squared norm at most $5/4+(2+3/2+4/3)/4<3$. The first three minima have smaller bounds. Graph membership for these raw vectors is independent of $q\ge19$. The shortest raw lift of the designated minimum has squared length two. The length and plane gates already pass at 19 and loosen as $q$ increases. To beat or tie either forced horizontal selection, a fresh competitor also has a raw lift of squared norm at most two, by the same rounding argument. Its fresh height must be $\pm1$, so it can occur only at a last residue $0,1,-1$. For the five sign tuples with at most one negative coordinate only zero prevents the event. For the other eleven tuples all three residues do. This gives $5(q-1)+11(q-3)=16q-38$ using the specified signed tie rule. Exhaustion shows this subfamily accounts for the whole shrunken count on the five measured primes. It gives a lower bound for the full event at every larger prime.

**Selected planes.** At $(2,2,1,5)$, 3420 penultimate draws win vertically in the band, 1980 also pass the retained length test, and just 4 pass the plane test. The three rates of interest are $4/15625$ unconditionally, $4/3420$ conditional on the vertical band, and $4/1980$ conditional on both gates. At $(1,2,1,17)$ the only two hits have both restart columns $-1$ and final column $1$ or $-1$. At $(3,2,1,3)$ the corresponding counts are 4670, 4046, and 6. Every positive $B$ counted in the tables has winning height one. The 4 hits at $(2,2,1,5)$ and the 6 at $(3,2,1,3)$ all have $(s^2,t^2)=(2,3/2)$. At $(1,3,2,23)$ the most frequent $(s^2,t^2)$ class is $(3/2,4/3)$, with 810 of the 1458 hits.

**Terminal multiplicity.** At $(2,2,1,5)$, 624 designs contribute one nonhorizontal-lift witness and 12 contribute two, giving $648/390625$. At $(3,2,1,3)$ the split is 912 singletons and 18 doubles, giving $948/531441$. Every counted nonhorizontal lift in both rows occurs at a rounding tie. At $(3,1,1,5)$, all 10688 contributing designs have one witness, only 1696 of which are ties. Its largest single length class, with $(s^2,p^2)=(8/3,21/8)$ and a strictly nonhorizontal rounded lift, accounts for 2784 incidences. The next largest, $(8/3,5/2)$, accounts for 1728. The sum of both lift classes there is $16656/1953125=0.008527872$. At $(1,3,2,23)$ the nonhorizontal share falls to $0/261142$ despite 20087778 terminal draws passing the vertical-winner and radius gates.

**Dimension, depth and modulus.** At $q=3$, $j=T=1$, increasing $m$ from two to three to four changes $\mathbb EC$ from $0$ to $36/19683$ to $1024/531441$. At $(m,j,q)=(3,1,3)$, one extra adaptive selection reduces it from $36/19683$ to $72/531441$, a factor of $2/27$. Holding $(m,j,T)=(3,1,1)$ fixed and changing $q=2,3,5$ gives $0$, $36/19683$, $10688/1953125$. At rank four and $q=3$, allocating two output coordinates instead of three gives zero at $(2,2,1,3)$. These comparisons do not support a single decay rate in rank or modulus. The earlier experiments sampled terminal minima and window lengths. Their scalar frequency tables cannot be substituted for these joint counts. [Part 119 and audit](wall1_experiments.md) · [Part 123 and audit](wall1_experiments2.md)

**Budget comparison.** The penultimate sufficient allowance $0.0089999976$ is shared by $\Pr(A_0)$ and $\Pr(B)$. At $(1,3,2,23)$ their sum is $2976/6436343\simeq0.0004624$, about 5.14% of that allowance. The shrunken contribution is $330/6436343$. In a one-step supplementary row, $73918/29^5\simeq0.003604$ comes from inherited hits with a short raw lift. Width-specific charges for such lifts cannot be imported into a toy row. At $(3,1,1,5)$, $\mathbb EC$ and $\mathbb EZ$ use 56.0% and 87.3% of $0.0097738000$, respectively. The following bars show the fractions of the common terminal allowance at that design law.

```text
Nonhorizontal rounded lifts   ███████████░░░░░░░░░   56.0%
All residual witnesses        █████████████████░░░   87.3%
```

The terminal allowance also covers the long-line charge on horizontal **winners**, which is a different observable. Comparing these numbers gives a scale for the measured terms only. Parts 149–154 give no implication from a small penultimate contribution alone to the whole long-line charge. [Parts 144–154](../PROOF_GAP.md) · [Long-line necessary condition](wall1_long_lines.md)

## Two exact scaling checks

First, $T=1$ forces $\Pr(A)=0$ at *every* modulus and rank where the event is defined. On a horizontal win, round an old lift of $x$ along $v$. Shortestness implies $s^2\le t^2+s^2/4$, and the rounded raw lift has squared length at most $t^2+s^2/4\le4t^2/3<(6t/5)^2$. A second selection is therefore essential to exercise the shrunken-lift obligation. There is another degeneracy at $d=3$. After the two forced old projections the old witness lattice has rank one and generator length $z=D/t$. Its cutoff requires $z<c(z/V_3)^{1/3}$, hence $z<(c^3/V_3)^{1/2}<0.46$. Rounding off the old minimum gives $z\ge(\sqrt3/2)t>0.86$. Consequently $A_0$ is empty at this rank for every $T$.

Second, a vertical band hit imposes a physical upper bound on the winning length that depends only on $d$. Put $\alpha=\sqrt3/2$. Twice rounding a primitive lift gives $t\ge\alpha s$ and $\lambda_1(P_{x^\perp}L)\ge\alpha t$. On $B$ the latter minimum is below $c[D_-/(s t V_d)]^{1/d}$, while $D_-=V_b g^b<V_b(s/c)^b$. Combining the inequalities gives
$$
                 s<\frac{V_b}{c V_d\alpha^{2d+1}}.
$$
For fixed $(m,j,T)$, $D_-$ grows uniformly with $q$. Indeed Minkowski's bound gives $s_i\le 2(D_{i-1}/V_b)^{1/b}$, whence $D_i\ge (V_b^{1/b}/2)D_{i-1}^{d/b}$, starting at $q^m$. Thus the lower band edge $cg$ eventually exceeds the displayed constant, and $\Pr(B)$ is exactly zero for all sufficiently large primes at fixed rank and depth. A positive power law in $q$ across all primes would contradict this cutoff. This argument gives a fixed-rank statement. The constant itself grows rapidly with rank.

## Conjectures to test

1. **Inherited flags with shrunken lifts.** The signed-unit calculation gives a fixed-rank term asymptotic to $16q^{-4}$. Additional flag lengths can enter as $q$ grows. For a proportional-rank target let $I_A$ test the two designated horizontal selections, the retained length gate and the raw-lift shrink gate, before testing for an old plane witness. Along sequences with $m/d\to\rho\in(0,1)$, $T/d\to\tau>0$, and primes $q=d^{\gamma+o(1)}$ for fixed $\gamma>0$, conjecture
   $$
   \Pr(A)\le e^{o(d)}\,\mathbb E\!\left[I_A\min\!\left(1,
   \frac{V_{d-2}}{2V_d}\,c^{d-2}\frac{t^{2/d}}{h^2}\right)\right].
   $$
   The old witness lattice has rank $d-2$ and covolume $D/t$ on the indicated selections. The factor is its radius-$R_t$ half-ball volume divided by that covolume. A complementary way to bound the gated histories is by the rank of the congruences imposed by each raw flag. A consistent rank-$r$ system costs exactly $q^{-mr}$ for its $m$ independent output rows. The challenge is to count the admitted flags with their signed winner tests.
2. **Selected vertical plane hit.** A high-rank target is an upper bound, exponential in the GH cutoff with a subexponential selection factor. In the same proportional regime, write $I_G$ for the indicator of the measured band and retained-length gates. Conjecture
   $$
   \Pr(B)\le e^{o(d)}\,\mathbb E\!\left[I_G\min\!\left(1,
   \frac{V_{d-1}}{2V_d}\,c^{d-1}\frac{t^{1/d}}{h}\right)\right].
   $$
   The factor inside is half the volume of the radius-$R_t$ ball divided by the actual covolume $D/t$ after the second projection. The factor $1/2$ counts signs. Dropping the primitive-density correction is conservative for the volume benchmark. The conjecture concerns the joint selected expectation. It is stronger than simply measuring the chance of a band win. The finite-size test is the ratio of the counted hits to this gated volume sum, taken along a specified parameter sequence. No prefactor or asymptotic exponent is fitted by the present ladder.
3. **Terminal nonhorizontal-lift count.** In the same proportional regime let $I_*$ denote the *actual terminal* vertical-winner and radius gates defining $Z$. A distinct conjectural upper envelope is
   $$
   \mathbb E C\le e^{o(d)}\,\frac{c^d}{2}\,\Pr(I_*).
   $$
   Here the projected lattice has rank $d$ and covolume $D/s$, so its radius-$R$ ball has volume exactly $c^d D/s$. At $(3,1,1,5)$ the observed ratio to this gated benchmark is exactly $2\cdot10688/(715768c^4)$, about 0.036. It is zero at $(1,3,2,23)$ despite a nonempty gate. The challenge is the joint bias from selecting $v$, the rounding class, and the mark exclusion. In particular a continuous rounding model would assign zero mass to the tie stratum that accounts for entire positive toy rows. For a finite-dimensional proof one needs a quantified prefactor and a separate lattice tie count. All three envelopes average over the selected histories. The notation $e^{o(d)}$ permits a subexponential upper prefactor for each fixed sequence. It gives no numerical constant at a finite width.

Of the three, the **selected plane-hit rate** has the clearest first proof target. It is an indicator with a measured conditional denominator, the two successive rounding inequalities impose a deterministic exclusion, and hundreds or thousands of qualifying draws can leave only a handful of hits. The inherited count also has a concrete finite-prefix explanation at depth two, but its flag rank can grow with the suffix. The terminal term already consumes a substantial fraction of the numerical budget and changes its dominant rounding class when the prime changes. None of these exact toy computations establishes a width-506 estimate.

## Reproduction

The scratch directory for this run was `/tmp/w1-selected-UZyBFGep`. With a C++17 compiler and GMP headers/libraries on the compiler search path, the commands below reproduce the two-output rank-four row and the separate inherited count. The four arguments are $m,j,T,q$.

```sh
g++ -O3 -std=c++17 -ftrapv toy.cpp -lgmpxx -lgmp -o toy
./toy 2 2 1 5
g++ -O3 -std=c++17 -ftrapv forced.cpp -lgmpxx -lgmp -o forced
./forced 2 3 2 5
```

The scratch implementation uses depth-first enumeration of the $Q$ raw choices at each column, including the initial graph columns. It works in the fixed ordered integer ambient coordinates. The following details specify the enumeration, comparison conventions, and truncations.

* Store the current projector as $P=A/f$, initially $A=I$, $f=1$. Given a raw lift $w$ of a winner, set $u=Aw$ and $n=w^\top u$. The ordering key is $(n,u)$ after removing $n=0$. Update $(A,f)$ to $((nA-uu^\top)/f,n)$, extending unread coordinates by the identity projector. Deduplicate equal projected vectors. The old and new squared norms and covolumes satisfy $s^2=n/f$ and $D_{\rm new}^2=Q^2/n$. A different raw lift of the same winner leaves this projector unchanged.
* To enumerate a raw ball of integer squared radius $M$, recurse over all signed input tuples $y$ within its radius. For each output coordinate enumerate all integers in the remaining ball congruent to the corresponding entry of the raw graph matrix times $y$ modulo $q$. For $l$ previous winners maintain $U=\sum_{i\le l}\lceil s_i^2/4\rceil$. Reverse-order nearest-integer reduction along their raw lifts produces a lift of every projected vector $p$ with raw squared norm at most $\|p\|^2+U$. Start the shortest search at $M=4+U$. If the smallest nonzero projected squared norm $a$ found satisfies $a\le M-U$, the closed ball certifies both the minimum and its signed ties. Otherwise grow to $U+\lceil a\rceil$, or double $M$ if the ball had no nonzero projection. The same lifting bound with a prescribed threshold finds every witness. In the shrink test enumerate the original graph ball through $\lfloor36t^2/25\rfloor$ and compare the actual projected vector to $x$.
* For $A_0$ and $B$, compute $x$ in the actual quotient. With a horizontal $v,x$, restrict witness raw lifts to zero fresh coordinate for $A_0$. For $B$, use the full projected lattice. As a separate exact recursion for the inherited average, force $v,x$ and the shortest witness in the **old** lattice before the draw. If any length test fails, charge zero for the whole subtree. On passing histories test horizontal wins for $v$ and $x$ against the same fresh residue. The forced shrink test can be cached before appending that residue.
* On a qualifying terminal draw enumerate projected vectors through squared cutoff $R^2$ using raw squared radius $\lceil R^2\rceil+U$ with the terminal winner included in $U$. Normalize the nonzero integer numerator of each projected vector by its content and a fixed sign to identify its rational line. Retain the shortest nonzero vector per line, which is primitive in the quotient, even when its ambient numerator has content greater than one. Each generator orientation and each rounded window lift have a raw representative within the bound. Multiple raw representatives may project to the same lift. For a raw candidate $w$ giving that generator, keep it as a rounded lift when $2|w^\top A_{\rm old}v_{\rm raw}|\le v_{\rm raw}^\top A_{\rm old}v_{\rm raw}$. A nonzero fresh coordinate on any retained lift puts the line in $C$.
* To remove the marked incidences, use signed fresh heights $k,l$ for the terminal winner and any primitive rounded lift. Form the horizontal raw lift $z=(k w-l v_{\rm raw})/\gcd(k,l)$ of the primitive old line. In the raw old graph basis use coefficients $((x-Ay)/q,y)$, and reduce them modulo $q$ and the span of the frozen raw coefficient rows. In this space let $a$ be the residue of $(a_{\rm fresh},0)$ in **coefficient** coordinates; it corresponds to $q$ times the fresh torus displacement. Exclude exactly when $a\ne0$ and $[z]=i a$ for some $1\le i<q$. Indeed this equality is equivalent to $Pz/q-i\widetilde U\in L$, since the frozen rows span the saturated projection kernel. It detects the entire marked line even when the chosen representative is not parallel to the old vector.
* All geometric norms and projections are rational. For GH comparisons raise positive sides to their common integer power and bound $\pi$ between $314159265358979323846/10^{20}$ and $314159265358979323847/10^{20}$. Compute $V_0=1,V_1=2,V_r=2\pi V_{r-2}/r$ with rational endpoints. Both endpoint tests must give the same answer. Use the squared tests $3s^2/4<R^2<64s^2$ and compare $R^{2dN}$ with $(q^{2m/N}d/(2\pi))^{dN}$ for the strip. Thus even the decisions involving GH have certified rational comparisons. The raw outputs are integer counts.

Across the 39 full rows the enumerator visited 156,049,323 terminal designs. It checked the two denominators, the inclusions of all gates, and the multiplicity totals. The $q=23$ row at $(1,3,2)$ was partitioned by the first residue into 23 disjoint blocks of $23^5$ complete designs. Its penultimate counts agreed with a separate penultimate-only traversal. On $(2,3,2,5)$ the forced-old recursion and the direct enumeration independently returned the same 2132 inherited hits, including 724 shrunken hits. A second implementation in Sage used the Part 119 LLL/rational SVP routine, unimodular completion, and direct marked coordinates. For primitive quotient enumeration it bounded each coefficient by the corresponding diagonal of the inverse Gram matrix and tested coefficient gcd directly. It agreed on signed winners and observables on 48 penultimate and 28 terminal records covering positive, negative, tie, strict and multiple-witness cases. Those are targeted cross-checks. The exact fractions come from exhaustion. Scripts and raw counters were kept in scratch storage.

## Audit

**Verdict — MINOR CAVEATS.** The requested exact counts and the fixed-rank exclusion reproduce. Two distinctions matter for comparison with width 506. The toy gates can admit zero-mark witnesses that the width-506 determinant floor rules out, and $C$ counts the nonhorizontal-lift part of the full residual, before Part 154's further restrictions.

**Independent counts.** A separate scratch enumerator tested raw graph congruences and compared signed projected minima using integer Gram data. It certified the raw search balls by reverse rounding. It tested plane saturation by the gcd of the maximal minors in the raw graph basis and the marked exclusion by ranks over $\mathbb F_q$. Interval arithmetic separated the GH cutoffs from their integer comparison thresholds. For the large row, signed permutations grouped the first four input columns. Each distinct ordered prefix retained its own coordinate order and signs when resolving ties.

| Observable | Independent count |
| --- | --- |
| Inherited $(A_0,A)$, $(m,j,T)=(1,3,2)$ | $(1230,266)/19^5$, $(1518,330)/23^5$, $(1950,426)/29^5$. A second calculation on the 16 signed-unit prefixes recovered squared lengths $2,3/2,4/3,5/4$. Five prefixes lose only residue $0$ and eleven lose $0,\pm1$, giving $5(q-1)+11(q-3)=16q-38$. This accounts for the entire $A$ count at these three primes. The all-prime claim for $q\ge19$ is a subfamily lower bound. |
| Selected plane, $(2,2,1,5)$ | Of 15,625 penultimate designs, 3,420 passed the vertical band, 1,980 also passed the length gate and 4 passed the plane test. The joint probability is $4/15625$ and the hit rate given both gates is $4/1980$. |
| Terminal, $(3,1,1,5)$ | Of 1,953,125 designs, 715,768 passed the gates. There were 16,656 residual incidences. Exactly 10,688 admitted a nonhorizontal rounded lift, each on a distinct design, including 1,696 horizontal/nonhorizontal ties. Thus $\mathbb EC=10688/1953125$. |
| Terminal, $(1,3,2,23)$ | Of 148,035,889 designs, 20,087,778 passed the gates. All 261,142 residual incidences had only horizontal rounded lifts. Restricting independently to the zero mark gave 50,656 of these incidences. |

**Explicit exclusion threshold.** Write $\alpha=\sqrt3/2$, $L_b=V_b/2^b$, $r=(d/b)^{T-1}$ and $S_d=V_b/(cV_d\alpha^{2d+1})$. A lift rounded along a shortest vector of length $s$ has squared length at most $t^2+s^2/4$ and at least $s^2$. Applying the same argument at the next minimum gives $t\ge\alpha s$ and $\ell\ge\alpha t$. On a plane hit,
$$
 \alpha^d t^{d+1}<\frac{c^dD_-}{sV_d}
 <\frac{V_b}{cV_d}s^d,
$$
so $s<S_d$. Iterating the Minkowski determinant recurrence through the $T-1$ selections **before** the penultimate draw gives $D_-\ge L_b^{1-r}q^{mr}$. Consequently a sufficient threshold for $\Pr(B)=0$ is
$$
 q\ \ge\ \left(\frac{V_b(S_d/c)^b}{L_b^{1-r}}\right)^{1/(mr)}.
$$
Equality suffices since $s>cg$ on the band. For $(m,j,T)=(2,2,1)$ the right side is between $86.80$ and $86.81$, so every prime $q\ge89$ is excluded by this argument. The threshold need not be sharp.

**Restart and cutoff scope.** The graph is marginally uniform, all horizontal axes are already present, and each unread column has fresh height one. Its residue maps with equal fibers onto the current mark subgroup. Both penultimate tests use the same mark and the terminal draw uses an independent raw column with the previous projections retained. Substitution of $(m,j,T)=(400,105,406)$ gives $d=505$, $b=506$, $N=912$ and the radius split of Part 152. The strict band copies Part 151's residual gate. Its upper endpoint $1.097193$ was derived with a width-506 determinant floor. Other width-specific exits likewise require their own estimates. In particular, at width 506 a zero-mark vertical winner has $s=1$ and $R>30$, so it fails $R/s<8$. The measured 50,656 zero-mark incidences illustrate the difference despite the identical cutoff ratios. [Part 108](wall1_first_tour.md) · [Part 117](wall1_idea_round2.md) · [Part 150, Theorem 4 and audit](wall1_shortened_lines.md) · [Part 151 and audit](wall1_penultimate_tail.md)

**Conjectures and allowance.** The half-ball factors have witness ranks $d-2$ for the old lattice, $d-1$ for the full penultimate projection and $d$ for the terminal projection, with respective covolumes $D/t,D/t,D/s$. The gated bounds with $e^{o(d)}$ are explicitly conjectural. They supply neither a finite-width prefactor nor independence after selection. The reported $55.9890\%$ is the ratio of one toy multiplicity mean to the numerical value $0.0097738000$. The analogous ratio for $Z$, which already includes $C$, is $87.2524\%$. At width 506 the sufficient condition concerns $h_{\rm long}+F_{\rm rem}$. Part 154's narrower $F_{\rm bulk}^{\rm nonhor}$ also removes preselected old lines and applies theta and radius-strip restrictions. Neither toy percentage measures how much of the width-506 allowance is spent or left. [Part 152 and audit](wall1_cylinder_average.md) · [Part 154 and audit](wall1_winner_exchange.md) · [Part 157 and audit](wall1_bounded_bias.md)
