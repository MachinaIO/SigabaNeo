# The conditional void for a selected upper-band plane hit

**Result.** The finite incidence exchange is exact. Conditional on the incoming history and a compatible candidate–witness incidence, the probability that the candidate wins is either zero or one. After integrating out the history, the conditional probability is a ratio of two weighted prefix counts. The rank-506 Haar empty-ball bound controls neither member of that ratio. Thus the proposed exchange alone supplies no upper bound of $10^{-4}$ for the restart. An exact graph example below computes both orders of conditioning and distinguishes three events that an empty-ball argument can conflate.

## Draw 406 and the event being averaged

Use the marginal width-506 restart for plain LWE $(511,512,3329)$, CBD(3). Write $S$ for the history before draw 406, $M$ for its rank-$d$ retained lattice, $d=505$, $b=d+1$, $D=\det M$, $V_i$ for unit ball volume, and $g=(D/V_b)^{1/b}$. Restrict to $G=\{32.18553<g<203.888\}$. A uniform $U\in H=K/M$, with $K=P_E\mathbb Z^{910}$, gives the window $W_U=(M,0)+\mathbb Z(\widetilde U,1)$. The prime $q=3329$ annihilates $H$. The restart history includes the ambient frame for signed ties. Let $a=0.990$, $e=1.097193$, and $\gamma=477/500$. [Part 108](wall1_first_tour.md) · [Part 142 and audit](wall1_dual_cusp.md) · [Part 163 and audit](wall1_restart_haar_ratio.md)

For a primitive first candidate $v=(y,k)$ oriented to height $k>0$, set $s=\|v\|$, $h=(D/(sV_d))^{1/d}$. Force the first projection along $v$ in a window containing it. Choose the designated shortest line $x$ in $L=P_{v^\perp}W_U$, set $t=\|x\|$ for its generator, and write $Q=P_{x^\perp}L$. The band and gates require
$$
 ag<s\le eg,\qquad 1<t\le\sqrt{1+\gamma^2h^2},\qquad
 \lambda_1(Q)<R=\gamma h\,t^{-1/d}.
$$
A witness $w$ is an unoriented primitive line in $Q$ whose generator has length less than $R$. Its inverse image in $L$ is a saturated plane through $x$. Its inverse image in $W_U$ has rank three. Indeed, quotienting a lattice by a primitive generator has kernel of rank one and torsion-free quotient. Pulling a primitive line back through the two projections successively increases rank by one and preserves saturation. Counting distinct lines in $Q$ avoids counting infinitely many lifts of the same witness. [Part 120](wall1_plane_count.md) · [Part 162 and audit](wall1_upper_band_quotient.md)

Write $E(S,z)$ for the event that the **designated** first shortest line in $W_z$ has positive absolute height and passes the band and both gates. The unconditional mass at issue is
$$
 P=\mathbb E_S\!\left[\mathbf1_G\,
 \frac{\#\{z\in H(S):E(S,z)\}}{|H(S)|}\right].                         \tag{1}
$$
The equality follows from conditional uniformity. Counting histories for which *some* mark works would omit the fraction in (1). The budget from Part 161 also includes the separate inherited residual $p_a$. [Part 161 and audit](wall1_band_plane_hits.md)

## The finite conditional void

**Proposition 1.** Fix $S\in G$ and a band candidate $v=(y,k)$ with $y\in K$. Put $u_v=k^{-1}[y]\in H$. Order sign pairs by $(\|v\|^2,\min_{\rm lex}(v,-v))$. Let $D_S(v)$ indicate that a nonzero horizontal pair in $M$ has smaller key. Let $C_S(v)$ be the *set of distinct labels* $u_{v'}$ of all positive-height candidates $v'$ of smaller key, including candidates outside the band. For this competitor list include all nonzero pairs, regardless of primitivity or gates. Then, conditional on $S$ and $v\in W_U$, the probability that $v$ is designated first is exactly
$$
 J_S(v)=(1-D_S(v))\,\mathbf1_{u_v\notin C_S(v)}.                        \tag{2}
$$
Conditioning in addition on any compatible specified witness for the forced candidate gives the same value. For the open-ball void use the same formula with strictly smaller *length* throughout. Void tests always omit the origin.

*Proof.* At height $k$ the horizontal coordinates are precisely $M+k\widetilde U$. Thus $v\in W_U$ if and only if $[y]=kU$. Since $1\le k\le eg<224<q$, multiplication by $k$ permutes $H$. Presence fixes $U=u_v$ with incidence probability $1/|H|$. Every smaller-key positive-height competitor also has height below $q$, so it belongs to this window exactly when its label equals $u_v$. Every horizontal competitor belongs for all labels. These exhaust the nonzero sign pairs, and the bounded competitor lists are finite by discreteness. Given $S,u_v$, both quotient lattices, their signed selections, and every witness are determined. An incompatible witness has incidence probability zero, so no conditional law is asserted for it. This proves (2). In particular, a shorter candidate belonging only to a **different** mark never disqualifies $v$. ∎

For example, fix $S$ and any additional raw window vector $(y',j)$ with $y'\in K$. The joint probability that it and $v$ are present equals $|H|^{-1}\mathbf1_{[y']=ju_v}$, even for $j=0$. Thus two independent vectors can span a fixed rank-two sublattice while the first incidence has already specified the entire window. For the actual plane gate the rank-three pullback described above matters as well. Neither interpretation supplies a fresh random quotient after conditioning on $S,v$.

**Proposition 2 (history-averaged exchange).** For each good $S$, form the incidences $(v,w)$ from all positive-height primitive band candidates in their own windows that pass the length gate, taking one incidence per primitive witness. Let $n_S(v)$ be their number for this $v$. Give each incidence weight $\alpha(S)=\Pr(S)/|H(S)|$. Then
$$
 P=\sum_{S\in G}\alpha(S)\sum_{(v,w)}\frac{J_S(v)}{n_S(v)}
 \ \le\ \sum_{S\in G}\alpha(S)\sum_{(v,w)} J_S(v).                      \tag{3}
$$
Only positive $n_S(v)$ occur in these sums. Equivalently, keep one canonical witness per successful forced candidate and omit the divisor in the equality. The designated shortest sign pair of $Q$ provides such a witness whenever the strict gate holds.

*Proof.* Given $S$, exchange summation over the uniform mark with summation over its candidate–witness pairs. Proposition 1 supplies the incidence weight and winner indicator. For one candidate the reciprocal witness weights sum to one. The signed rule leaves precisely one first candidate on every contributing mark, proving the equality with (1). Dropping the divisor gives the upper bound. In particular the void factor belongs **inside** the sum over candidates. ∎

To evaluate the conditional probability with the history *unobserved*, group incidences by any recorded datum $f$ such as $(v,w)$ in the ambient frame. Denote by $I_S(f)$ the incidences in that group. Under the pair-counting measure on the right of (3), the probability of the signed void given $f$ is exactly
$$
 \frac{\displaystyle\sum_{S\in G}\alpha(S)
          \sum_{(v,w)\in I_S(f)}J_S(v)}
      {\displaystyle\sum_{S\in G}\alpha(S)\,|I_S(f)|}.                  \tag{4}
$$
Use groups with positive denominator. This is finite conditional probability, obtained by dividing the mass of surviving incidences by the mass of all incidences in the group. For the equality in (3), use canonical witnesses in both numerator and denominator, or give each incidence its reciprocal multiplicity weight in both. The remaining randomness in (4) is the prefix under these incidence weights. The marginal restart averages over a uniform $400\times510$ raw graph prefix with deterministic selections. Applying Part 108 at the last draw accounts for $1/|H(S)|$ and leaves that prefix sum intact. A Poisson insertion argument would require invariance of the remaining process after conditioning on points. That step has no counterpart in (2)–(4). [Part 108](wall1_first_tour.md) · [Part 162](wall1_upper_band_quotient.md) · [Last and Penrose, Theorems 4.4–4.5](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf)

## Exact tests of the two conditioning orders

Consider the full one-append graph $z=A u_1+B u_2+j u_3\pmod {17}$ in coordinates $(z,u_1,u_2,u_3)$ with $A,B,j$ independent and uniform. The prefix is $(A,B)$ and the mark is $j$. Use the same band and gates with $b=4,d=3,D=17$, omitting the width-506 restriction $G$.

**A prescribed pair, averaged over prefixes.** Fix sign representatives $v=(-1,0,0,-1)$ and $w_0=(0,1,-1,0)$. Containment of both is exactly $j=1$, $A=B=r$. Thus it leaves 17 equiprobable graphs. The lattice they span is the same in all 17. Here $w_0$ is a second raw vector used to test rank-two conditioning. We independently test the actual quotient-plane gate below.

| Conditional test on these 17 graphs | Passing $r$ | Probability |
|---|---|---:|
| No nonzero vector strictly shorter than $v$ | $r\ne0$ | $16/17$ |
| $v$ wins the signed first selection | $r\notin\{0,1\}$ | $15/17$ |
| Both gates after forcing $v$ | $r=1,-1$ | $2/17$ |
| $v$ wins and both gates pass | $r=-1$ | $1/17$ |

For the first row a shorter vector must be a coordinate unit. It exists exactly at $r=0$. For the second row any tie with first coordinate zero loses to the signed representative of $v$. A competing norm-two vector starting with $-1$ must use one other unit coordinate. Using an old input requires $r=\pm1$. At $r=1$ an old line with a $-1$ in the first input beats $v$, while at $r=-1$ the old lines with first coordinate $-1$ have a $+1$ in an old input and lose. At all other nonzero $r$, $v$ is the only tied representative starting with $-1$. This proves the first two rows. The finite certificate below proves the gate rows. In particular, further conditioning this pair on both gates gives open-ball void probability **one** and signed selection probability **one half**. The ordinary graph open-ball probability before either incidence is $(16/17)^3$, since precisely a zero graph column admits a unit. Even after integrating over histories, these are different laws.

**Full enumeration and certificate.** The following counts sum over all $17^3=4913$ graphs, orienting each line once. The three right columns apply distinct tests to the same 24 forced candidates.

| Band candidates | Pass length gate | Pass both forced gates | No strictly shorter pair | Designated by signed key | Unique shortest line |
|---:|---:|---:|---:|---:|---:|
| 1734 | 816 | 24 | 24 | 2 | 0 |

Here is a reproducible finite proof of the counts. Enumerate all signed representatives in $\{-1,0,1\}^4$ of squared norm $1,2,3$ satisfying the given graph congruence, retaining the lexicographically smaller tuple in each sign pair. For every vertical norm-two representative in that list perform the following operations.

1. Project the list along $v$ using $P_v(y)=y-\langle y,v\rangle v/\|v\|^2$. Discard zero and take the minimum $x$ of the distinct signed images under the prescribed key. An empty list cannot pass the length gate. Test $1<t^2\le 1+\gamma^2h^2$.
2. Project the first projected list along $x$, again removing zero. Test whether some image has squared norm strictly less than $\gamma^2h^2(t^2)^{-1/3}$. A hit contains a primitive witness since one can divide along the occupied line.
3. For each passing $v$, tally whether the original list has a shorter sign pair, a smaller key, or another sign pair of length at most $s$. For the prescribed-pair table also record the outcomes just for $A=B$, $j=1$ and the specified $v$, before discarding any forced-gate failures.

For completeness, $(ag)^2\in(1.81911,1.81912)$ and $(eg)^2\in(2.23437,2.23438)$, so only $s^2=2$ is in the band and each candidate is primitive. Write $r_*^2=1+\gamma^2h^2\in(2.83792,2.83793)$. A possible gated first projected point lifts to raw squared norm at most $r_*^2+1/2<4$ by rounding the coefficient along $v$. After $t>1$, a second projected witness lifts by rounding first along $x$, then along $v$, to raw squared norm less than $\gamma^2h^2+r_*^2/4+1/2<3.04741$. Thus the integer list through squared norm three includes all points needed for the tests, even on losing first candidates. The scratch enumeration used rational projections and exact lexicographic ties. Seventy-decimal-digit outward interval comparisons separated all nonrational cutoffs, with $V_3=4\pi/3$, $V_4=\pi^2/2$. The selected-event probability in this toy law is $2/4913$. Neither this probability nor $1/2$ is an estimate for width 506.

## What the rank-506 Haar estimate controls

Part 162 splits at $u=1.05$. On $a<s/g\le u$ it bounds the joint Haar probability by the mean count of primitive flags. On $s/g>u$ the event implies that the **unconditioned Haar window** has an empty open $ug$-ball of nonzero points. The primitive sign-pair count $N$ in that ball has mean $m=u^{506}/(2\zeta(506))$ and second factorial moment at most $m^2$. Hence $\Pr(N>0)\ge (\mathbb E N)^2/\mathbb E N^2\ge m/(1+m)$. The bound $1/(1+m)$ applies before marking any candidate. Using it as a multiplicative factor for each forced pair would require a separate conditional inequality, even on the Haar side. [Part 162 and audit](wall1_upper_band_quotient.md) · [Haar second moment](../../SigabaNeo/Lib/Lattices/Research/Wall1/HaarMinimumLower.lean)

For an interval check of both scales, set $h_0=32.18553(V_b/(eV_d))^{1/d}$, $X=(\gamma^2+h_0^{-2})^{1/2}$ and $Z=V_{d-1}\gamma^{d-1}204^{1/d}/(2V_d h_0)$. The low-strip flag bound of Part 163 is $(u^b-a^b)X^d Z/4$. Evaluating $V_0=1,V_1=2,V_i=2\pi V_{i-2}/i$ with 70-decimal-digit outward intervals gives $(5.64891360,5.64891361)\,10^{-12}$. For the high strip replace $\zeta(b)$ by $1+2^{-b}(1+2/(b-1))$, an upper bound by the integral test. The resulting empty-ball majorant lies in $(3.79528737,3.79528738)\,10^{-11}$. The sum of the unrounded majorants lies in $(4.36017873,4.36017875)\,10^{-11}$. These are enclosures of upper bounds on the Haar masses. [Part 163, Haar benchmark and audit](wall1_restart_haar_ratio.md)

**Remaining conjecture.** For the specified restart the sufficient budget is $P+p_a\le0.00019770868$. Equations (2)–(4) evaluate the conditional void and identify exactly which histories are weighted. The missing estimate is the total weight of prefixes supporting a gated incidence whose label has no smaller-key competitor. Part 153's fixed-radius result concerns the fresh void before conditioning on a witness. Part 163's singularity result prevents a uniform density comparison and leaves an event-specific bound possible. Neither supplies the weighted prefix estimate. Even a direct proof of $P\le0.0001$ would leave $0.00009770868$ for the separate residual under this allocation. [Part 153 and audit](wall1_neargh_vertical.md) · [Part 160 and audit](wall1_shrunken_lifts.md) · [Parts 161–163](../PROOF_GAP.md)

## Audit

**Verdict — MINOR CAVEATS.** Equations (1)–(4), the toy counts, and the Haar upper bound check out. One wording correction applies to the remaining gap. Read “total weight of prefixes supporting a gated incidence” as the **history average of the fraction of marks whose designated candidate passes both gates and the band** on $G$, as in (1). The toy example distinguishes these quantities exactly. Only the prefix $(A,B)=(-1,-1)$ supports a winner, giving prefix mass $1/289$. Its two winning marks $j=\pm1$ give selected mass $(1/289)(2/17)=2/4913$.

On $G$, every positive height under consideration is strictly below $q$. Thus $kU=[y]$ fixes the mark on the $q$-torsion group and fixes the entire window. Given a compatible witness, the signed void still has the value $J_S(v)$ in (2). This tests horizontal competitors for every mark and smaller-key positive-height competitors at the candidate's own mark. With the prefix unobserved, (4) follows by summing $\Pr(S)/|H(S)|$ once per incidence in each positive-mass group. The selected-event identity counts each successful candidate once through a canonical witness or reciprocal witness multiplicities. [Part 108](wall1_first_tour.md) · [Part 162 and audit](wall1_upper_band_quotient.md)

An independent scratch enumeration used raw squared norms through four, rational orthogonal projections, and signed ambient lexicographic ties. Across all 4,913 graphs it found 1,734 band candidates, 816 length-gate passes, and 24 candidates passing both gates. All 24 had an empty open ball below their length, two won the signed selection, and zero were uniquely shortest. Among the 17 graphs containing the prescribed raw pair, the four table numerators were respectively 16, 15, 2, and 1.

An independent 85-decimal-digit outward interval calculation with factorial ball volumes enclosed the sum of the low-strip flag bound and high-strip empty-ball bound in $(4.36017873984,4.36017873986)\,10^{-11}$. The high-strip term uses the unconditioned rank-506 Haar window at fixed determinant. Applying it to the incidence-weighted ratio (4) requires a separate comparison. The width-506 history average in (1) and residual $p_a$ both remain open under the sufficient shared allowance $0.00019770868$. [Part 161 and audit](wall1_band_plane_hits.md) · [Part 163 and audit](wall1_restart_haar_ratio.md)
