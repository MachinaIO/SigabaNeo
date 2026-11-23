# Uniform primitive prefixes at finite covolume

A short sublattice in an orthogonal quotient corresponds to a **flag** in the original lattice. Forgetting the lower member of the flag can undercount even the number of prefixes having a witness. In the finite example below, the quotient hit probability is exactly $180/240=3/4$, while division of the two unweighted sublattice counts gives $1/240$. There is a second normalization issue when the ambient lattice is random. The sampling experiment averages the ratio conditional on each lattice. Both issues arise before any approximation by an invariant distribution.

## The fixed-lattice count

Write $N_j(L,x)$ for the number of unoriented primitive rank-$j$ sublattices of a Euclidean lattice $L$ with covolume at most $x$. Covolumes are in the intrinsic spans. Put $n=\operatorname{rk}L$, $1\le k<n$, $d=n-k$, and $D=\det L$. A primitive sublattice is the intersection of its real span with its ambient lattice. Its exterior product is primitive and determines it up to sign. This proves finiteness. For $N=N_k(L,C)>0$, draw $P$ uniformly from the $N$ entries and write $Q_P$ for orthogonal projection off $P$. For $N=0$, record a failed draw. For any test $F$ on the whole projected lattice, conditional on this $L$ with $N>0$,
$$
 \Pr(F\mid L)=\frac1N\sum_{\det P\le C}{\bf1}_F(Q_PL),
 \qquad \det(Q_PL)=D/\det P .
$$
Here and below the prefix sums run over primitive rank-$k$ sublattices. If $F$ uses an embedded subgroup, include that subgroup in the summand. If it uses a block of width less than $d$, specify the intermediate span or the conditional law of the completion. A prefix determines the whole quotient. Different completions can have different first blocks. [Randomized reducer addendum](wall1_randomized_reducer_addendum.md)

For $1\le j\le d$, let $X_j(P,a)=N_j(Q_PL,a)$. Each primitive $J\subseteq Q_PL$ has the unique preimage $E=L\cap Q_P^{-1}(J)$, primitive of rank $k+j$. Conversely any primitive $E\supset P$ of that rank gives such a $J$. This follows by taking quotients of free abelian groups, since the kernel on $L$ is exactly $P$. A basis of $P$ followed by lifts of a basis of $J$ shows that $\det E=\det P\det J$. Define $N_k(E,t^-)$ by the strict inequality $\det P<t$. Double counting gives the finite identity
$$
 N\,\mathbb E[X_j(P,a)\mid L]
 =\sum_{\substack{E\text{ primitive in }L,\ \operatorname{rk}E=k+j\\\det E\le a C}}
 \left[N_k(E,C)-N_k\big(E,(\det E/a)^-\big)\right].                 \tag{1}
$$
Primitivity in $E$ implies primitivity in $L$ here since $E$ is primitive. Both endpoints matter, including equality at the lower endpoint. The hit probability is at most (1) divided by $N$, clipped at one. A quotient shape restriction can be inserted inside the inner count on $P$. An area cutoff by itself discards that information.

**Exact counterexample.** Take $L=\mathbb Z^2\oplus100\mathbb Z$, $k=j=1$, $C=16$, $a=1/8$. All 240 eligible prefix lines are horizontal. For $P=\mathbb Z(x,y,0)$ with $h=\sqrt{x^2+y^2}$, the quotient is rectangular with spacings $1/h$ and 100. The first spacing follows from Bézout's identity. The hit test is $h\ge8$, giving 180 hits. The horizontal plane is the only primitive plane of area at most $aC=2$. Every nonhorizontal plane has a nonzero exterior coordinate divisible by 100 in the standard orthonormal frame. Thus the proposed bare ratio is smaller than the hit probability by a factor of 180. Here (1) counts each hit exactly once.

## Finite denominators and random congruence lattices

For comparison, Kim's Theorem 1.3′ gives, with $b=\max(1/k,1/(n-k))$ and $\lambda=\lambda_1(L)$,
$$
 N_k(L,C)=a(n,k) C^n/D^k+
 O_n\!\left(1+(C/\lambda^k)^{n-b}\right).
$$
The coefficient $a(n,k)$ is explicit in Theorem 1.1. Theorem 1.3 refines the dependence on the successive minima. The displayed implied constant depends on dimension and supplies no numerical lower denominator at the cutoff under study. At the raw rank 911 and prefix rank 406 the saving in the power of $C$ is only $1/406$. Even for a fixed lattice the asymptotic needs a finite error before its main term can be used as a lower bound. [Kim, *Counting rational points on a Grassmannian*, Theorems 1.1 and 1.3](https://arxiv.org/pdf/1908.01245)

There are elementary finite bounds for the repository's congruence model. Let $L=\ker(\sigma:\mathbb Z^n\to\mathbb F_q^m)$ for prime $q$. A rational $k$-space gives the pair of sections $S\subseteq\mathbb Z^n$ and $P=S\cap L$ in the two lattices. This is a bijection of their primitive sublattices, with
$$
 \det P=\det S\,q^{\dim\sigma(S)},\qquad
 N_k(\mathbb Z^n,C/q^{\min(m,k)})\le N_k(L,C)\le N_k(\mathbb Z^n,C).
$$
For example every rank-$k$ coordinate section contributes to the lower bound at $C\ge q^{\min(m,k)}$. In this model the sandwich can be evaluated by bounded integer counts. Specifically $N_k(\mathbb Z^n,T)$ is half the count of nonzero decomposable integer exterior vectors of Euclidean length at most $T$ whose coordinates have gcd one. The lattice they represent is the integral section of their span. A primitive basis extends to an integer basis of the whole space, proving both directions. The sandwich can be very loose for smaller $C$. [Fixed rational sections in Part 226](wall1_high_codim_sections.md)

For fixed nested rational spaces $U\subset V$, put $S_W=W\cap\mathbb Z^n$, $h_W=\det S_W$, $r_W=\dim\sigma(S_W)$. Their contribution to the expected right side of (1) is the probability of the two simultaneous inequalities
$$
 h_U q^{r_U}\le C,\qquad h_V q^{r_V}\le a h_U q^{r_U}.
$$
Only $h_U\le C$ and $h_V\le aC$ need be included. This is a finite sum over deterministic flags before the random map is drawn. The ranks are correlated even for a single flag. Additional gates or shape tests must retain their own indicators.

Write $Y$ for the count in (1). For any $B>0$, the probability of an empty list **or** a quotient hit is bounded by
$$
 \Pr(N<B)+\mathbb E[Y\,{\bf1}_{N\ge B}]/B .
$$
This follows by splitting on $N<B$. The ratio of unconditional first moments instead weights lattices in proportion to their number of eligible prefixes. For instance, two equally probable inputs with (prefix count, hit-prefix count) equal to $(1,1)$ and $(99,0)$ have mean conditional hit probability $1/2$, whereas pooling prefixes gives $1/100$. A first moment for the denominator does not control its lower tail.

## Scale, marked voids and lifting

* **Area and spacing.** A square plane with side 27 has area 729 and internal perpendicular spacing 27. A hexagonal plane of shortest length 30 has spacing $15\sqrt3<26$ and area $450\sqrt3>729$. For a plane of shortest length $s$ and spacing $t=\det J/s$, reduction gives $t\ge\sqrt3\,s/2$, hence $t\le26$ implies $\det J\le 2(26)^2/\sqrt3\approx780.578$. This is the terminal area envelope in Parts 207–210. Substituting 729 in that bound omits admissible planes. Conversely, an area hit can have spacing above 26. The residuals also impose gates and a history of first hits, including the possibility of replacement of an earlier plane. A bound on the terminal area marginal under the correct law could majorize each residual requiring that hit. The existing decomposition of their probabilities uses the original trajectory. [Part 208](wall1_z1_terminal_law.md) · [Part 210](wall1_distortion_sharpening.md)
* **Marks.** Even all the unmarked sublattice counts and the order of the subgroup do not determine a height-one void. On the torus of $M=4\mathbb Z\oplus\mathbb Z$, take the order-two subgroup generated by $(2,0)$, or the one generated by $(0,1/2)$. At horizontal radius $3/4$, the respective miss fractions are $1/2$ and zero. This example concerns the height-one test only. Part 230 requires a conditional bound of 0.18 on the surviving histories at draws 129–405. A one-time average over all prefixes is a different probability. Selecting a prefix using future columns also changes the conditional distribution of an unread mark. [Part 108 and Parts 229–231](../PROOF_GAP.md) · [Part 230](wall1_inductive_typicality.md)
* **Unique shortest pair.** For a prefix in the horizontal lattice $L$, every height-one vector retains its unit height. Its projection therefore has norm at least one. If $\det P\ge T=D\,\gamma_d^{d/2}$, Hermite's inequality gives a nonzero horizontal competitor of norm at most one. This rules out a unique shortest height-one pair, including equality. For a full terminal quotient the success probability of that test is thus at most $N_k(L,\min(C,T))/N_k(L,C)$, with the sharper strict endpoint $\det P<T$. At fixed $L,k$, the numerator is bounded while the denominator grows as $C^n$. The success probability is $O_{L,k}(C^{-n})$ for this experiment as $C\to\infty$. The threshold uses only the unit height, so this necessary test can be quite weak at practical cutoffs. For prefixes in the full embedding, the unit-height argument requires a separate justification. [Part 47](wall1_decoupled.md) · [Physical scale of the quotient](wall1_randomized_reducer_addendum.md)
* **Lifting.** Even a shortest projected pair determines only two cosets of $P$. For instance $P=4\mathbb Z\oplus0$ in $4\mathbb Z\oplus\mathbb Z$ sends $(4,1)$ and $(0,1)$ to the same shortest image. Minimum-norm lifting returns the latter. Part 47 bounds a specified lifting procedure using individual prefix Gram–Schmidt lengths. A product bound on these lengths leaves their minimum uncontrolled. Quantitatively, the rectangular bases with lengths $u,1/u$ all have covolume one and have minimum length tending to zero as $u\downarrow0$. [Part 47](wall1_decoupled.md)

## Cost and numerical conclusion

At raw rank 911, Part 205's raw gate implies $\lambda_1(L)>250$. On every such input **the rank-406 list is empty for $C\le 2^{2090}$**. In fact, each $P$ inherits the same lower bound on its minimum. Blichfeldt's Hermite cap gives
$$
 \det P > (250^2/\gamma_{406})^{203}
 \ \ge\ (250^2\pi/2)^{203}/204! > 2^{2090}.
$$
The final inequality already holds with $\pi$ replaced by 3.141. This condition uses only the raw lattice and therefore survives a change of prefix selector on that input. It certifies an empty-list regime and says nothing about the distribution above its endpoint. [Raw gate in Part 205](wall1_doubly_gated.md) · [Blichfeldt bound](../PROOF_GAP.md)

Exact enumeration with one-pass reservoir sampling costs at least one visit per eligible prefix for this particular implementation. At draw 406 the width-506 appended raw lattice has rank 911 and index $3329^{400}$. Projecting 406 directions leaves rank 505. At any $C\ge3329^{400}$, the coordinate sections alone give at least $\binom{911}{406}>2^{897}$ eligible prefixes for **every** matrix. This is a lower bound on explicit listing at that cutoff, irrespective of the quotient test. It gives neither a complexity lower bound for all exact samplers nor a count at smaller cutoffs. For an enumeration of a subset of $m$ out of $N$ entries, uniform sampling on the subset has total variation distance exactly $1-m/N$ from uniform on the full list. Thus a short-vector list without a coverage or weight estimate supplies no numerical sampling error. [Raw rank and determinant](wall1_raw_graph_winner_cap.md)

At the stated widths and physical cutoffs, the identities above give no certified bound below one for either residual or the marked miss fraction of the redesigned process. The old-chain allowances $7.1275\cdot10^{-11}$ and $6.485\cdot10^{-11}$ refer to specific residuals after earlier charges. Those charges and their defining histories require verification under any new sampling law. The large-$C$ estimate rules out using an asymptotic equidistribution limit alone for terminal recovery. Whether an intermediate finite cutoff works remains open. There is no demonstrated sampling cost at such a cutoff, probability of successful lifting, or end-to-end recovery estimate here. [Parts 205–231](../PROOF_GAP.md) · [Earlier reducer and lifting discussion](wall1_randomized_reducer.md)

## Reproduce the finite checks

Run from the repository root. The script is embedded to keep the change in one file.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_random_prefix.md | python3 -B -)
```

```python
from fractions import Fraction
from math import comb, factorial, gcd

squared_lengths = [
    x*x + y*y
    for x in range(17) for y in range(-16, 17)
    if (x > 0 or y > 0) and gcd(x, y) == 1 and x*x + y*y <= 256
]
hits = sum(h >= 64 for h in squared_lengths)
assert (hits, len(squared_lengths)) == (180, 240)
assert Fraction(hits, len(squared_lengths)) == Fraction(3, 4)
assert 15**2 * 3 < 26**2 and 450**2 * 3 > 729**2
assert 27**2 == 729 and 27 > 26
assert 780577**2 * 3 < (1352*1000)**2 < 780578**2 * 3
assert (250**2 * 3141)**203 > 2**2090 * 2000**203 * factorial(204)
assert 2**897 < comb(911, 406) < 2**898
print("180 of 240 prefixes hit; one outer plane; coordinate count between 2^897 and 2^898.")
```

## Audit

**Verdict.** All three claims hold with the stated gates and sampling law. The embedded verifier passed. Two qualifications affect the interpretation of the results: the raw count uses a rank-406 prefix, and the terminal probability bounds a specific shortest-vector event.

1. **Flags and first moment.** For $a>0$ and $N>0$, each incidence $(P,E)$ in (1) corresponds to one primitive quotient witness, since $E/P$ projects isomorphically onto that witness. Its cutoff is exactly $\det E/a\le\det P\le C$. Thus $Y/N$ is the conditional mean number of witnesses and bounds the conditional hit probability. On random inputs the hit contribution from nonempty lists is the expectation of the conditional hit probability, with weight zero on empty lists. An independent disk count, grouping nonzero integer points by their coordinate gcd and dividing primitive counts by two for signs, gave 60 lines with squared length at most 63 and 240 with squared length at most 256. The single eligible outer plane therefore witnesses exactly 180 prefixes. The hit probability is $3/4$, while the unweighted ratio is $1/240$.
2. **Raw rank 911.** The raw gate gives $\lambda_1(P)>250$ for every rank-406 section. Using $\pi>3141/1000$ in the Blichfeldt bound already puts $\log_2\det P$ above $2090.279$, proving emptiness through $C=2^{2090}$ inclusive. At the other endpoint, each coordinate section has index $|\sigma(S)|\le3329^{400}$ in its coordinate lattice, which has covolume one. Distinct coordinate spans give distinct primitive sections, and $897<\log_2\binom{911}{406}<898$. This count applies to every matrix at $C\ge3329^{400}$. The original width-506 draw enters with 405 frozen directions. The count here concerns the explicitly proposed 406 directions, leaving 505 horizontal dimensions. [Draw-406 dimensions](wall1_raw_graph_winner_cap.md)
3. **Terminal event.** For a uniform horizontal prefix in a fixed $L$, Hermite gives $\lambda_1(Q_PL)^d\le T/\det P$ with $T=D\gamma_d^{d/2}$. At equality a horizontal vector of length at most one already precludes uniqueness. For $\det P>T$ a horizontal vector is strictly shorter than every height-one vector. Even allowing arbitrary tie-breaking, recovery that requires an exact shortest-vector call on the full terminal quotient to return a height-one vector has per-draw probability at most $N_k(L,T)/N_k(L,C)$ for $C\ge T$ and a nonempty list. The numerator is fixed, and Kim's Theorem 1.3′ gives denominator asymptotic to $a(n,k)C^n/D^k$. This proves the $O_{L,k}(C^{-n})$ upper bound. Lifting can further reduce success. Recovery at an intermediate finite cutoff or by a procedure that succeeds without a shortest height-one output remains unresolved. [Kim, Theorem 1.3′](https://arxiv.org/pdf/1908.01245)
